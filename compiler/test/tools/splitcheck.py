#!/usr/bin/env python3
"""Differential check of split compilations (-j=N) against unsplit ones (-j=1).

Compiles a program with -j=1 and with -j=N for each N given, and compares the
outputs symbol by symbol: every defined symbol must exist in both, in the same
section and with the same binding, and with the same contents. The -j=N output of
each N must also be byte for byte the same in repeated compilations.

Contents are compared after normalizing only what depends on where the linker of
the parts (`ld -r`, or the library writer) placed them:

 * a relocated field (a branch or ADRP target, a page offset, a pointer) is
   compared by the relocation type, the name of the symbol it refers to and the
   addend, not by the bits the field holds;
 * a branch or ADR(P) without a relocation is compared by its offset within the
   function when it stays in the function, and by the symbol and offset it reaches
   otherwise;
 * a reference to a local symbol (a string literal `_TMP123`, a frame description)
   is compared by the contents of that symbol, as their names are numbered in the
   order a compiler process creates them;
 * the doppelganger modules written for -lib (a template instance or a function in
   an object file of its own, with a ModuleInfo if it has static constructors) are
   named `module.N` after a counter, which the workers of a split compilation
   number apart: `N` is replaced by `#`, in symbol names and in the module names
   their ModuleInfo holds;
 * in a library, a weak definition may be in several members, as the members that
   need a comdat (a TypeInfo, a template instance's data) carry their own copy;
   the copies of one symbol must be the same, and are compared once;
 * local symbols are compared as a set of contents: the parts of a split
   compilation can each have a copy of a string literal that the unsplit
   compilation has once.

With --stress K, each -j=N is also compiled K more times in the determinism stress
mode of the compiler (DMD_SPLIT_STRESS set to K different seeds, from --stress-seed
on), in which every process of the split sleeps for pseudo-random short times at the
points where they synchronize, so that they run at other relative speeds: each of
those outputs must be byte for byte the -j=N output compiled without it.

Usage:
  splitcheck.py [-j 2,3,8] [-r 3] [--stress K [--stress-seed S]] [--dmd DMD] [--cwd DIR]
                [--keep] [--require-split] [--verbose] -- dmd-command...

The dmd command compiles to an object file (-c, with -of), to object files (-c
without -of: one per module) or to a library (-lib); a command that would link
is compiled with -c. Its -j, -of and -od options are replaced. The split log
(DMD_SPLIT_LOG) tells whether each -j=N compilation was split: with
--require-split, one that was not, or whose split was given up, is an error.
Exit status: 0 if the outputs match, 1 if any differ or a compilation fails.
"""

import argparse
import collections
import hashlib
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile

# ---------------------------------------------------------------------------
# Mach-O reading

MH_MAGIC_64 = 0xFEEDFACF
LC_SEGMENT_64 = 0x19
LC_SYMTAB = 0x2
N_STAB = 0xE0
N_TYPE = 0x0E
N_EXT = 0x01
N_PEXT = 0x10
N_SECT = 0x0E
N_WEAK_DEF = 0x0080
S_ATTR_PURE_INSTRUCTIONS = 0x80000000
S_ATTR_SOME_INSTRUCTIONS = 0x00000400
SECTION_TYPE = 0xFF
S_ZEROFILL = 0x1
S_GB_ZEROFILL = 0xC
S_THREAD_LOCAL_ZEROFILL = 0x12

R_UNSIGNED, R_SUBTRACTOR, R_BRANCH26, R_PAGE21, R_PAGEOFF12, R_GOT_PAGE21, \
    R_GOT_PAGEOFF12, R_POINTER_TO_GOT, R_TLVP_PAGE21, R_TLVP_PAGEOFF12, R_ADDEND = range(11)


class Section:
    __slots__ = ("index", "segname", "sectname", "addr", "size", "flags", "data", "relocs", "code", "_rmap")

    @property
    def name(self):
        return self.segname + "," + self.sectname


class Symbol:
    __slots__ = ("name", "type", "sect", "desc", "value")


class Reloc:
    __slots__ = ("address", "symbolnum", "pcrel", "length", "extern", "type")


class MachO:
    """The sections, symbols and relocations of a 64-bit Mach-O object file"""

    def __init__(self, data, label):
        self.label = label
        magic, cputype, _, filetype, ncmds, _, _, _ = struct.unpack_from("<IiiIIIII", data, 0)
        if magic != MH_MAGIC_64:
            raise ValueError("%s: not a 64-bit Mach-O object file" % label)
        self.sections = []
        self.symbols = []
        off = 32
        symtab = None
        for _ in range(ncmds):
            cmd, size = struct.unpack_from("<II", data, off)
            if cmd == LC_SEGMENT_64:
                nsects = struct.unpack_from("<I", data, off + 64)[0]
                so = off + 72
                for _ in range(nsects):
                    s = Section()
                    s.sectname = data[so:so + 16].rstrip(b"\0").decode()
                    s.segname = data[so + 16:so + 32].rstrip(b"\0").decode()
                    s.addr, s.size = struct.unpack_from("<QQ", data, so + 32)
                    offset, _, reloff, nreloc, s.flags = struct.unpack_from("<IIIII", data, so + 48)
                    s.index = len(self.sections) + 1
                    t = s.flags & SECTION_TYPE
                    if t in (S_ZEROFILL, S_GB_ZEROFILL, S_THREAD_LOCAL_ZEROFILL):
                        s.data = bytes(s.size)
                    else:
                        s.data = data[offset:offset + s.size]
                    s.code = bool(s.flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS))
                    s.relocs = []
                    for i in range(nreloc):
                        a, info = struct.unpack_from("<iI", data, reloff + 8 * i)
                        r = Reloc()
                        r.address = a
                        r.symbolnum = info & 0xFFFFFF
                        r.pcrel = (info >> 24) & 1
                        r.length = (info >> 25) & 3
                        r.extern = (info >> 27) & 1
                        r.type = (info >> 28) & 0xF
                        s.relocs.append(r)
                    self.sections.append(s)
                    so += 80
            elif cmd == LC_SYMTAB:
                symtab = struct.unpack_from("<IIII", data, off + 8)
            off += size
        if symtab:
            symoff, nsyms, stroff, strsize = symtab
            strtab = data[stroff:stroff + strsize]
            for i in range(nsyms):
                strx, ntype, nsect, ndesc, nvalue = struct.unpack_from("<IBBHQ", data, symoff + 16 * i)
                s = Symbol()
                end = strtab.find(b"\0", strx)
                s.name = strtab[strx:end].decode("latin-1")
                s.type, s.sect, s.desc, s.value = ntype, nsect, ndesc, nvalue
                self.symbols.append(s)


def read_archive(data, label):
    """Returns: the (name, contents) of the members of a BSD archive"""
    if not data.startswith(b"!<arch>\n"):
        raise ValueError("%s: not an archive" % label)
    off = 8
    members = []
    while off + 60 <= len(data):
        hdr = data[off:off + 60]
        name = hdr[0:16].decode().rstrip()
        size = int(hdr[48:58].decode().strip())
        body = data[off + 60:off + 60 + size]
        if name.startswith("#1/"):
            n = int(name[3:])
            name = body[:n].rstrip(b"\0").decode()
            body = body[n:]
        if not name.startswith("__.SYMDEF"):
            members.append((name, body))
        off += 60 + size
        off += off & 1
    return members


# ---------------------------------------------------------------------------
# Normalizing

DOPPEL = re.compile(r"^([A-Za-z_][A-Za-z_0-9]*)\.(\d+)$")


def normalize_name(name):
    """Replace the counter of doppelganger module names in a D mangled name"""
    if not name.startswith("__D") and not name.startswith("_D"):
        return name
    i = name.index("D") + 1
    out = [name[:i]]
    changed = False
    while i < len(name) and name[i].isdigit():
        j = i
        while j < len(name) and name[j].isdigit():
            j += 1
        n = int(name[i:j])
        ident = name[j:j + n]
        if len(ident) < n:
            break
        m = DOPPEL.match(ident)
        if m:
            ident = m.group(1) + ".#"
            changed = True
        out.append("%d%s" % (len(ident), ident))
        i = j + n
    if not changed:
        return name
    out.append(name[i:])
    return "".join(out)


MODULE_NAME_IN_DATA = re.compile(rb"([A-Za-z_][A-Za-z_0-9.]*)\.\d+\0")


def sign_extend(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


class Unit:
    """The normalized symbols of one object file"""

    def __init__(self, obj):
        self.obj = obj
        self.defined = {}       # normalized external name -> record
        self.locals = collections.Counter()   # record of local symbol contents
        self.anonymous = collections.Counter()
        self.byaddr = {}        # section index -> sorted [(addr, end, sym)]
        sects = obj.sections
        bysect = collections.defaultdict(list)
        for s in obj.symbols:
            if s.type & N_STAB or (s.type & N_TYPE) != N_SECT:
                continue
            bysect[s.sect].append(s)
        self.ranges = {}
        self.endof = {}
        self.owners = []        # the symbols whose records are being made
        for si, syms in bysect.items():
            sec = sects[si - 1]
            addrs = sorted(set(s.value for s in syms))
            ends = {}
            for k, a in enumerate(addrs):
                ends[a] = addrs[k + 1] if k + 1 < len(addrs) else sec.addr + sec.size
            lst = sorted(((s.value, ends[s.value], s) for s in syms), key=lambda t: (t[0], t[2].name))
            self.ranges[si] = lst
            for start, end, s in lst:
                self.endof[id(s)] = end
        self.local_keys = {}

    def symbol_at(self, sectindex, addr):
        """Returns: the symbol whose range holds addr, and the offset in it"""
        lst = self.ranges.get(sectindex)
        if not lst:
            return None, addr
        lo, hi = 0, len(lst)
        while lo < hi:
            mid = (lo + hi) // 2
            if lst[mid][0] <= addr:
                lo = mid + 1
            else:
                hi = mid
        k = lo - 1
        if k < 0:
            return None, addr
        # prefer an external symbol among aliases
        a = lst[k][0]
        best = lst[k]
        j = k
        while j >= 0 and lst[j][0] == a:
            if lst[j][2].type & N_EXT:
                best = lst[j]
                break
            j -= 1
        if addr >= best[1] and best[1] > best[0]:
            return None, addr
        return best[2], addr - best[0]

    def section_of_addr(self, addr):
        for s in self.obj.sections:
            if s.size and s.addr <= addr < s.addr + s.size:
                return s.index
        return None

    def target_name(self, sym, depth):
        """The name a reference to sym compares by"""
        if self.owners and sym is self.owners[-1]:
            return "self"
        if sym.type & N_EXT:
            return normalize_name(sym.name)
        return "local:" + self.local_key(sym, depth + 1)

    def local_key(self, sym, depth):
        key = self.local_keys.get(id(sym))
        if key is not None:
            return key
        if depth > 3:
            return "~" + sym.name
        self.local_keys[id(sym)] = "~cycle"
        rec = self.record(sym, depth)
        key = hashlib.sha1(repr(rec).encode()).hexdigest()[:16]
        self.local_keys[id(sym)] = key
        return key

    def address_ref(self, addr, depth, si=None):
        if si is None:
            si = self.section_of_addr(addr)
        if si is None:
            return ("abs", addr)
        sym, off = self.symbol_at(si, addr)
        if sym is None:
            return ("sect", self.obj.sections[si - 1].name, "anon")
        return (self.target_name(sym, depth), off)

    def ref(self, r, addend, depth):
        """The (symbol, offset) a data relocation refers to"""
        if r.extern:
            sym = self.obj.symbols[r.symbolnum]
            if (sym.type & N_TYPE) == N_SECT:
                return (self.target_name(sym, depth), addend)
            return (normalize_name(sym.name), addend)
        # relative to a section, whose number the relocation gives
        return self.address_ref(addend, depth, r.symbolnum)

    def reloc_target(self, r, addend, depth):
        if r.extern:
            sym = self.obj.symbols[r.symbolnum]
            if (sym.type & N_TYPE) == N_SECT:
                return (self.target_name(sym, depth), addend)
            return (normalize_name(sym.name), addend)
        # section-relative: the field holds the address
        return ("addr",) + self.address_ref(addend, depth, r.symbolnum)

    def code_tokens(self, sec, start, end, relocmap, depth):
        data = sec.data
        toks = []
        base = sec.addr
        for o in range(start - base, end - base, 4):
            if o + 4 > len(data):
                toks.append(("tail", data[o:].hex()))
                break
            w = struct.unpack_from("<I", data, o)[0]
            rs = relocmap.get(o)
            if rs:
                addend = 0
                tok = []
                for r in rs:
                    if r.type == R_ADDEND:
                        addend = sign_extend(r.symbolnum, 24)
                        continue
                    if r.type == R_BRANCH26:
                        mask = 0xFC000000
                    elif r.type in (R_PAGE21, R_GOT_PAGE21, R_TLVP_PAGE21):
                        mask = 0x9F00001F
                    elif r.type in (R_PAGEOFF12, R_GOT_PAGEOFF12, R_TLVP_PAGEOFF12):
                        mask = 0xFFC003FF
                    else:
                        mask = 0
                    if not r.extern and r.type in (R_PAGE21, R_PAGEOFF12, R_BRANCH26):
                        tok.append(("local-reloc", r.type, w))
                        continue
                    tok.append((w & mask, r.type) + self.reloc_target(r, addend, depth))
                toks.append(tuple(tok))
                continue
            pc = base + o
            tgt = None
            if (w & 0x7C000000) == 0x14000000:          # b, bl
                tgt = pc + (sign_extend(w & 0x3FFFFFF, 26) << 2)
                m = w & 0xFC000000
            elif (w & 0xFF000010) == 0x54000000:        # b.cond
                tgt = pc + (sign_extend((w >> 5) & 0x7FFFF, 19) << 2)
                m = w & 0xFF00001F
            elif (w & 0x7E000000) == 0x34000000:        # cbz, cbnz
                tgt = pc + (sign_extend((w >> 5) & 0x7FFFF, 19) << 2)
                m = w & 0xFF00001F
            elif (w & 0x7E000000) == 0x36000000:        # tbz, tbnz
                tgt = pc + (sign_extend((w >> 5) & 0x3FFF, 14) << 2)
                m = w & 0xFFF8001F
            elif (w & 0x3B000000) == 0x18000000:        # ldr literal
                tgt = pc + (sign_extend((w >> 5) & 0x7FFFF, 19) << 2)
                m = w & 0xFF00001F
            elif (w & 0x9F000000) == 0x10000000:        # adr
                tgt = pc + sign_extend(((w >> 5) & 0x7FFFF) << 2 | (w >> 29) & 3, 21)
                m = w & 0x9F00001F
            elif (w & 0x9F000000) == 0x90000000:        # adrp without a relocation
                toks.append(("adrp-unrelocated", w & 0x9F00001F))
                continue
            if tgt is None:
                toks.append(w)
            elif start <= tgt < end:
                toks.append((m, "rel", tgt - start))
            else:
                toks.append((m, "to") + self.address_ref(tgt, depth))
        return toks

    def data_tokens(self, sec, start, end, relocmap, depth):
        data = sec.data
        base = sec.addr
        o = start - base
        e = end - base
        toks = []
        chunk = bytearray()
        offs = sorted(k for k in relocmap if o <= k < e)
        k = 0
        skip = None
        if sec.sectname == "__eh_frame" and e - o >= 8 and data[o + 4:o + 8] != bytes(4):
            # the CIE pointer of a frame description entry is the distance back to the
            # CIE, written with or without a relocation
            skip = o + 4
        while o < e:
            if o == skip:
                if chunk:
                    toks.append(bytes(chunk))
                    chunk = bytearray()
                toks.append(("cie",))
                o += 4
                while k < len(offs) and offs[k] < o:
                    k += 1
                continue
            if k < len(offs) and offs[k] == o:
                rs = relocmap[o]
                size = 1 << rs[-1].length
                field = int.from_bytes(data[o:o + size], "little", signed=True)
                if chunk:
                    toks.append(bytes(chunk))
                    chunk = bytearray()
                tok = []
                if len(rs) == 2 and rs[0].type == R_SUBTRACTOR:
                    # the difference of two addresses, as in a frame description
                    tok = [("diff", self.ref(rs[0], 0, depth), self.ref(rs[1], 0, depth), field)]
                else:
                    for r in rs:
                        if r.type == R_UNSIGNED:
                            # an address: the field holds the addend, or the address itself
                            # when the relocation is to a section
                            tok.append(("ptr",) + (self.ref(r, field, depth) if not r.extern else
                                                   (self.ref(r, 0, depth)[0], field)))
                        else:
                            tok.append((r.type, self.ref(r, 0, depth), field))
                toks.append(tuple(tok))
                o += size
                k += 1
                continue
            chunk.append(data[o])
            o += 1
        if chunk:
            toks.append(bytes(chunk))
        return toks

    def relocmap(self, sec):
        m = sec._rmap if hasattr(sec, "_rmap") else None
        if m is None:
            m = collections.defaultdict(list)
            for r in sec.relocs:
                m[r.address].append(r)
            # the ADDEND of a pair comes first
            for v in m.values():
                v.sort(key=lambda r: 0 if r.type in (R_ADDEND, R_SUBTRACTOR) else 1)
            sec._rmap = m
        return m

    def record(self, sym, depth=0):
        self.owners.append(sym)
        try:
            return self.make_record(sym, depth)
        finally:
            self.owners.pop()

    def make_record(self, sym, depth):
        sec = self.obj.sections[sym.sect - 1]
        end = self.endof[id(sym)]
        start = sym.value
        if sec.sectname == "__eh_frame":
            # a frame description entry ends where its length says, before whatever
            # entry without a symbol follows it
            o = start - sec.addr
            length = struct.unpack_from("<I", sec.data, o)[0] if o + 4 <= len(sec.data) else 0
            if 0 < length < 0xFFFFFFFF:
                end = min(end, start + 4 + length)
        rmap = self.relocmap(sec)
        if sec.code:
            toks = self.code_tokens(sec, start, end, rmap, depth)
            # the zeros aligning the next function
            while toks and toks[-1] == 0:
                toks.pop()
            return (sec.name, None, tuple(toks))
        else:
            toks = self.data_tokens(sec, start, end, rmap, depth)
            if "ModuleInfo" in sym.name:
                toks = [MODULE_NAME_IN_DATA.sub(rb"\1.#\0", t) if isinstance(t, bytes) else t for t in toks]
            # Mach-O records no symbol sizes: a data symbol extends to the next one, past
            # the zeros that align it, which depend on what follows it
            while toks and isinstance(toks[-1], bytes) and not toks[-1].strip(b"\0"):
                toks.pop()
            if toks and isinstance(toks[-1], bytes):
                toks[-1] = toks[-1].rstrip(b"\0")
            return (sec.name, None, tuple(toks))
        return (sec.name, end - start, tuple(toks))


def binding(sym):
    b = "global"
    if sym.desc & N_WEAK_DEF:
        b = "weak"
    if sym.type & N_PEXT:
        b += "-hidden"
    return b


def collect(objects):
    """Returns: the normalized defined symbols of the object files `objects`:
    external ones by name (a list of distinct definitions each), local ones as a set"""
    defined = collections.defaultdict(list)
    locals_ = set()
    for label, data in objects:
        obj = MachO(data, label)
        u = Unit(obj)
        for si, lst in u.ranges.items():
            for start, end, sym in lst:
                if sym.type & N_EXT:
                    rec = (binding(sym),) + u.record(sym)
                    name = normalize_name(sym.name)
                    if rec not in defined[name]:
                        defined[name].append(rec)
                else:
                    if sym.name.startswith("ltmp") or sym.name.startswith("l_"):
                        continue
                    sec = obj.sections[sym.sect - 1]
                    o = sym.value - sec.addr
                    if sec.sectname == "__eh_frame" and sec.data[o + 4:o + 8] == bytes(4):
                        # a CIE: each part has its own, which ld -r may merge or not; the
                        # FDEs refer to theirs by position, compared as ("cie",)
                        continue
                    locals_.add(u.record(sym))
    return defined, locals_


# ---------------------------------------------------------------------------
# Comparing

def describe(rec):
    b, sect, size, toks = rec
    return "%s %s" % (b, sect) + (" size %d" % size if size is not None else "")


def first_difference(a, b):
    ta, tb = a[3], b[3]
    for i, (x, y) in enumerate(zip(ta, tb)):
        if x != y:
            return i, x, y
    return min(len(ta), len(tb)), ta[len(tb):][:1], tb[len(ta):][:1]


def compare(base, other, label, report, limit):
    """Compare the symbols of the -j=1 output `base` with those of `other`"""
    bdef, bloc = base
    odef, oloc = other
    problems = 0
    names = sorted(set(bdef) | set(odef))
    for name in names:
        a = bdef.get(name)
        b = odef.get(name)
        if a is None:
            problems += 1
            if problems <= limit:
                report("%s: %s is defined only with -j=N (%s)" % (label, name, describe(b[0])))
            continue
        if b is None:
            problems += 1
            if problems <= limit:
                report("%s: %s is defined only with -j=1 (%s)" % (label, name, describe(a[0])))
            continue
        if len(b) > 1 and len(a) == 1:
            problems += 1
            if problems <= limit:
                report("%s: %s has %d different definitions with -j=N" % (label, name, len(b)))
            continue
        if sorted(map(repr, a)) != sorted(map(repr, b)):
            problems += 1
            if problems <= limit:
                x, y = a[0], b[0]
                if x[:3] != y[:3]:
                    report("%s: %s is %s with -j=1 but %s with -j=N" % (label, name, describe(x), describe(y)))
                else:
                    i, tx, ty = first_difference(x, y)
                    report("%s: %s differs at token %d: -j=1 %r, -j=N %r" % (label, name, i, tx, ty))
    only1 = bloc - oloc
    onlyN = oloc - bloc
    if only1 or onlyN:
        problems += 1
        if problems <= limit:
            report("%s: local symbols differ: %d only with -j=1, %d only with -j=N" % (label, len(only1), len(onlyN)))
            for r in list(only1)[:3]:
                report("    only -j=1: %s %r" % (r[0], r[2][:4]))
            for r in list(onlyN)[:3]:
                report("    only -j=N: %s %r" % (r[0], r[2][:4]))
    return problems


# ---------------------------------------------------------------------------
# Compiling

def strip_options(cmd):
    out = []
    skip = False
    for a in cmd:
        if skip:
            skip = False
            continue
        if re.match(r"^-j(=|$)", a) or a.startswith("-of") or a.startswith("-od") or a == "-op":
            continue
        out.append(a)
    return out


def output_kind(cmd):
    if "-lib" in cmd:
        return "lib"
    if "-c" in cmd and not any(a.startswith("-of") for a in cmd):
        return "objs"
    return "obj"


def compile_once(cmd, kind, jobs, outdir, cwd, logfile, stress=0):
    os.makedirs(outdir, exist_ok=True)
    args = strip_options(cmd)
    if kind == "obj":
        if "-c" not in args:
            args.append("-c")
        args.append("-of=" + os.path.join(outdir, "out.o"))
    elif kind == "lib":
        args.append("-of=" + os.path.join(outdir, "out.a"))
    else:
        args.append("-od=" + outdir)
    args.append("-j=%d" % jobs)
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = "0"
    env["DMD_SPLIT_LOG"] = logfile
    if stress:
        env["DMD_SPLIT_STRESS"] = str(stress)
    else:
        env.pop("DMD_SPLIT_STRESS", None)
    if os.path.exists(logfile):
        os.remove(logfile)
    p = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = open(logfile).read().strip() if os.path.exists(logfile) else ""
    if p.returncode != 0:
        raise RuntimeError("-j=%d%s failed:\n%s" % (jobs, " (stress seed %d)" % stress if stress else "",
                                                   p.stdout.decode(errors="replace")))
    return log


def output_files(kind, outdir):
    if kind == "obj":
        return [os.path.join(outdir, "out.o")]
    if kind == "lib":
        return [os.path.join(outdir, "out.a")]
    return sorted(os.path.join(outdir, f) for f in os.listdir(outdir) if f.endswith(".o"))


def objects_of(kind, files):
    objs = []
    for f in files:
        data = open(f, "rb").read()
        if kind == "lib":
            objs.extend((os.path.basename(f) + "(" + n + ")", b) for n, b in read_archive(data, f))
        else:
            objs.append((os.path.basename(f), data))
    return objs


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("-j", "--jobs", default="2,3,8", help="worker counts to check, comma separated")
    ap.add_argument("-r", "--repeat", type=int, default=3, help="compilations of each -j=N compared byte for byte")
    ap.add_argument("--dmd", help="the compiler, replacing the first word of the command")
    ap.add_argument("--cwd", default=None, help="directory to run the command in")
    ap.add_argument("--keep", action="store_true", help="keep the outputs")
    ap.add_argument("--require-split", action="store_true", help="fail if a -j=N compilation is not split")
    ap.add_argument("--limit", type=int, default=20, help="differences reported per comparison")
    ap.add_argument("--stress", type=int, default=0, metavar="K",
                    help="compilations of each -j=N in the determinism stress mode, compared byte for byte")
    ap.add_argument("--stress-seed", type=int, default=1, metavar="S", help="the first stress seed")
    ap.add_argument("command", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    cmd = a.command
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        ap.error("no dmd command")
    if a.dmd:
        cmd = [a.dmd] + cmd[1:]
    kind = output_kind(cmd)
    jobs = [int(j) for j in a.jobs.split(",") if j]
    work = tempfile.mkdtemp(prefix="splitcheck.")
    logfile = os.path.join(work, "split.log")
    failed = False

    def report(msg):
        print(msg, flush=True)

    try:
        compile_once(cmd, kind, 1, os.path.join(work, "j1"), a.cwd, logfile)
        base = collect(objects_of(kind, output_files(kind, os.path.join(work, "j1"))))
        nfunc = sum(1 for d in base[0].values() if d[0][1].endswith("__text"))
        report("-j=1: %d symbols defined (%d functions), %d local" % (len(base[0]), nfunc, len(base[1])))
        for n in jobs:
            first = None
            for k in range(a.repeat):
                out = os.path.join(work, "j%d-%d" % (n, k))
                log = compile_once(cmd, kind, n, out, a.cwd, logfile)
                files = output_files(kind, out)
                blobs = [open(f, "rb").read() for f in files]
                if k == 0:
                    first = (files, blobs)
                    status = log if log else "not split"
                    report("-j=%d: %s" % (n, status))
                    if a.require_split and not log.endswith("succeeded"):
                        report("-j=%d: the compilation was not split" % n)
                        failed = True
                    if log.endswith("succeeded"):
                        probs = compare(base, collect(objects_of(kind, files)), "-j=%d" % n, report, a.limit)
                        if probs:
                            report("-j=%d: %d differences from -j=1" % (n, probs))
                            failed = True
                        else:
                            report("-j=%d: same symbols and contents as -j=1" % n)
                elif [os.path.basename(f) for f in files] != [os.path.basename(f) for f in first[0]] or \
                        blobs != first[1]:
                    report("-j=%d: compilation %d differs from the first" % (n, k + 1))
                    failed = True
                    firstobjs = [(os.path.basename(f), b) for f, b in zip(first[0], first[1])]
                    if kind == "lib":
                        firstobjs = [(n2, b2) for f, b in firstobjs for n2, b2 in read_archive(b, f)]
                    compare(collect(firstobjs), collect(objects_of(kind, files)),
                            "-j=%d compilation %d" % (n, k + 1), report, a.limit)
            if a.repeat > 1 and not failed:
                report("-j=%d: %d compilations byte for byte the same" % (n, a.repeat))
            stressed = 0
            for k in range(a.stress):
                seed = a.stress_seed + k
                out = os.path.join(work, "j%d-s%d" % (n, seed))
                log = compile_once(cmd, kind, n, out, a.cwd, logfile, seed)
                files = output_files(kind, out)
                if a.require_split and not log.endswith("succeeded"):
                    report("-j=%d stress seed %d: the compilation was not split: %s" % (n, seed, log or "not split"))
                    failed = True
                elif [os.path.basename(f) for f in files] != [os.path.basename(f) for f in first[0]] or \
                        [open(f, "rb").read() for f in files] != first[1]:
                    report("-j=%d stress seed %d: the output differs from the one compiled without stress" % (n, seed))
                    failed = True
                    firstobjs = [(os.path.basename(f), b) for f, b in zip(first[0], first[1])]
                    if kind == "lib":
                        firstobjs = [(n2, b2) for f, b in firstobjs for n2, b2 in read_archive(b, f)]
                    compare(collect(firstobjs), collect(objects_of(kind, files)),
                            "-j=%d stress seed %d" % (n, seed), report, a.limit)
                else:
                    stressed += 1
                shutil.rmtree(out, ignore_errors=True)
            if a.stress:
                report("-j=%d: %d of %d stressed compilations byte for byte the same (seeds %d-%d)" %
                       (n, stressed, a.stress, a.stress_seed, a.stress_seed + a.stress - 1))
    except (RuntimeError, ValueError) as e:
        report(str(e))
        failed = True
    finally:
        if a.keep:
            report("outputs kept in " + work)
        else:
            shutil.rmtree(work, ignore_errors=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
