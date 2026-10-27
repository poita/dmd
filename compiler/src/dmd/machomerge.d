/**
 * Merge the AArch64 Mach-O object files the workers of a split compilation write into
 * the one object file an unsplit compilation writes.
 *
 * The parts are relocatable objects (MH_OBJECT, MH_SUBSECTIONS_VIA_SYMBOLS) as
 * `dmd.backend.machobj` writes them. The merge does what `ld -r` does with them, and
 * keeps their debug information:
 *
 * $(UL
 * $(LI The sections of the same name are concatenated, in the order of the parts, each
 *   part's at an offset aligned as the part's section is. Debug sections come last.)
 * $(LI An external symbol is defined once: a weak definition in several parts is kept
 *   from the first part defining it, unless another part defines it strongly. The atom
 *   each dropped definition starts (the bytes up to the next symbol of its section) is
 *   removed with the frame description entry of its function, and the references to it
 *   go to the definition kept. Removing an atom shifts what follows by a multiple of
 *   the section's alignment, so the atoms keep their alignment; the rest of the removed
 *   atom's bytes are zeroed padding. A symbol defined in one part and undefined in
 *   others is defined; commons are merged as the linker merges them.)
 * $(LI The relocations are moved with their sections and refer to the merged symbols;
 *   a section relative relocation refers to the merged section and the address it
 *   holds is moved with its target.)
 * $(LI The debug information of each part is a compilation unit of its own, its
 *   sections concatenated with the others' and the offsets from one debug section
 *   into another, which have no relocations, rebased. The debug information of a
 *   removed function is removed: its subprogram, its line table rows, its address
 *   ranges and its location lists' entries.)
 * )
 *
 * The merge supports what the parts can hold and checks it; for anything else (or a
 * malformed part) it gives up with a reason, and the caller falls back to another way.
 *
 * Copyright:   Copyright (C) 1999-2026 by The D Language Foundation, All Rights Reserved
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/compiler/src/dmd/machomerge.d, _machomerge.d)
 */
module dmd.machomerge;

import core.stdc.string : memcpy, memset;

import dmd.backend.mach;

/**
 * Merge Mach-O object files.
 * Params:
 *      parts = the contents of the object files, in order
 *      result = receives the contents of the merged object file
 *      reason = set to why the merge is not done, when it is not
 * Returns:
 *      true if merged
 */
bool mergeMachObjects(const(ubyte)[][] parts, out ubyte[] result, out const(char)[] reason) nothrow
{
    try
    {
        Merger m;
        m.run(parts);
        result = m.output;
        return true;
    }
    catch (Exception e)
    {
        reason = e.msg;
        return false;
    }
}

private:

final class MergeError : Exception
{
    this(string msg) { super(msg); }
}

void fail(string msg)
{
    throw new MergeError(msg);
}

enum CPU_TYPE_ARM64 = 0x0100000C;
enum LC_DATA_IN_CODE = 0x29;

struct Reloc
{
    uint address;
    uint symbolnum;
    bool pcrel;
    ubyte length;
    bool extern_;
    ubyte type;

    static Reloc decode(const(ubyte)* p)
    {
        Reloc r;
        const a = rd32(p);
        const info = rd32(p + 4);
        if (a & R_SCATTERED)
            fail("scattered relocation");
        r.address = a;
        r.symbolnum = info & 0xFF_FFFF;
        r.pcrel = (info >> 24) & 1;
        r.length = (info >> 25) & 3;
        r.extern_ = (info >> 27) & 1;
        r.type = cast(ubyte)(info >> 28);
        return r;
    }

    void encode(ref Buffer buf) const
    {
        buf.put32(address);
        buf.put32(symbolnum | (pcrel << 24) | (length << 25) | (extern_ << 27) | (type << 28));
    }
}

/// A span of a section's bytes removed from the merged object file, in the part's offsets
struct Span
{
    ulong start, end;   // removed bytes
    ulong before;       // bytes removed before `start`
}

/// An atom removed for being a dropped weak definition
struct Dropped
{
    ulong start, end;   // offsets in the part's section
    uint ext;           // the external symbol defined there, in `Merger.exts`
}

enum Dwarf : ubyte
{
    none, info, abbrev, line, str, aranges, ranges, loc, pubnames, pubtypes,
}

struct Sect
{
    const(char)[] segname, sectname;
    ulong addr, size;
    uint align_;
    uint flags;
    const(ubyte)[] data;        // null for a zero fill section
    Reloc[] relocs;
    uint out_;                  // index of the output section
    ulong base;                 // offset of the part's bytes in the output section
    Span[] removed;             // sorted
    Dropped[] dropped;          // sorted
    bool[] relocDropped;        // the relocations in removed or dropped bytes

    bool zerofill() const { return isZerofill(flags); }

    /// Returns: the offset in the output section's part bytes of offset `o` in this section
    ulong map(ulong o) const
    {
        if (!removed.length)
            return o;
        size_t lo = 0, hi = removed.length;
        while (lo < hi)
        {
            const mid = (lo + hi) / 2;
            if (removed[mid].start <= o)
                lo = mid + 1;
            else
                hi = mid;
        }
        if (lo == 0)
            return o;
        const s = &removed[lo - 1];
        if (o < s.end)
            return s.start - s.before;
        return o - (s.before + s.end - s.start);
    }

    /// Returns: the dropped atom offset `o` is in, or null
    const(Dropped)* droppedAt(ulong o) const
    {
        size_t lo = 0, hi = dropped.length;
        while (lo < hi)
        {
            const mid = (lo + hi) / 2;
            if (dropped[mid].start <= o)
                lo = mid + 1;
            else
                hi = mid;
        }
        if (lo == 0 || o >= dropped[lo - 1].end)
            return null;
        return &dropped[lo - 1];
    }

    /// Returns: the size of the section's bytes in the output
    ulong mappedSize() const
    {
        return map(size);
    }
}

struct Sym
{
    const(char)[] name;
    ubyte type;
    ubyte sect;
    ushort desc;
    ulong value;

    bool isExt() const { return (type & N_EXT) != 0; }
    ubyte kind() const { return type & N_TYPE; }
}

struct Part
{
    const(ubyte)[] data;
    uint cputype, cpusubtype, flags;
    const(ubyte)[] versionCmd;
    Sect[] sects;
    Sym[] syms;
    uint[] outSym;      // the output symbol of each symbol, uint.max if removed
    uint[] symExt;      // the external symbol of each external symbol, in `Merger.exts`
    bool[] symDropped;  // the external definitions dropped for another
    Dwarf[] dwarf;      // the debug section kind of each section
    int[Dwarf.max + 1] dwarfSect = -1;  // the section of each debug section kind
    bool anyDropped;
}

/// The definition and references of an external symbol, merged
struct Ext
{
    const(char)[] name;
    int defPart = -1;   // the part whose definition is kept, -1 if none
    uint defSym;
    bool common;        // a common symbol (if no part defines it)
    ulong commonSize;
    uint commonAlign;
    ushort undefDesc;
    bool strongRef;     // referenced not weakly by some part
    uint outIndex = uint.max;
}

struct OutSect
{
    const(char)[] segname, sectname;
    uint flags;
    uint align_;
    ulong addr, size;
    Buffer data;
    Buffer relocs;
    uint nreloc;
    Dwarf dwarf;
    bool zerofill() const { return isZerofill(flags); }
}

bool isZerofill(uint flags)
{
    const t = flags & SECTION_TYPE;
    return t == S_ZEROFILL || t == S_GB_ZEROFILL || t == S_THREAD_LOCAL_ZEROFILL;
}

/// A growable byte buffer
struct Buffer
{
    ubyte[] buf;
    size_t length;

    void reserve(size_t n)
    {
        if (length + n > buf.length)
        {
            size_t cap = buf.length ? buf.length * 2 : 256;
            while (cap < length + n)
                cap *= 2;
            buf.length = cap;
        }
    }
    void put(const(ubyte)[] b)
    {
        reserve(b.length);
        buf[length .. length + b.length] = b[];
        length += b.length;
    }
    void put8(uint v) { reserve(1); buf[length++] = cast(ubyte)v; }
    void put16(uint v) { reserve(2); wr16(buf.ptr + length, v); length += 2; }
    void put32(uint v) { reserve(4); wr32(buf.ptr + length, v); length += 4; }
    void put64(ulong v) { reserve(8); wr64(buf.ptr + length, v); length += 8; }
    void zeros(size_t n) { reserve(n); buf[length .. length + n] = 0; length += n; }
    void putUleb(ulong v)
    {
        do
        {
            ubyte b = v & 0x7F;
            v >>= 7;
            if (v)
                b |= 0x80;
            put8(b);
        } while (v);
    }
    void putSleb(long v)
    {
        while (true)
        {
            ubyte b = v & 0x7F;
            v >>= 7;
            const done = (v == 0 && !(b & 0x40)) || (v == -1 && (b & 0x40));
            if (!done)
                b |= 0x80;
            put8(b);
            if (done)
                break;
        }
    }
    void alignTo(ulong a) { zeros(cast(size_t)((a - length % a) % a)); }
    inout(ubyte)[] opSlice() inout { return buf[0 .. length]; }
}

uint rd16(const(ubyte)* p) { return p[0] | p[1] << 8; }
uint rd32(const(ubyte)* p) { return p[0] | p[1] << 8 | p[2] << 16 | cast(uint)p[3] << 24; }
ulong rd64(const(ubyte)* p) { return rd32(p) | cast(ulong)rd32(p + 4) << 32; }
void wr16(ubyte* p, uint v) { p[0] = cast(ubyte)v; p[1] = cast(ubyte)(v >> 8); }
void wr32(ubyte* p, uint v) { foreach (i; 0 .. 4) p[i] = cast(ubyte)(v >> (8 * i)); }
void wr64(ubyte* p, ulong v) { foreach (i; 0 .. 8) p[i] = cast(ubyte)(v >> (8 * i)); }

const(char)[] fixedName(const(char)[] s)
{
    foreach (i, c; s)
        if (!c)
            return s[0 .. i];
    return s;
}

/// A reader of DWARF data
struct Reader
{
    const(ubyte)[] d;
    size_t pos;

    void need(size_t n) { if (pos + n > d.length) fail("truncated debug information"); }
    ubyte u8() { need(1); return d[pos++]; }
    uint u16() { need(2); auto v = rd16(d.ptr + pos); pos += 2; return v; }
    uint u32() { need(4); auto v = rd32(d.ptr + pos); pos += 4; return v; }
    ulong u64() { need(8); auto v = rd64(d.ptr + pos); pos += 8; return v; }
    ulong uleb()
    {
        ulong v;
        uint shift;
        while (true)
        {
            const b = u8();
            if (shift < 64)
                v |= cast(ulong)(b & 0x7F) << shift;
            shift += 7;
            if (!(b & 0x80))
                return v;
        }
    }
    long sleb()
    {
        long v;
        uint shift;
        ubyte b;
        do
        {
            b = u8();
            if (shift < 64)
                v |= cast(long)(b & 0x7F) << shift;
            shift += 7;
        } while (b & 0x80);
        if (shift < 64 && (b & 0x40))
            v |= -(1L << shift);
        return v;
    }
    void cstring()
    {
        while (u8()) {}
    }
    void skip(size_t n) { need(n); pos += n; }
}

// DWARF constants
enum : uint
{
    DW_TAG_subprogram = 0x2e,

    DW_AT_sibling = 0x01, DW_AT_location = 0x02, DW_AT_low_pc = 0x11, DW_AT_high_pc = 0x12,
    DW_AT_stmt_list = 0x10, DW_AT_return_addr = 0x2a, DW_AT_string_length = 0x19,
    DW_AT_data_member_location = 0x38, DW_AT_frame_base = 0x40, DW_AT_segment = 0x46,
    DW_AT_static_link = 0x48, DW_AT_use_location = 0x4a, DW_AT_vtable_elem_location = 0x4d,
    DW_AT_ranges = 0x55, DW_AT_start_scope = 0x2c, DW_AT_macro_info = 0x43,
    DW_AT_decl_file = 0x3a, DW_AT_call_file = 0x58,

    DW_FORM_addr = 0x01, DW_FORM_block2 = 0x03, DW_FORM_block4 = 0x04, DW_FORM_data2 = 0x05,
    DW_FORM_data4 = 0x06, DW_FORM_data8 = 0x07, DW_FORM_string = 0x08, DW_FORM_block = 0x09,
    DW_FORM_block1 = 0x0a, DW_FORM_data1 = 0x0b, DW_FORM_flag = 0x0c, DW_FORM_sdata = 0x0d,
    DW_FORM_strp = 0x0e, DW_FORM_udata = 0x0f, DW_FORM_ref_addr = 0x10, DW_FORM_ref1 = 0x11,
    DW_FORM_ref2 = 0x12, DW_FORM_ref4 = 0x13, DW_FORM_ref8 = 0x14, DW_FORM_ref_udata = 0x15,
    DW_FORM_indirect = 0x16, DW_FORM_sec_offset = 0x17, DW_FORM_exprloc = 0x18,
    DW_FORM_flag_present = 0x19, DW_FORM_ref_sig8 = 0x20,

    DW_LNS_copy = 1, DW_LNS_advance_pc = 2, DW_LNS_advance_line = 3, DW_LNS_set_file = 4,
    DW_LNS_set_column = 5, DW_LNS_negate_stmt = 6, DW_LNS_set_basic_block = 7,
    DW_LNS_const_add_pc = 8, DW_LNS_fixed_advance_pc = 9,
    DW_LNE_end_sequence = 1, DW_LNE_set_address = 2,
}

/// The kind of section offset an attribute of `form` holds, in a unit of `version`
enum Ptr : ubyte { none, line, loc, ranges }

Ptr ptrClass(uint at, uint form, uint version_)
{
    const offsetForm = form == DW_FORM_sec_offset ||
        (version_ < 4 && (form == DW_FORM_data4 || form == DW_FORM_data8));
    if (!offsetForm)
        return Ptr.none;
    switch (at)
    {
        case DW_AT_stmt_list:
            return Ptr.line;
        case DW_AT_location, DW_AT_string_length, DW_AT_return_addr, DW_AT_data_member_location,
             DW_AT_frame_base, DW_AT_segment, DW_AT_static_link, DW_AT_use_location,
             DW_AT_vtable_elem_location:
            return Ptr.loc;
        case DW_AT_ranges, DW_AT_start_scope:
            return Ptr.ranges;
        case DW_AT_macro_info:
            fail("macro information");
            assert(0);
        default:
            return Ptr.none;
    }
}

struct Abbrev
{
    uint tag;
    bool children;
    uint[2][] attrs;    // attribute, form
}

/// The one compilation unit of a part's debug_info
struct Unit
{
    bool present;
    size_t end;         // of the unit in the part's debug_info
    size_t dies;        // the offset of its first DIE
    uint version_;
}

/// The offset in the merged debug_info of a DIE of a part
struct DieAt
{
    ulong old, new_;
    bool isNull;        // the entry ending a list of children
}

/// The new offsets of the lists of a part's debug_loc
struct ListMap
{
    bool identity = true;
    ulong[ulong] starts;    // the new offset of each list, when not identity

    /// Returns: the new offset of a list starting at `o`
    ulong list(ulong o) const
    {
        if (identity)
            return o;
        if (auto p = o in starts)
            return *p;
        fail("reference to no list of a debug section");
        assert(0);
    }
}

/// The header of a line table
struct LineHeader
{
    bool present;
    uint version_;
    ubyte minInst, maxOps, defaultIsStmt, lineRange, opcodeBase;
    byte lineBase;
    const(ubyte)[] stdLengths;
    const(char)[][] dirs;
    static struct File
    {
        const(char)[] name;
        ulong dir, mtime, length;
    }
    File[] files;
    size_t programStart, end;
}

/// A row of a line table
struct LineRow
{
    ulong addr;
    uint file, column;
    long line;
    bool isStmt, endSeq;
}

struct Merger
{
    Part[] parts;
    Ext[] exts;
    uint[const(char)[]] extIndex;
    OutSect[] outs;
    uint[const(char)[]] outIndex;   // by "segname,sectname"
    uint nlocal, nextdef, nundef;
    ubyte[] output;

    // per part: the bases of its debug_str and debug_loc in the merged ones, the new
    // offsets of its location lists, its unit, its abbreviations and their codes in the
    // merged table, the file numbers of its line table in the merged one, the new
    // offsets of its DIEs, and its unit's range list
    ulong[Dwarf.max + 1][] dwarfBase;
    ListMap[] locMaps;
    Unit[] units;
    Abbrev[ulong][] abbrevs;
    const(Abbrev)*[][] abbrevTable;     // by code
    uint[][] codeMap;                   // the merged code of each code
    uint[][] fileMap;
    DieAt[][] dies;
    ulong[] cuRanges;
    int firstUnit = -1;         // the first part with a unit
    ulong combinedRanges;       // the offset of the merged unit's range list
    ulong infoSize;             // of the merged debug_info

    void run(const(ubyte)[][] inputs)
    {
        if (!inputs.length)
            fail("no parts");
        parts.length = inputs.length;
        foreach (i, d; inputs)
            parse(d, parts[i]);
        foreach (ref p; parts[1 .. $])
        {
            if (p.cputype != parts[0].cputype || p.cpusubtype != parts[0].cpusubtype ||
                p.flags != parts[0].flags || p.versionCmd != parts[0].versionCmd)
                fail("parts of different targets");
        }
        if (parts[0].cputype != CPU_TYPE_ARM64)
            fail("not AArch64");
        if (!(parts[0].flags & MH_SUBSECTIONS_VIA_SYMBOLS))
            fail("no subsections via symbols");
        planSections();
        resolveSymbols();
        planDrops();
        layoutSections();
        numberSymbols();
        copySections();
        copyDebugSections();
        write();
    }

    void parse(const(ubyte)[] d, ref Part p)
    {
        p.data = d;
        if (d.length < mach_header_64.sizeof)
            fail("truncated object file");
        if (rd32(d.ptr) != MH_MAGIC_64 || rd32(d.ptr + 12) != MH_OBJECT)
            fail("not a 64-bit Mach-O object file");
        p.cputype = rd32(d.ptr + 4);
        p.cpusubtype = rd32(d.ptr + 8);
        const ncmds = rd32(d.ptr + 16);
        p.flags = rd32(d.ptr + 24);
        size_t off = mach_header_64.sizeof;
        bool segment, symtab;
        uint symoff, nsyms, stroff, strsize;
        foreach (i; 0 .. ncmds)
        {
            if (off + 8 > d.length)
                fail("truncated load commands");
            const cmd = rd32(d.ptr + off);
            const cmdsize = rd32(d.ptr + off + 4);
            if (cmdsize < 8 || off + cmdsize > d.length)
                fail("bad load command");
            const c = d.ptr + off;
            switch (cmd)
            {
                case LC_SEGMENT_64:
                {
                    if (segment)
                        fail("several segments");
                    segment = true;
                    const nsects = rd32(c + 64);
                    if (72 + nsects * section_64.sizeof > cmdsize)
                        fail("bad segment command");
                    p.sects.length = nsects;
                    foreach (k; 0 .. nsects)
                    {
                        const h = c + 72 + k * section_64.sizeof;
                        auto s = &p.sects[k];
                        s.sectname = fixedName(cast(const(char)[])h[0 .. 16]);
                        s.segname = fixedName(cast(const(char)[])h[16 .. 32]);
                        s.addr = rd64(h + 32);
                        s.size = rd64(h + 40);
                        const offset = rd32(h + 48);
                        s.align_ = rd32(h + 52);
                        const reloff = rd32(h + 56);
                        const nreloc = rd32(h + 60);
                        s.flags = rd32(h + 64);
                        if (s.align_ > 15)
                            fail("bad section alignment");
                        if (!s.zerofill)
                        {
                            if (offset + s.size > d.length)
                                fail("truncated section");
                            s.data = d[offset .. cast(size_t)(offset + s.size)];
                        }
                        if (reloff + nreloc * 8UL > d.length)
                            fail("truncated relocations");
                        s.relocs.length = nreloc;
                        foreach (r; 0 .. nreloc)
                        {
                            s.relocs[r] = Reloc.decode(d.ptr + reloff + 8 * r);
                            if (s.relocs[r].address >= s.size)
                                fail("relocation outside its section");
                        }
                    }
                    break;
                }
                case LC_SYMTAB:
                    symtab = true;
                    symoff = rd32(c + 8);
                    nsyms = rd32(c + 12);
                    stroff = rd32(c + 16);
                    strsize = rd32(c + 20);
                    break;
                case LC_DYSYMTAB:
                    // the parts have no indirect symbols, table of contents, module table
                    // or external relocations
                    foreach (field; [9, 11, 13, 15, 17, 19])
                        if (rd32(c + 4 * field))
                            fail("dynamic symbol table entries");
                    break;
                case LC_VERSION_MIN_MACOSX, LC_BUILD_VERSION:
                    if (p.versionCmd.length)
                        fail("several version commands");
                    p.versionCmd = d[off .. off + cmdsize];
                    break;
                case LC_DATA_IN_CODE:
                    if (rd32(c + 12))
                        fail("data in code");
                    break;
                default:
                    fail("unknown load command");
            }
            off += cmdsize;
        }
        if (symtab)
        {
            if (symoff + nsyms * 16UL > d.length || stroff + strsize > d.length)
                fail("truncated symbol table");
            const strtab = cast(const(char)[])d[stroff .. stroff + strsize];
            p.syms.length = nsyms;
            foreach (k; 0 .. nsyms)
            {
                const e = d.ptr + symoff + 16 * k;
                auto s = &p.syms[k];
                const strx = rd32(e);
                if (strx >= strsize)
                    fail("bad symbol name");
                size_t end = strx;
                while (end < strsize && strtab[end])
                    ++end;
                s.name = strtab[strx .. end];
                s.type = e[4];
                s.sect = e[5];
                s.desc = cast(ushort)rd16(e + 6);
                s.value = rd64(e + 8);
                if (s.type & N_STAB)
                    fail("stabs");
                switch (s.kind)
                {
                    case N_UNDF:
                        if (!s.isExt)
                            fail("local undefined symbol");
                        break;
                    case N_ABS:
                        break;
                    case N_SECT:
                        if (!s.sect || s.sect > p.sects.length)
                            fail("bad symbol section");
                        break;
                    default:
                        fail("indirect symbol");
                }
            }
        }
        p.outSym.length = p.syms.length;
        p.symExt.length = p.syms.length;
        p.symDropped.length = p.syms.length;
        foreach (ref s; p.sects)
            s.relocDropped.length = s.relocs.length;
        p.dwarf.length = p.sects.length;
        foreach (k, ref s; p.sects)
        {
            const debug_ = (s.flags & S_ATTR_DEBUG) != 0;
            if (debug_ != (s.segname == "__DWARF"))
                fail("debug section outside __DWARF");
            if (!debug_)
                continue;
            Dwarf kind;
            switch (s.sectname)
            {
                case "__debug_info":     kind = Dwarf.info; break;
                case "__debug_abbrev":   kind = Dwarf.abbrev; break;
                case "__debug_line":     kind = Dwarf.line; break;
                case "__debug_str":      kind = Dwarf.str; break;
                case "__debug_aranges":  kind = Dwarf.aranges; break;
                case "__debug_ranges":   kind = Dwarf.ranges; break;
                case "__debug_loc":      kind = Dwarf.loc; break;
                case "__debug_pubnames": kind = Dwarf.pubnames; break;
                case "__debug_pubtypes": kind = Dwarf.pubtypes; break;
                default:
                    if (s.size)
                        fail("unknown debug section");
                    continue;
            }
            if (p.dwarfSect[kind] >= 0)
                fail("debug section twice");
            p.dwarf[k] = kind;
            p.dwarfSect[kind] = cast(int)k;
        }
    }

    /// The output sections: the parts' sections in order of first appearance, the
    /// zero fill ones after those with contents, and the debug ones last
    void planSections()
    {
        foreach (pass; 0 .. 3)
        {
            foreach (ref p; parts)
            {
                foreach (k, ref s; p.sects)
                {
                    const sectPass = p.dwarf[k] != Dwarf.none || s.flags & S_ATTR_DEBUG ? 2 : s.zerofill ? 1 : 0;
                    if (sectPass != pass)
                        continue;
                    const key = s.segname ~ "," ~ s.sectname;
                    if (auto o = key in outIndex)
                    {
                        auto os = &outs[*o];
                        if (os.flags != s.flags)
                            fail("sections of the same name and different types");
                        if (s.align_ > os.align_)
                            os.align_ = s.align_;
                        s.out_ = *o;
                        continue;
                    }
                    s.out_ = cast(uint)outs.length;
                    outIndex[key] = s.out_;
                    OutSect os;
                    os.segname = s.segname;
                    os.sectname = s.sectname;
                    os.flags = s.flags;
                    os.align_ = s.align_;
                    os.dwarf = p.dwarf[k];
                    outs ~= os;
                }
            }
        }
        if (outs.length > 255)
            fail("too many sections");
    }

    void resolveSymbols()
    {
        foreach (pi, ref p; parts)
        {
            foreach (si, ref s; p.syms)
            {
                if (!s.isExt)
                    continue;
                uint e;
                if (auto pe = s.name in extIndex)
                    e = *pe;
                else
                {
                    e = cast(uint)exts.length;
                    extIndex[s.name] = e;
                    Ext x;
                    x.name = s.name;
                    exts ~= x;
                }
                p.symExt[si] = e;
                auto x = &exts[e];
                if (s.kind == N_UNDF)
                {
                    if (s.value)        // a common symbol
                    {
                        x.common = true;
                        if (s.value > x.commonSize)
                            x.commonSize = s.value;
                        const a = (s.desc >> 8) & 0x0F;
                        if (a > x.commonAlign)
                            x.commonAlign = a;
                    }
                    else
                    {
                        if (!(s.desc & N_WEAK_REF))
                            x.strongRef = true;
                        x.undefDesc |= s.desc;
                    }
                    continue;
                }
                // a definition
                const weak = (s.desc & N_WEAK_DEF) != 0;
                if (x.defPart < 0)
                {
                    x.defPart = cast(int)pi;
                    x.defSym = cast(uint)si;
                    continue;
                }
                auto kept = &parts[x.defPart].syms[x.defSym];
                const keptWeak = (kept.desc & N_WEAK_DEF) != 0;
                if (!weak && !keptWeak)
                    fail("symbol defined twice");
                if (!weak)      // a strong definition replaces a weak one
                {
                    parts[x.defPart].symDropped[x.defSym] = true;
                    x.defPart = cast(int)pi;
                    x.defSym = cast(uint)si;
                }
                else
                    p.symDropped[si] = true;
            }
        }
        foreach (ref x; exts)
        {
            if (x.defPart < 0)
                continue;
            const s = &parts[x.defPart].syms[x.defSym];
            if (s.kind == N_ABS)
            {
                foreach (ref p; parts)
                    foreach (k, ref t; p.syms)
                        if (p.symDropped[k] && t.name == x.name)
                            fail("absolute symbol defined twice");
            }
        }
    }

    /// Find the atoms of the dropped definitions and the bytes to remove
    void planDrops()
    {
        foreach (pi, ref p; parts)
        {
            bool any;
            foreach (k, d; p.symDropped)
                if (d)
                {
                    if (p.syms[k].kind != N_SECT)
                        fail("dropped symbol not in a section");
                    any = true;
                }
            if (!any)
                continue;
            p.anyDropped = true;

            // The symbols of each section, by address: the atoms
            static struct At { ulong value; uint sym; }
            At[][] bySect;
            bySect.length = p.sects.length;
            foreach (k, ref s; p.syms)
                if (s.kind == N_SECT)
                    bySect[s.sect - 1] ~= At(s.value, cast(uint)k);
            foreach (si, ref list; bySect)
            {
                import core.stdc.stdlib : qsort;
                static extern (C) int cmp(scope const void* a, scope const void* b)
                {
                    const x = cast(const(At)*)a, y = cast(const(At)*)b;
                    return x.value < y.value ? -1 : x.value > y.value ? 1 :
                           x.sym < y.sym ? -1 : x.sym > y.sym;
                }
                if (list.length > 1)
                    qsort(list.ptr, list.length, At.sizeof, &cmp);
                auto sect = &p.sects[si];
                for (size_t i = 0; i < list.length; )
                {
                    size_t j = i;
                    bool dropped, kept;
                    uint ext = uint.max;
                    while (j < list.length && list[j].value == list[i].value)
                    {
                        const k = list[j].sym;
                        if (p.symDropped[k])
                        {
                            dropped = true;
                            ext = p.symExt[k];
                        }
                        else
                            kept = true;
                        ++j;
                    }
                    if (dropped)
                    {
                        if (kept)
                            fail("dropped definition at the address of another symbol");
                        const start = list[i].value - sect.addr;
                        const end = (j < list.length ? list[j].value : sect.addr + sect.size) - sect.addr;
                        if (start > sect.size || end > sect.size)
                            fail("symbol outside its section");
                        sect.dropped ~= Dropped(start, end, ext);
                    }
                    i = j;
                }
            }

            // The frame description entries of the dropped functions
            if (auto eh = sectionNamed(p, "__TEXT", "__eh_frame"))
            {
                planEhFrame(p, *eh);
                planLsdas(p, *eh);
            }

            // The bytes removed: a multiple of the alignment, so that what follows keeps
            // its alignment. In __eh_frame, the rest of a dropped record is padding of
            // the record before (see `fixFrameRecords`).
            foreach (ref sect; p.sects)
            {
                if (!sect.dropped.length)
                    continue;
                const a = 1UL << sect.align_;
                ulong before;
                foreach (ref d; sect.dropped)
                {
                    const n = (d.end - d.start) / a * a;
                    if (n)
                    {
                        sect.removed ~= Span(d.start, d.start + n, before);
                        before += n;
                    }
                }
                foreach (r, ref rel; sect.relocs)
                    if (sect.droppedAt(rel.address))
                        sect.relocDropped[r] = true;
                if (sect.flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS))
                    checkUnrelocatedBranches(sect);
            }

            // Local symbols in removed atoms go with them
            foreach (k, ref s; p.syms)
                if (!s.isExt && s.kind == N_SECT && p.sects[s.sect - 1].droppedAt(s.value - p.sects[s.sect - 1].addr))
                    p.outSym[k] = uint.max;
        }
    }

    static Sect* sectionNamed(ref Part p, const(char)[] seg, const(char)[] sect)
    {
        foreach (ref s; p.sects)
            if (s.segname == seg && s.sectname == sect)
                return &s;
        return null;
    }

    /// Mark the frame description entries of dropped functions dropped
    void planEhFrame(ref Part p, ref Sect eh)
    {
        // the relocations of each address
        size_t[] order = sortedRelocs(eh);
        size_t off;
        Dropped[] fdes;
        while (off < eh.size)
        {
            if (off + 4 > eh.size)
                fail("truncated frame record");
            const len = rd32(eh.data.ptr + off);
            if (len == 0xFFFF_FFFF)
                fail("64-bit frame record");
            const end = off + 4 + len;
            if (end > eh.size)
                fail("truncated frame record");
            if (len >= 4 && rd32(eh.data.ptr + off + 4) != 0)
            {
                // an FDE: its pc_begin is a SUBTRACTOR/UNSIGNED pair at off + 8
                const i = findReloc(eh, order, off + 8);
                if (i == size_t.max || i + 1 >= eh.relocs.length ||
                    eh.relocs[i].type != ARM64_RELOC_SUBTRACTOR)
                    fail("frame description entry without its function");
                const u = eh.relocs[i + 1];
                bool dropped;
                uint ext;
                if (u.extern_)
                {
                    if (u.symbolnum >= p.syms.length)
                        fail("bad relocation symbol");
                    if (p.symDropped[u.symbolnum])
                    {
                        dropped = true;
                        ext = p.symExt[u.symbolnum];
                    }
                }
                else
                {
                    const v = rd64(eh.data.ptr + off + 8);
                    if (!u.symbolnum || u.symbolnum > p.sects.length)
                        fail("bad relocation section");
                    const t = &p.sects[u.symbolnum - 1];
                    if (auto d = t.droppedAt(v - t.addr))
                    {
                        dropped = true;
                        ext = d.ext;
                    }
                }
                if (dropped)
                    fdes ~= Dropped(off, end, ext);
            }
            off = end;
        }
        if (!fdes.length)
            return;
        // merge with the atoms dropped for symbols in the section, if any
        if (eh.dropped.length)
            fail("dropped definition in __eh_frame");
        eh.dropped = fdes;
    }

    /// Drop the LSDAs that only dropped frame description entries of `eh` refer to
    void planLsdas(ref Part p, ref Sect eh)
    {
        if (!eh.dropped.length)
            return;
        auto lsdaSect = sectionNamed(p, "__TEXT", "__gcc_except_tab");
        if (!lsdaSect)
            return;
        const lsdaIndex = cast(uint)(lsdaSect - p.sects.ptr) + 1;
        bool[uint] lsdas;
        foreach (ref r; eh.relocs)
        {
            if (!r.extern_ || !eh.droppedAt(r.address) || r.symbolnum >= p.syms.length)
                continue;
            const s = &p.syms[r.symbolnum];
            if (!s.isExt && s.kind == N_SECT && s.sect == lsdaIndex)
                lsdas[r.symbolnum] = true;
        }
        if (!lsdas.length)
            return;
        foreach (ref sect; p.sects)
            foreach (ref r; sect.relocs)
                if (r.extern_ && (r.symbolnum in lsdas) && !sect.droppedAt(r.address))
                    lsdas.remove(r.symbolnum);
        if (!lsdas.length)
            return;
        // the atoms of the LSDAs: up to the next symbol of the section
        ulong[] starts;
        foreach (ref s; p.syms)
            if (s.kind == N_SECT && s.sect == lsdaIndex)
                starts ~= s.value - lsdaSect.addr;
        foreach (k; lsdas.byKey)
        {
            const start = p.syms[k].value - lsdaSect.addr;
            ulong end = lsdaSect.size;
            foreach (o; starts)
                if (o > start && o < end)
                    end = o;
            foreach (j, ref s; p.syms)
                if (j != k && s.kind == N_SECT && s.sect == lsdaIndex && s.value - lsdaSect.addr == start)
                    fail("LSDA at the address of another symbol");
            lsdaSect.dropped ~= Dropped(start, end, uint.max);
        }
        import core.stdc.stdlib : qsort;
        static extern (C) int cmp(scope const void* a, scope const void* b)
        {
            const x = cast(const(Dropped)*)a, y = cast(const(Dropped)*)b;
            return x.start < y.start ? -1 : x.start > y.start;
        }
        qsort(lsdaSect.dropped.ptr, lsdaSect.dropped.length, Dropped.sizeof, &cmp);
    }

    /// Fail if an instruction branches without relocation out of its atom across
    /// removed bytes
    void checkUnrelocatedBranches(ref Sect sect)
    {
        if (!sect.removed.length)
            return;
        size_t[] order = sortedRelocs(sect);
        size_t ri;
        for (ulong o = 0; o + 4 <= sect.size; o += 4)
        {
            while (ri < order.length && sect.relocs[order[ri]].address < o)
                ++ri;
            if (ri < order.length && sect.relocs[order[ri]].address == o)
                continue;
            if (sect.droppedAt(o))
                continue;
            const insn = rd32(sect.data.ptr + o);
            long disp;
            bool branch = true;
            if ((insn & 0x7C00_0000) == 0x1400_0000)                // B, BL
                disp = signExtend(insn & 0x3FF_FFFF, 26) * 4;
            else if ((insn & 0xFF00_0010) == 0x5400_0000 ||         // B.cond
                     (insn & 0x7E00_0000) == 0x3400_0000 ||         // CBZ, CBNZ
                     (insn & 0x3B00_0000) == 0x1800_0000)           // LDR (literal)
                disp = signExtend((insn >> 5) & 0x7_FFFF, 19) * 4;
            else if ((insn & 0x7E00_0000) == 0x3600_0000)           // TBZ, TBNZ
                disp = signExtend((insn >> 5) & 0x3FFF, 14) * 4;
            else if ((insn & 0x9F00_0000) == 0x1000_0000)           // ADR
                disp = signExtend(((insn >> 5) & 0x7_FFFF) << 2 | ((insn >> 29) & 3), 21);
            else
                branch = false;
            if (!branch)
                continue;
            const target = cast(long)o + disp;
            if (target < 0 || target > sect.size)
                continue;       // not an instruction branching in the section
            if (sect.map(target) - sect.map(o) != cast(ulong)(target - cast(long)o))
                fail("unrelocated branch across a dropped definition");
        }
    }

    static long signExtend(ulong v, uint bits)
    {
        const m = 1UL << (bits - 1);
        return cast(long)((v ^ m) - m);
    }

    static size_t[] sortedRelocs(ref const Sect s)
    {
        auto order = new size_t[s.relocs.length];
        foreach (i, ref o; order)
            o = i;
        bool sorted = true;
        foreach (i; 1 .. s.relocs.length)
            if (s.relocs[i].address < s.relocs[i - 1].address)
                sorted = false;
        if (!sorted)
        {
            import core.stdc.stdlib : qsort;
            static __gshared const(Reloc)[] relocs;
            relocs = s.relocs;
            static extern (C) int cmp(scope const void* a, scope const void* b)
            {
                const x = *cast(const(size_t)*)a, y = *cast(const(size_t)*)b;
                const ax = relocs[x].address, ay = relocs[y].address;
                return ax < ay ? -1 : ax > ay ? 1 : x < y ? -1 : x > y;
            }
            qsort(order.ptr, order.length, size_t.sizeof, &cmp);
            relocs = null;
        }
        return order;
    }

    /// Returns: the index of the first relocation at `address`, size_t.max if none
    static size_t findReloc(ref const Sect s, const size_t[] order, ulong address)
    {
        size_t lo = 0, hi = order.length;
        while (lo < hi)
        {
            const mid = (lo + hi) / 2;
            if (s.relocs[order[mid]].address < address)
                lo = mid + 1;
            else
                hi = mid;
        }
        if (lo < order.length && s.relocs[order[lo]].address == address)
            return order[lo];
        return size_t.max;
    }

    /// Place the parts' bytes in the output sections, but for the debug sections,
    /// whose sizes are known once they are rewritten
    void layoutSections()
    {
        foreach (oi, ref os; outs)
        {
            if (os.dwarf != Dwarf.none || os.flags & S_ATTR_DEBUG)
                continue;
            ulong size;
            foreach (ref p; parts)
                foreach (ref s; p.sects)
                {
                    if (s.out_ != oi)
                        continue;
                    const a = 1UL << s.align_;
                    const aligned = (size + a - 1) & ~(a - 1);
                    if (aligned != size && isEhFrame(os.segname, os.sectname))
                        fail("frame records not aligned");
                    s.base = aligned;
                    size = aligned + s.mappedSize();
                    // the records of the next part follow aligned: the last record here
                    // is padded to them
                    if (isEhFrame(os.segname, os.sectname))
                        size = (size + a - 1) & ~(a - 1);
                }
            os.size = size;
        }
        assignAddresses(false);
    }

    void assignAddresses(bool debugToo)
    {
        ulong addr;
        foreach (ref os; outs)
        {
            const isDebug = os.dwarf != Dwarf.none || (os.flags & S_ATTR_DEBUG);
            if (isDebug && !debugToo)
                break;
            const a = 1UL << os.align_;
            addr = (addr + a - 1) & ~(a - 1);
            os.addr = addr;
            addr += os.size;
        }
    }

    /// Returns: the address in the output of offset `o` of section `s` of part `p`
    ulong outAddress(ref const Part p, uint s, ulong o) const
    {
        const sect = &p.sects[s];
        return outs[sect.out_].addr + sect.base + sect.map(o);
    }

    /// Number the output symbols: the local ones first, then the external definitions,
    /// then the undefined ones
    void numberSymbols()
    {
        uint n;
        foreach (ref p; parts)
            foreach (k, ref s; p.syms)
                if (!s.isExt && p.outSym[k] != uint.max)
                    p.outSym[k] = n++;
        nlocal = n;
        // external definitions in the order of the parts defining them
        foreach (pi, ref p; parts)
            foreach (k, ref s; p.syms)
                if (s.isExt && s.kind != N_UNDF && !p.symDropped[k])
                    exts[p.symExt[k]].outIndex = n++;
        nextdef = n - nlocal;
        foreach (ref p; parts)
            foreach (k, ref s; p.syms)
                if (s.isExt && s.kind == N_UNDF)
                {
                    auto x = &exts[p.symExt[k]];
                    if (x.defPart < 0 && x.outIndex == uint.max)
                        x.outIndex = n++;
                }
        nundef = n - nlocal - nextdef;
        foreach (ref p; parts)
            foreach (k, ref s; p.syms)
                if (s.isExt)
                    p.outSym[k] = exts[p.symExt[k]].outIndex;
        if (n > 0xFF_FFFF)
            fail("too many symbols");
    }

    /// The address in the output a section relative address refers to, and the section
    /// it is in, of part `p`, which refers to section `s` (numbered from 1)
    void retarget(ref const Part p, uint s, ulong value, bool end, out ulong addr, out uint outSect)
    {
        if (!s || s > p.sects.length)
            fail("bad relocation section");
        const t = &p.sects[s - 1];
        const o = value - t.addr;
        if (!end)
        {
            if (auto d = t.droppedAt(o))
            {
                // to the definition kept
                if (d.ext == uint.max)
                    fail("reference to a removed LSDA");
                const x = &exts[d.ext];
                if (x.defPart < 0)
                    fail("dropped definition without a kept one");
                const kp = &parts[x.defPart];
                const ks = &kp.syms[x.defSym];
                if (ks.kind != N_SECT)
                    fail("reference to an absolute symbol");
                const kt = &kp.sects[ks.sect - 1];
                addr = outAddress(*kp, ks.sect - 1, ks.value - kt.addr) + (o - d.start);
                outSect = kt.out_ + 1;
                return;
            }
        }
        addr = outAddress(p, s - 1, o);
        outSect = t.out_ + 1;
    }

    /**
     * Translate a relocation of part `p`'s section `s` to the output.
     * Params:
     *  p = the part
     *  s = the section index
     *  r = the relocation, of the part
     *  prev = the relocation before it at the same address, if any (of a pair)
     *  field = the bytes of the field relocated, in the output, holding the part's value
     *  end = the field is the end of an address range
     * Returns: the relocation for the output
     */
    Reloc translate(ref const Part p, uint s, Reloc r, const(Reloc)* prev, ubyte* field, bool end)
    {
        Reloc o = r;
        if (r.type == ARM64_RELOC_ADDEND)
            return o;
        if (r.extern_)
        {
            if (r.symbolnum >= p.syms.length || p.outSym[r.symbolnum] == uint.max)
                fail("relocation to a removed symbol");
            o.symbolnum = p.outSym[r.symbolnum];
            return o;
        }
        if (r.type != ARM64_RELOC_UNSIGNED)
            fail("section relative relocation other than UNSIGNED");
        if (r.length != 2 && r.length != 3)
            fail("bad relocation length");
        // the linker gives these no meaning the parts rely on
        if (prev && prev.type == ARM64_RELOC_SUBTRACTOR)
            fail("section relative subtrahend");
        if (r.pcrel)
            fail("pc relative UNSIGNED relocation");
        const ulong target = r.length == 3 ? rd64(field) : rd32(field);
        ulong addr;
        uint outSect;
        retarget(p, r.symbolnum, target, end, addr, outSect);
        if (r.length == 3)
            wr64(field, addr);
        else
        {
            if (addr > uint.max)
                fail("relocated address too large");
            wr32(field, cast(uint)addr);
        }
        o.symbolnum = outSect;
        return o;
    }

    /// Copy the parts' bytes of the sections but the debug ones, translating their
    /// relocations
    void copySections()
    {
        foreach (oi, ref os; outs)
        {
            if (os.dwarf != Dwarf.none || os.flags & S_ATTR_DEBUG)
                continue;
            if (!os.zerofill)
                os.data.reserve(cast(size_t)os.size);
            foreach (ref p; parts)
                foreach (si, ref s; p.sects)
                {
                    if (s.out_ != oi)
                        continue;
                    if (os.zerofill)
                        continue;
                    os.data.zeros(cast(size_t)(s.base - os.data.length));
                    const start = os.data.length;
                    // the kept bytes, the removed ones left out, the dropped ones zeroed
                    ulong o;
                    foreach (ref span; s.removed)
                    {
                        os.data.put(s.data[cast(size_t)o .. cast(size_t)span.start]);
                        o = span.end;
                    }
                    os.data.put(s.data[cast(size_t)o .. $]);
                    foreach (ref d; s.dropped)
                    {
                        const from = start + s.map(d.start);
                        const to = start + s.map(d.end);
                        os.data.buf[from .. to] = 0;
                    }
                    if (isEhFrame(s.segname, s.sectname))
                    {
                        const a = 1UL << s.align_;
                        const chunk = (s.mappedSize() + a - 1) & ~(a - 1);
                        os.data.zeros(cast(size_t)(start + chunk - os.data.length));
                        if (s.dropped.length || chunk != s.size)
                            fixFrameRecords(s, os.data.buf.ptr + start, chunk);
                    }
                    copyRelocs(p, cast(uint)si, os, start, (ref const Reloc r) => false);
                }
            if (!os.zerofill && os.data.length != os.size)
                fail("section size mismatch");
        }
    }

    static bool isEhFrame(const(char)[] seg, const(char)[] sect)
    {
        return seg == "__TEXT" && sect == "__eh_frame";
    }

    /**
     * Rewrite the records kept of `eh`, copied to `bytes`, for the records removed: the
     * distance of a frame description entry back to its CIE, and the length of each,
     * which takes in what follows it up to the next record kept or the end of the
     * `chunk` as padding (DW_CFA_nop).
     */
    static void fixFrameRecords(ref const Sect eh, ubyte* bytes, ulong chunk)
    {
        size_t off;
        long last = -1;       // the record kept before
        while (off < eh.size)
        {
            const len = rd32(eh.data.ptr + off);
            if (len < 4)
                fail("frame record without an identifier");
            const id = rd32(eh.data.ptr + off + 4);
            if (!eh.droppedAt(off))
            {
                if (id)
                {
                    const cie = off + 4 - id;
                    if (eh.droppedAt(cie))
                        fail("frame description entry of a removed CIE");
                    wr32(bytes + eh.map(off) + 4, cast(uint)(eh.map(off + 4) - eh.map(cie)));
                }
                if (last >= 0)
                    wr32(bytes + eh.map(last), cast(uint)(eh.map(off) - eh.map(last) - 4));
                last = off;
            }
            off += 4 + len;
        }
        if (last >= 0)
            wr32(bytes + eh.map(last), cast(uint)(chunk - eh.map(last) - 4));
    }

    /// Translate the relocations of part `p`'s section `si` to `os`, whose bytes for the
    /// section start at `start`
    void copyRelocs(ref const Part p, uint si, ref OutSect os, size_t start,
                    scope bool delegate(ref const Reloc) isEnd)
    {
        const s = &p.sects[si];
        const(Reloc)* prev;
        foreach (ri, ref r; s.relocs)
        {
            const pr = prev;
            prev = &r;
            if (s.relocDropped[ri])
                continue;
            const newOff = s.map(r.address);
            auto field = os.data.buf.ptr + start + newOff;
            const paired = pr && pr.address == r.address ? pr : null;
            Reloc t = translate(p, si, r, paired, field, isEnd(r));
            t.address = cast(uint)(s.base + newOff);
            t.encode(os.relocs);
            ++os.nreloc;
        }
    }

    // ------------------------------------------------------------------------
    // Debug information
    //
    // The parts' units are merged into one, as lldb, reading the debug information of
    // the object files of a program through its debug map, takes an object file's first
    // unit for all of it. The merged unit is the first part's unit DIE, followed by the
    // children of every part's unit, in order. The abbreviation tables and the line
    // tables are merged with them, and the file numbers of the DIEs renumbered.

    void copyDebugSections()
    {
        const n = parts.length;
        dwarfBase.length = n;
        locMaps.length = n;
        units.length = n;
        codeMap.length = n;
        abbrevTable.length = n;
        abbrevs.length = n;
        fileMap.length = n;
        dies.length = n;
        cuRanges.length = n;
        foreach (pi, ref p; parts)
            readUnit(p, pi);

        foreach (kind; [Dwarf.abbrev, Dwarf.str, Dwarf.line, Dwarf.loc, Dwarf.ranges, Dwarf.info,
                        Dwarf.aranges, Dwarf.pubnames, Dwarf.pubtypes])
        {
            OutSect* os;
            foreach (ref o; outs)
                if (o.dwarf == kind)
                    os = &o;
            if (!os)
                continue;
            final switch (kind)
            {
                case Dwarf.abbrev:   writeAbbrevs(*os); break;
                case Dwarf.line:     writeLine(*os); break;
                case Dwarf.ranges:   writeRanges(*os); break;
                case Dwarf.info:     writeInfo(*os); break;
                case Dwarf.aranges:  writeAranges(*os); break;
                case Dwarf.pubnames, Dwarf.pubtypes:
                    writePubnames(kind, *os);
                    break;
                case Dwarf.str, Dwarf.loc:
                    foreach (pi, ref p; parts)
                    {
                        const si = p.dwarfSect[kind];
                        if (si < 0)
                            continue;
                        dwarfBase[pi][kind] = os.data.length;
                        if (kind == Dwarf.loc)
                            copyLocs(p, pi, si, *os);
                        else
                        {
                            if (p.sects[si].relocs.length)
                                fail("relocations in debug_str");
                            os.data.put(p.sects[si].data);
                        }
                    }
                    break;
                case Dwarf.none:
                    assert(0);
            }
            os.size = os.data.length;
        }
        foreach (ref os; outs)
            if (os.flags & S_ATTR_DEBUG && os.dwarf == Dwarf.none)
                os.size = 0;
        // the addresses of the debug sections, after the others', which they do not move
        ulong[] addrs;
        foreach (ref os; outs)
            addrs ~= os.addr;
        assignAddresses(true);
        foreach (i, ref os; outs)
            if (!(os.dwarf != Dwarf.none || os.flags & S_ATTR_DEBUG) && os.addr != addrs[i])
                fail("section moved");
    }

    /// Read the header of the one unit of part `p`'s debug_info, and its abbreviations
    void readUnit(ref Part p, size_t pi)
    {
        const si = p.dwarfSect[Dwarf.info];
        if (si < 0)
            return;
        const info = &p.sects[si];
        if (!info.size)
            return;
        const abbrevSi = p.dwarfSect[Dwarf.abbrev];
        if (abbrevSi < 0)
            fail("debug_info without debug_abbrev");
        Reader r = Reader(info.data);
        Unit u;
        const len = r.u32();
        if (len >= 0xFFFF_FFF0)
            fail("64-bit DWARF");
        u.end = r.pos + len;
        if (u.end != info.data.length)
            fail("not one unit in debug_info");
        u.version_ = r.u16();
        if (u.version_ < 2 || u.version_ > 4)
            fail("DWARF version");
        const abbrevOff = r.u32();
        if (r.u8() != 8)
            fail("address size");
        u.dies = r.pos;
        u.present = true;
        units[pi] = u;
        abbrevs[pi] = parseAbbrevs(p.sects[abbrevSi].data, abbrevOff);
        foreach (code, ref a; abbrevs[pi])
        {
            if (code > 0xFFFF)
                fail("abbreviation code too large");
            if (code >= abbrevTable[pi].length)
                abbrevTable[pi].length = cast(size_t)code + 1;
            abbrevTable[pi][cast(size_t)code] = &a;
        }
        if (firstUnit < 0)
            firstUnit = cast(int)pi;
        else if (units[firstUnit].version_ != u.version_)
            fail("units of different DWARF versions");

        // the range list of the unit DIE
        Reader dr = Reader(info.data, u.dies);
        const code = dr.uleb();
        const ab = code in abbrevs[pi];
        if (!ab)
            fail("unknown abbreviation");
        cuRanges[pi] = ulong.max;
        foreach (ref af; ab.attrs)
        {
            uint form = af[1];
            while (form == DW_FORM_indirect)
                form = cast(uint)dr.uleb();
            const at = dr.pos;
            skipForm(dr, form, u.version_);
            if (ptrClass(af[0], form, u.version_) == Ptr.ranges)
                cuRanges[pi] = form == DW_FORM_data8 ? rd64(info.data.ptr + at) : rd32(info.data.ptr + at);
        }
    }

    static Abbrev[ulong] parseAbbrevs(const(ubyte)[] data, size_t offset)
    {
        Abbrev[ulong] result;
        Reader r = Reader(data, offset);
        while (true)
        {
            const code = r.uleb();
            if (!code)
                break;
            Abbrev a;
            a.tag = cast(uint)r.uleb();
            a.children = r.u8() != 0;
            while (true)
            {
                const at = cast(uint)r.uleb();
                const form = cast(uint)r.uleb();
                if (!at && !form)
                    break;
                if (form == 0x21)
                    fail("implicit constant");
                a.attrs ~= [at, form];
            }
            result[code] = a;
        }
        return result;
    }

    static void skipForm(ref Reader r, uint form, uint version_)
    {
        switch (form)
        {
            case DW_FORM_addr: r.skip(8); break;
            case DW_FORM_data1, DW_FORM_ref1, DW_FORM_flag: r.skip(1); break;
            case DW_FORM_data2, DW_FORM_ref2: r.skip(2); break;
            case DW_FORM_data4, DW_FORM_ref4, DW_FORM_strp, DW_FORM_sec_offset: r.skip(4); break;
            case DW_FORM_data8, DW_FORM_ref8, DW_FORM_ref_sig8: r.skip(8); break;
            case DW_FORM_ref_addr: r.skip(version_ == 2 ? 8 : 4); break;
            case DW_FORM_sdata: r.sleb(); break;
            case DW_FORM_udata, DW_FORM_ref_udata: r.uleb(); break;
            case DW_FORM_string: r.cstring(); break;
            case DW_FORM_block1: r.skip(r.u8()); break;
            case DW_FORM_block2: r.skip(r.u16()); break;
            case DW_FORM_block4: r.skip(r.u32()); break;
            case DW_FORM_block, DW_FORM_exprloc: r.skip(cast(size_t)r.uleb()); break;
            case DW_FORM_flag_present: break;
            default:
                fail("unknown attribute form");
        }
    }

    /// The merged abbreviation table: the parts' abbreviations once each, numbered in
    /// order of first appearance
    void writeAbbrevs(ref OutSect os)
    {
        uint[string] codes;
        foreach (pi, ref p; parts)
        {
            if (!units[pi].present)
                continue;
            ulong[] keys = abbrevs[pi].keys;
            import core.stdc.stdlib : qsort;
            static extern (C) int cmp(scope const void* a, scope const void* b)
            {
                const x = *cast(const(ulong)*)a, y = *cast(const(ulong)*)b;
                return x < y ? -1 : x > y;
            }
            qsort(keys.ptr, keys.length, ulong.sizeof, &cmp);
            foreach (code; keys)
            {
                const a = &abbrevs[pi][code];
                Buffer b;
                b.putUleb(a.tag);
                b.put8(a.children);
                foreach (ref af; a.attrs)
                {
                    b.putUleb(af[0]);
                    b.putUleb(af[1]);
                }
                b.put8(0);
                b.put8(0);
                const key = cast(string)b[].idup;
                uint c;
                if (auto pc = key in codes)
                    c = *pc;
                else
                {
                    c = cast(uint)codes.length + 1;
                    codes[key] = c;
                    os.data.putUleb(c);
                    os.data.put(b[]);
                }
                if (code >= codeMap[pi].length)
                    codeMap[pi].length = cast(size_t)code + 1;
                codeMap[pi][cast(size_t)code] = c;
            }
        }
        os.data.put8(0);
    }

    /// Read the header of a part's line table, which has one unit
    static LineHeader readLineHeader(ref const Sect sect)
    {
        LineHeader h;
        Reader rd = Reader(sect.data);
        const len = rd.u32();
        if (len >= 0xFFFF_FFF0)
            fail("64-bit DWARF");
        h.end = rd.pos + len;
        if (h.end != sect.data.length)
            fail("not one unit in debug_line");
        h.version_ = rd.u16();
        if (h.version_ < 2 || h.version_ > 4)
            fail("line table version");
        const headerLength = rd.u32();
        h.programStart = rd.pos + headerLength;
        h.minInst = rd.u8();
        h.maxOps = h.version_ >= 4 ? rd.u8() : 1;
        h.defaultIsStmt = rd.u8();
        h.lineBase = cast(byte)rd.u8();
        h.lineRange = rd.u8();
        h.opcodeBase = rd.u8();
        if (!h.lineRange || !h.minInst || !h.opcodeBase || h.maxOps != 1)
            fail("bad line table header");
        rd.need(h.opcodeBase - 1);
        h.stdLengths = sect.data[rd.pos .. rd.pos + h.opcodeBase - 1];
        rd.pos += h.opcodeBase - 1;
        while (true)
        {
            const s = rd.pos;
            rd.cstring();
            if (rd.pos == s + 1)
                break;
            h.dirs ~= cast(const(char)[])sect.data[s .. rd.pos - 1];
        }
        while (true)
        {
            const s = rd.pos;
            rd.cstring();
            if (rd.pos == s + 1)
                break;
            LineHeader.File f;
            f.name = cast(const(char)[])sect.data[s .. rd.pos - 1];
            f.dir = rd.uleb();
            f.mtime = rd.uleb();
            f.length = rd.uleb();
            h.files ~= f;
        }
        if (rd.pos != h.programStart)
            fail("line table header length");
        return h;
    }

    /// The merged line table: one unit, with the parts' directories and files once
    /// each, and the parts' line programs, without the rows of removed code
    void writeLine(ref OutSect os)
    {
        LineHeader[] headers;
        headers.length = parts.length;
        int first = -1;
        foreach (pi, ref p; parts)
        {
            const si = p.dwarfSect[Dwarf.line];
            if (si < 0 || !p.sects[si].size)
                continue;
            headers[pi] = readLineHeader(p.sects[si]);
            headers[pi].present = true;
            if (first < 0)
            {
                first = cast(int)pi;
                continue;
            }
            const h = &headers[pi], f = &headers[first];
            if (h.version_ != f.version_ || h.minInst != f.minInst || h.defaultIsStmt != f.defaultIsStmt ||
                h.lineBase != f.lineBase || h.lineRange != f.lineRange || h.opcodeBase != f.opcodeBase ||
                h.stdLengths != f.stdLengths)
                fail("line tables of different parameters");
        }
        if (first < 0)
            return;
        const hdr = &headers[first];

        // the directories and files
        const(char)[][] dirs;
        uint[const(char)[]] dirIndex;
        LineHeader.File[] files;
        uint[string] fileIndex;
        foreach (pi, ref h; headers)
        {
            if (!h.present)
                continue;
            uint[] dmap = new uint[h.dirs.length + 1];
            foreach (k, d; h.dirs)
            {
                if (auto pd = d in dirIndex)
                    dmap[k + 1] = *pd;
                else
                {
                    dirs ~= d;
                    dmap[k + 1] = dirIndex[d] = cast(uint)dirs.length;
                }
            }
            fileMap[pi] = new uint[h.files.length + 1];
            foreach (k, f; h.files)
            {
                if (f.dir > h.dirs.length)
                    fail("bad line table directory");
                LineHeader.File g = f;
                g.dir = dmap[cast(size_t)f.dir];
                Buffer key;
                key.put(cast(const(ubyte)[])g.name);
                key.put8(0);
                key.putUleb(g.dir);
                key.putUleb(g.mtime);
                key.putUleb(g.length);
                const ks = cast(string)key[].idup;
                if (auto pf = ks in fileIndex)
                    fileMap[pi][k + 1] = *pf;
                else
                {
                    files ~= g;
                    fileMap[pi][k + 1] = fileIndex[ks] = cast(uint)files.length;
                }
            }
        }

        // the header
        const unitStart = os.data.length;
        os.data.put32(0);
        os.data.put16(hdr.version_);
        const headerLengthAt = os.data.length;
        os.data.put32(0);
        os.data.put8(hdr.minInst);
        if (hdr.version_ >= 4)
            os.data.put8(hdr.maxOps);
        os.data.put8(hdr.defaultIsStmt);
        os.data.put8(cast(ubyte)hdr.lineBase);
        os.data.put8(hdr.lineRange);
        os.data.put8(hdr.opcodeBase);
        os.data.put(hdr.stdLengths);
        foreach (d; dirs)
        {
            os.data.put(cast(const(ubyte)[])d);
            os.data.put8(0);
        }
        os.data.put8(0);
        foreach (ref f; files)
        {
            os.data.put(cast(const(ubyte)[])f.name);
            os.data.put8(0);
            os.data.putUleb(f.dir);
            os.data.putUleb(f.mtime);
            os.data.putUleb(f.length);
        }
        os.data.put8(0);
        wr32(os.data.buf.ptr + headerLengthAt, cast(uint)(os.data.length - headerLengthAt - 4));

        // the programs
        foreach (pi, ref p; parts)
            if (headers[pi].present)
                copyLineProgram(p, pi, p.dwarfSect[Dwarf.line], headers[pi], os);
        wr32(os.data.buf.ptr + unitStart, cast(uint)(os.data.length - unitStart - 4));
    }

    /// Append the sequences of part `p`'s line program to `os`, at the addresses the
    /// code is at in the merged object file
    void copyLineProgram(ref Part p, size_t pi, int si, ref const LineHeader h, ref OutSect os)
    {
        auto sect = &p.sects[si];
        auto order = sortedRelocs(*sect);
        const fmap = fileMap[pi];
        LineRow state;
        LineRow[] rows, kept;
        uint seqSect;
        void reset() { state = LineRow(0, 1, 0, 1, h.defaultIsStmt != 0, false); }
        reset();

        void emitSequence()
        {
            if (!seqSect)
            {
                if (rows.length > 1)
                    fail("line sequence without its address");
                rows.length = 0;
                rows.assumeSafeAppend();
                return;
            }
            const t = &p.sects[seqSect - 1];
            kept.length = 0;
            kept.assumeSafeAppend();
            foreach (ref row; rows)
            {
                const o = row.addr - t.addr;
                if (!row.endSeq && t.droppedAt(o))
                    continue;
                LineRow k = row;
                k.addr = outAddress(p, seqSect - 1, o);
                if (k.file >= fmap.length)
                    fail("bad line table file");
                k.file = fmap[k.file];
                kept ~= k;
            }
            rows.length = 0;
            rows.assumeSafeAppend();
            if (kept.length < 2)
                return;     // nothing but the end
            os.data.put8(0);
            os.data.put8(9);
            os.data.put8(DW_LNE_set_address);
            Reloc rel;
            rel.address = cast(uint)os.data.length;
            rel.symbolnum = t.out_ + 1;
            rel.length = 3;
            rel.encode(os.relocs);
            ++os.nreloc;
            os.data.put64(kept[0].addr);
            LineRow cur = LineRow(kept[0].addr, 1, 0, 1, h.defaultIsStmt != 0, false);
            foreach (ref row; kept)
            {
                if (row.file != cur.file)
                {
                    os.data.put8(DW_LNS_set_file);
                    os.data.putUleb(row.file);
                }
                if (row.column != cur.column)
                {
                    os.data.put8(DW_LNS_set_column);
                    os.data.putUleb(row.column);
                }
                if (row.isStmt != cur.isStmt)
                    os.data.put8(DW_LNS_negate_stmt);
                if (row.addr < cur.addr || (row.addr - cur.addr) % h.minInst)
                    fail("line rows out of order");
                const addrAdv = (row.addr - cur.addr) / h.minInst;
                if (row.endSeq)
                {
                    if (addrAdv)
                    {
                        os.data.put8(DW_LNS_advance_pc);
                        os.data.putUleb(addrAdv);
                    }
                    os.data.put8(0);
                    os.data.put8(1);
                    os.data.put8(DW_LNE_end_sequence);
                    break;
                }
                const lineAdv = row.line - cur.line;
                bool special;
                if (lineAdv >= h.lineBase && lineAdv < h.lineBase + h.lineRange)
                {
                    const opcode = (lineAdv - h.lineBase) + h.lineRange * addrAdv + h.opcodeBase;
                    if (opcode <= 255)
                    {
                        os.data.put8(cast(uint)opcode);
                        special = true;
                    }
                }
                if (!special)
                {
                    if (lineAdv)
                    {
                        os.data.put8(DW_LNS_advance_line);
                        os.data.putSleb(lineAdv);
                    }
                    if (addrAdv)
                    {
                        os.data.put8(DW_LNS_advance_pc);
                        os.data.putUleb(addrAdv);
                    }
                    os.data.put8(DW_LNS_copy);
                }
                cur = row;
            }
        }

        Reader pr = Reader(sect.data[0 .. h.end], h.programStart);
        while (pr.pos < h.end)
        {
            const op = pr.u8();
            if (op >= h.opcodeBase)
            {
                const adj = op - h.opcodeBase;
                state.addr += (adj / h.lineRange) * h.minInst;
                state.line += h.lineBase + adj % h.lineRange;
                rows ~= state;
                continue;
            }
            switch (op)
            {
                case 0:
                {
                    const len = pr.uleb();
                    const at = pr.pos;
                    if (!len)
                        fail("empty extended line opcode");
                    const sub = pr.u8();
                    if (sub == DW_LNE_end_sequence)
                    {
                        state.endSeq = true;
                        rows ~= state;
                        emitSequence();
                        reset();
                        seqSect = 0;
                    }
                    else if (sub == DW_LNE_set_address)
                    {
                        if (len != 9)
                            fail("address size");
                        const ri = findReloc(*sect, order, pr.pos);
                        if (ri == size_t.max || sect.relocs[ri].extern_)
                            fail("line address without section relocation");
                        const sn = sect.relocs[ri].symbolnum;
                        if (!sn || sn > p.sects.length)
                            fail("bad relocation section");
                        if (rows.length && sn != seqSect)
                            fail("line sequence across sections");
                        seqSect = sn;
                        state.addr = pr.u64();
                    }
                    else
                        fail("extended line opcode");
                    pr.pos = at + cast(size_t)len;
                    break;
                }
                case DW_LNS_copy:
                    rows ~= state;
                    break;
                case DW_LNS_advance_pc:
                    state.addr += pr.uleb() * h.minInst;
                    break;
                case DW_LNS_advance_line:
                    state.line += pr.sleb();
                    break;
                case DW_LNS_set_file:
                    state.file = cast(uint)pr.uleb();
                    break;
                case DW_LNS_set_column:
                    state.column = cast(uint)pr.uleb();
                    break;
                case DW_LNS_negate_stmt:
                    state.isStmt = !state.isStmt;
                    break;
                case DW_LNS_const_add_pc:
                    state.addr += ((255 - h.opcodeBase) / h.lineRange) * h.minInst;
                    break;
                case DW_LNS_fixed_advance_pc:
                    state.addr += pr.u16();
                    break;
                default:
                    fail("line opcode");
            }
        }
        if (rows.length)
            fail("line sequence without its end");
    }

    /// Copy a part's debug_loc: lists of address ranges with location expressions,
    /// each list ended by an entry of two zeros. The entries of removed code go.
    void copyLocs(ref Part p, size_t pi, int si, ref OutSect os)
    {
        auto sect = &p.sects[si];
        const start = os.data.length;
        if (!p.anyDropped)
        {
            os.data.put(sect.data);
            const(Reloc)* prev;
            foreach (ri, ref r; sect.relocs)
            {
                const pr = prev;
                prev = &r;
                const paired = pr && pr.address == r.address ? pr : null;
                // with nothing dropped from the part, no address is of a dropped atom
                Reloc t = translate(p, si, r, paired, os.data.buf.ptr + start + r.address, false);
                t.address = cast(uint)(start + r.address);
                t.encode(os.relocs);
                ++os.nreloc;
            }
            return;
        }
        auto map = &locMaps[pi];
        map.identity = false;
        auto order = sortedRelocs(*sect);
        size_t pos;
        while (pos < sect.data.length)
        {
            map.starts[pos] = os.data.length - start;
            pos = copyList(p, si, order, pos, os, true, true);
        }
    }

    /**
     * Copy a list of part `p`'s debug_loc (`loc`) or debug_ranges `si` to `os`.
     * Params:
     *  order = the section's relocations, sorted
     *  pos = the offset of the list in the section
     *  terminate = end the list copied with an entry of two zeros
     * Returns: the offset after the list
     */
    size_t copyList(ref Part p, int si, const size_t[] order, size_t pos, ref OutSect os, bool loc, bool terminate)
    {
        auto sect = &p.sects[si];
        Reader rd = Reader(sect.data, pos);
        while (true)
        {
            const entry = rd.pos;
            const b = rd.u64();
            const e = rd.u64();
            if (b == 0 && e == 0)
            {
                if (terminate)
                {
                    os.data.put64(0);
                    os.data.put64(0);
                }
                return rd.pos;
            }
            if (b == ulong.max)
                fail("base address selection entry");
            const(ubyte)[] expr;
            if (loc)
            {
                const n = rd.u16();
                rd.need(n);
                expr = sect.data[rd.pos .. rd.pos + n];
                rd.pos += n;
            }
            const rb = findReloc(*sect, order, entry);
            const re = findReloc(*sect, order, entry + 8);
            if (rb == size_t.max || re == size_t.max)
                fail("list entry without relocations");
            const relB = sect.relocs[rb], relE = sect.relocs[re];
            if (relB.extern_ || relE.extern_ || relB.symbolnum != relE.symbolnum ||
                !relB.symbolnum || relB.symbolnum > p.sects.length)
                fail("list entry relocations");
            const t = &p.sects[relB.symbolnum - 1];
            if (t.droppedAt(b - t.addr))
                continue;       // an entry of removed code
            const at = os.data.length;
            os.data.put64(b);
            os.data.put64(e);
            foreach (k, rel; [relB, relE])
            {
                Reloc tr = translate(p, si, rel, null, os.data.buf.ptr + at + 8 * k, k == 1);
                tr.address = cast(uint)(at + 8 * k);
                tr.encode(os.relocs);
                ++os.nreloc;
            }
            if (loc)
            {
                os.data.put16(cast(uint)expr.length);
                const exprAt = os.data.length;
                os.data.put(expr);
                // the relocations in the expression
                const exprStart = entry + 18;
                for (size_t i = findFirstReloc(*sect, order, exprStart); i < order.length; ++i)
                {
                    const rel = sect.relocs[order[i]];
                    if (rel.address >= exprStart + expr.length)
                        break;
                    const off = rel.address - exprStart;
                    Reloc tr = translate(p, si, rel, null, os.data.buf.ptr + exprAt + off, false);
                    tr.address = cast(uint)(exprAt + off);
                    tr.encode(os.relocs);
                    ++os.nreloc;
                }
            }
        }
    }

    /// The range list of the merged unit: the entries of the parts' units' lists
    void writeRanges(ref OutSect os)
    {
        combinedRanges = os.data.length;
        foreach (pi, ref p; parts)
        {
            const si = p.dwarfSect[Dwarf.ranges];
            if (si < 0 || !units[pi].present || cuRanges[pi] == ulong.max)
                continue;
            if (cuRanges[pi] >= p.sects[si].size)
                fail("bad range list offset");
            auto order = sortedRelocs(p.sects[si]);
            copyList(p, si, order, cast(size_t)cuRanges[pi], os, false, false);
        }
        os.data.put64(0);
        os.data.put64(0);
    }

    /// An attribute of a DIE being copied
    static struct Attr
    {
        uint at, form;
        size_t start, value, end;   // of the attribute, its value, and the end, in the part
    }

    /// The merged unit
    void writeInfo(ref OutSect os)
    {
        if (firstUnit < 0)
            return;
        os.data.put32(0);
        os.data.put16(units[firstUnit].version_);
        os.data.put32(0);       // the merged abbreviation table
        os.data.put8(8);
        static struct RefPatch { size_t at; ubyte size; size_t part; ulong target; bool sibling; }
        RefPatch[] refs;
        refs.reserve(1 << 16);
        Attr[] attrs;
        size_t maxAttrs;
        foreach (pi; 0 .. parts.length)
            foreach (ab; abbrevTable[pi])
                if (ab && ab.attrs.length > maxAttrs)
                    maxAttrs = ab.attrs.length;
        Attr[] attrBuf = new Attr[maxAttrs];
        foreach (pi, ref p; parts)
        {
            const u = &units[pi];
            if (!u.present)
                continue;
            const si = p.dwarfSect[Dwarf.info];
            const info = &p.sects[si];
            auto order = sortedRelocs(*info);
            dies[pi].reserve(info.data.length / 8);
            const table = abbrevTable[pi];
            const codes = codeMap[pi];
            size_t rc;      // the relocations before are of the DIEs copied
            Reader r = Reader(info.data[0 .. u.end], u.dies);
            int depth;
            int skipDepth = -1;     // the depth of the DIE whose subtree is skipped
            while (r.pos < u.end)
            {
                const dieStart = r.pos;
                const code = r.uleb();
                if (!code)
                {
                    --depth;
                    if (skipDepth >= 0)
                    {
                        if (depth == skipDepth)
                            skipDepth = -1;
                        continue;
                    }
                    // the end of the unit's children is written once, after all parts'
                    dies[pi] ~= DieAt(dieStart, os.data.length, true);
                    if (depth > 0)
                        os.data.put8(0);
                    continue;
                }
                const ab = code < table.length ? table[cast(size_t)code] : null;
                if (!ab)
                    fail("unknown abbreviation");
                attrs = attrBuf[0 .. ab.attrs.length];
                foreach (ai, ref af; ab.attrs)
                {
                    auto a = &attrs[ai];
                    a.at = af[0];
                    a.start = r.pos;
                    uint form = af[1];
                    while (form == DW_FORM_indirect)
                        form = cast(uint)r.uleb();
                    a.form = form;
                    a.value = r.pos;
                    skipForm(r, form, u.version_);
                    a.end = r.pos;
                }
                const isUnit = depth == 0;
                if (ab.children)
                    ++depth;
                if (skipDepth >= 0)
                    continue;
                if (isUnit ? pi != firstUnit : removesDie(p, *info, order, *ab, attrs))
                {
                    if (ab.children && !isUnit)
                        skipDepth = depth - 1;
                    continue;
                }
                dies[pi] ~= DieAt(dieStart, os.data.length);
                os.data.putUleb(codes[cast(size_t)code]);
                foreach (ref a; attrs)
                {
                    if (a.start != a.value)
                        os.data.put(info.data[a.start .. a.value]);     // the forms of indirect ones
                    const at = os.data.length;
                    ulong v;
                    ubyte size;
                    switch (a.form)
                    {
                        case DW_FORM_data1, DW_FORM_ref1: v = info.data[a.value]; size = 1; break;
                        case DW_FORM_data2, DW_FORM_ref2: v = rd16(info.data.ptr + a.value); size = 2; break;
                        case DW_FORM_data4, DW_FORM_ref4, DW_FORM_strp, DW_FORM_sec_offset:
                            v = rd32(info.data.ptr + a.value); size = 4; break;
                        case DW_FORM_data8, DW_FORM_ref8: v = rd64(info.data.ptr + a.value); size = 8; break;
                        case DW_FORM_ref_addr:
                            size = cast(ubyte)(a.end - a.value);
                            v = size == 8 ? rd64(info.data.ptr + a.value) : rd32(info.data.ptr + a.value);
                            break;
                        default: break;
                    }
                    bool patched = true;
                    const ptr = ptrClass(a.at, a.form, u.version_);
                    if (a.form == DW_FORM_ref1 || a.form == DW_FORM_ref2 || a.form == DW_FORM_ref4 || a.form == DW_FORM_ref8)
                        refs ~= RefPatch(at, size, pi, v, a.at == DW_AT_sibling);
                    else if (a.form == DW_FORM_ref_addr)
                    {
                        if (v < u.dies || v >= u.end)
                            fail("reference outside the unit");
                        refs ~= RefPatch(at, size, pi, v, a.at == DW_AT_sibling);
                    }
                    else if (a.form == DW_FORM_ref_udata)
                        fail("variable size reference");
                    else if (a.form == DW_FORM_strp)
                        v += dwarfBase[pi][Dwarf.str];
                    else if (ptr == Ptr.line)
                    {
                        if (!isUnit)
                            fail("line table reference of a DIE");
                        v = 0;
                    }
                    else if (ptr == Ptr.ranges)
                    {
                        if (!isUnit)
                            fail("range list of a DIE");
                        v = combinedRanges;
                    }
                    else if (ptr == Ptr.loc)
                        v = locMaps[pi].list(v) + dwarfBase[pi][Dwarf.loc];
                    else if ((a.at == DW_AT_decl_file || a.at == DW_AT_call_file) &&
                             (size || a.form == DW_FORM_udata))
                    {
                        if (a.form == DW_FORM_udata)
                        {
                            Reader fr = Reader(info.data, a.value);
                            v = fr.uleb();
                        }
                        if (v >= fileMap[pi].length)
                            fail("bad file number");
                        v = fileMap[pi][cast(size_t)v];
                        if (a.form == DW_FORM_udata)
                        {
                            os.data.putUleb(v);
                            continue;
                        }
                    }
                    else
                        patched = false;
                    if (patched)
                    {
                        if (size < 8 && v >> (8 * size))
                            fail("debug information value too large");
                        foreach (i; 0 .. size)
                            os.data.put8(cast(ubyte)(v >> (8 * i)));
                        continue;
                    }
                    os.data.put(info.data[a.value .. a.end]);
                    // the relocations of the value, of an address or in an expression
                    while (rc < order.length && info.relocs[order[rc]].address < a.value)
                        ++rc;
                    for (size_t i = rc; i < order.length; ++i)
                    {
                        const rel = info.relocs[order[i]];
                        if (rel.address >= a.end)
                            break;
                        const off = rel.address - a.value;
                        const end = a.at == DW_AT_high_pc && a.form == DW_FORM_addr;
                        Reloc tr = translate(p, si, rel, null, os.data.buf.ptr + at + off, end);
                        tr.address = cast(uint)(at + off);
                        tr.encode(os.relocs);
                        ++os.nreloc;
                    }
                }
            }
            if (depth != 0 || skipDepth >= 0)
                fail("unterminated DIE");
        }
        os.data.put8(0);
        wr32(os.data.buf.ptr, cast(uint)(os.data.length - 4));
        infoSize = os.data.length;
        foreach (ref rp; refs)
        {
            const t = newDie(rp.part, rp.target, rp.sibling);
            if (rp.size < 8 && t >> (8 * rp.size))
                fail("reference too large");
            foreach (i; 0 .. rp.size)
                os.data.buf[rp.at + i] = cast(ubyte)(t >> (8 * i));
        }
    }

    /// Returns: whether a DIE goes: the subprogram of a function removed
    bool removesDie(ref const Part p, ref const Sect info, const size_t[] order, ref const Abbrev ab, const Attr[] attrs)
    {
        if (ab.tag != DW_TAG_subprogram || !p.anyDropped)
            return false;
        foreach (ref a; attrs)
        {
            if (a.at != DW_AT_low_pc || a.form != DW_FORM_addr)
                continue;
            const ri = findReloc(info, order, a.value);
            if (ri == size_t.max || info.relocs[ri].extern_)
                return false;
            const rel = info.relocs[ri];
            if (!rel.symbolnum || rel.symbolnum > p.sects.length)
                fail("bad relocation section");
            const t = &p.sects[rel.symbolnum - 1];
            return t.droppedAt(rd64(info.data.ptr + a.value) - t.addr) !is null;
        }
        return false;
    }

    /// Returns: the offset in the merged debug_info of the DIE of part `pi` at `old`;
    /// for a `sibling` reference, of what follows the DIEs removed there
    ulong newDie(size_t pi, ulong old, bool sibling)
    {
        const d = dies[pi];
        size_t lo = 0, hi = d.length;
        while (lo < hi)
        {
            const mid = (lo + hi) / 2;
            if (d[mid].old < old)
                lo = mid + 1;
            else
                hi = mid;
        }
        if (lo == d.length || (!sibling && (d[lo].old != old || d[lo].isNull)))
            fail("reference to a removed DIE");
        return d[lo].new_;
    }

    /// Returns: the index in `order` of the first relocation at or after `address`
    static size_t findFirstReloc(ref const Sect s, const size_t[] order, ulong address)
    {
        size_t lo = 0, hi = order.length;
        while (lo < hi)
        {
            const mid = (lo + hi) / 2;
            if (s.relocs[order[mid]].address < address)
                lo = mid + 1;
            else
                hi = mid;
        }
        return lo;
    }

    /// The merged debug_aranges: one set for the merged unit, with the parts' ranges
    /// moved with the code they describe
    void writeAranges(ref OutSect os)
    {
        if (firstUnit < 0)
            return;
        os.data.put32(0);
        os.data.put16(2);
        os.data.put32(0);       // the merged unit
        os.data.put8(8);
        os.data.put8(0);
        os.data.zeros(4);       // to the first tuple, a multiple of twice the address size
        foreach (pi, ref p; parts)
        {
            const si = p.dwarfSect[Dwarf.aranges];
            if (si < 0)
                continue;
            auto sect = &p.sects[si];
            auto order = sortedRelocs(*sect);
            Reader rd = Reader(sect.data);
            while (rd.pos < sect.data.length)
            {
                const setStart = rd.pos;
                const len = rd.u32();
                const setEnd = rd.pos + len;
                if (len >= 0xFFFF_FFF0 || setEnd > sect.data.length)
                    fail("bad address range set");
                if (rd.u16() != 2)
                    fail("address range version");
                if (rd.u32() != 0 || !units[pi].present)
                    fail("address ranges of no unit");
                if (rd.u8() != 8 || rd.u8() != 0)
                    fail("address range sizes");
                rd.pos = setStart + 16;
                while (rd.pos + 16 <= setEnd)
                {
                    const tuple = rd.pos;
                    const a = rd.u64();
                    const n = rd.u64();
                    if (a == 0 && n == 0)
                        break;
                    const ri = findReloc(*sect, order, tuple);
                    if (ri == size_t.max || sect.relocs[ri].extern_)
                        fail("address range without section relocation");
                    const sn = sect.relocs[ri].symbolnum;
                    if (!sn || sn > p.sects.length)
                        fail("bad relocation section");
                    const t = &p.sects[sn - 1];
                    const o = a - t.addr;
                    const nb = outAddress(p, sn - 1, o);
                    const ne = outAddress(p, sn - 1, o + n);
                    if (ne == nb && n)
                        continue;
                    Reloc rel;
                    rel.address = cast(uint)os.data.length;
                    rel.symbolnum = t.out_ + 1;
                    rel.length = 3;
                    rel.encode(os.relocs);
                    ++os.nreloc;
                    os.data.put64(nb);
                    os.data.put64(ne - nb);
                }
                rd.pos = setEnd;
            }
        }
        os.data.put64(0);
        os.data.put64(0);
        wr32(os.data.buf.ptr, cast(uint)(os.data.length - 4));
    }

    /// The merged debug_pubnames or debug_pubtypes: one set for the merged unit, with
    /// the parts' entries but those of removed DIEs
    void writePubnames(Dwarf kind, ref OutSect os)
    {
        if (firstUnit < 0)
            return;
        os.data.put32(0);
        os.data.put16(2);
        os.data.put32(0);       // the merged unit
        os.data.put32(cast(uint)infoSize);
        foreach (pi, ref p; parts)
        {
            const si = p.dwarfSect[kind];
            if (si < 0)
                continue;
            auto sect = &p.sects[si];
            if (sect.relocs.length)
                fail("relocations in a name table");
            Reader rd = Reader(sect.data);
            while (rd.pos < sect.data.length)
            {
                const len = rd.u32();
                const setEnd = rd.pos + len;
                if (len >= 0xFFFF_FFF0 || setEnd > sect.data.length)
                    fail("bad name set");
                if (rd.u16() != 2)
                    fail("name table version");
                if (rd.u32() != 0 || !units[pi].present)
                    fail("names of no unit");
                rd.u32();       // debug_info_length
                while (rd.pos < setEnd)
                {
                    const off = rd.u32();
                    if (!off)
                        break;
                    const nameStart = rd.pos;
                    rd.cstring();
                    const d = dies[pi];
                    size_t lo = 0, hi = d.length;
                    while (lo < hi)
                    {
                        const mid = (lo + hi) / 2;
                        if (d[mid].old < off)
                            lo = mid + 1;
                        else
                            hi = mid;
                    }
                    if (lo == d.length || d[lo].old != off || d[lo].isNull)
                        continue;       // of a removed DIE
                    os.data.put32(cast(uint)d[lo].new_);
                    os.data.put(sect.data[nameStart .. rd.pos]);
                }
                rd.pos = setEnd;
            }
        }
        os.data.put32(0);
        wr32(os.data.buf.ptr, cast(uint)(os.data.length - 4));
    }

    // ------------------------------------------------------------------------
    // The object file

    void write()
    {
        // the symbol and string tables
        Buffer strtab;
        strtab.put8(0);
        uint str(const(char)[] s)
        {
            if (!s.length)
                return 0;
            const o = cast(uint)strtab.length;
            strtab.put(cast(const(ubyte)[])s);
            strtab.put8(0);
            return o;
        }
        Buffer symtab;
        void putSym(const(char)[] name, ubyte type, ubyte sect, ushort desc, ulong value)
        {
            symtab.put32(str(name));
            symtab.put8(type);
            symtab.put8(sect);
            symtab.put16(desc);
            symtab.put64(value);
        }
        void putDefined(ref const Part p, ref const Sym s)
        {
            if (s.kind == N_ABS)
            {
                putSym(s.name, s.type, 0, s.desc, s.value);
                return;
            }
            const t = &p.sects[s.sect - 1];
            putSym(s.name, s.type, cast(ubyte)(t.out_ + 1), s.desc, outAddress(p, s.sect - 1, s.value - t.addr));
        }
        foreach (ref p; parts)
            foreach (k, ref s; p.syms)
                if (!s.isExt && p.outSym[k] != uint.max)
                    putDefined(p, s);
        foreach (pi, ref p; parts)
            foreach (k, ref s; p.syms)
                if (s.isExt && s.kind != N_UNDF && !p.symDropped[k])
                    putDefined(p, s);
        {
            bool[] done = new bool[exts.length];
            foreach (ref p; parts)
                foreach (k, ref s; p.syms)
                {
                    if (!s.isExt || s.kind != N_UNDF)
                        continue;
                    const e = p.symExt[k];
                    auto x = &exts[e];
                    if (x.defPart >= 0 || done[e])
                        continue;
                    done[e] = true;
                    if (x.common)
                        putSym(x.name, N_UNDF | N_EXT, 0, cast(ushort)(x.commonAlign << 8), x.commonSize);
                    else
                    {
                        ushort desc = cast(ushort)(x.undefDesc & ~N_WEAK_REF);
                        if (!x.strongRef)
                            desc |= N_WEAK_REF;
                        putSym(x.name, N_UNDF | N_EXT, 0, desc, 0);
                    }
                }
        }
        const nsyms = nlocal + nextdef + nundef;
        assert(symtab.length == nsyms * 16);

        // the load commands
        const nsects = cast(uint)outs.length;
        const segSize = segment_command_64.sizeof + nsects * section_64.sizeof;
        const versionCmd = parts[0].versionCmd;
        const sizeofcmds = cast(uint)(segSize + versionCmd.length + symtab_command.sizeof + dysymtab_command.sizeof);
        const ncmds = versionCmd.length ? 4 : 3;

        Buffer f;
        f.reserve(1 << 20);
        f.put32(MH_MAGIC_64);
        f.put32(parts[0].cputype);
        f.put32(parts[0].cpusubtype);
        f.put32(MH_OBJECT);
        f.put32(ncmds);
        f.put32(sizeofcmds);
        f.put32(parts[0].flags);
        f.put32(0);
        const cmds = f.length;
        f.zeros(sizeofcmds);

        // the section contents
        f.alignTo(8);
        const fileoff = f.length;
        ulong[] offsets = new ulong[nsects];
        foreach (i, ref os; outs)
        {
            if (os.zerofill || !os.size)
                continue;
            f.alignTo(1UL << os.align_);
            offsets[i] = f.length;
            f.put(os.data[]);
        }
        const filesize = f.length - fileoff;
        ulong[] reloffs = new ulong[nsects];
        foreach (i, ref os; outs)
        {
            if (!os.nreloc)
                continue;
            f.alignTo(8);
            reloffs[i] = f.length;
            f.put(os.relocs[]);
        }
        f.alignTo(8);
        const symoff = f.length;
        f.put(symtab[]);
        const stroff = f.length;
        strtab.alignTo(8);
        f.put(strtab[]);

        // fill in the load commands
        Buffer c;
        ulong vmsize;
        foreach (ref os; outs)
            if (os.addr + os.size > vmsize)
                vmsize = os.addr + os.size;
        c.put32(LC_SEGMENT_64);
        c.put32(cast(uint)segSize);
        c.zeros(16);
        c.put64(0);
        c.put64(vmsize > filesize ? vmsize : filesize);
        c.put64(fileoff);
        c.put64(filesize);
        c.put32(7);
        c.put32(7);
        c.put32(nsects);
        c.put32(0);
        foreach (i, ref os; outs)
        {
            char[16] name = 0;
            name[0 .. os.sectname.length] = os.sectname[];
            c.put(cast(const(ubyte)[])name[]);
            name[] = 0;
            name[0 .. os.segname.length] = os.segname[];
            c.put(cast(const(ubyte)[])name[]);
            c.put64(os.addr);
            c.put64(os.size);
            c.put32(cast(uint)offsets[i]);
            c.put32(os.align_);
            c.put32(cast(uint)reloffs[i]);
            c.put32(os.nreloc);
            c.put32(os.flags);
            c.zeros(12);
        }
        c.put(versionCmd);
        c.put32(LC_SYMTAB);
        c.put32(symtab_command.sizeof);
        c.put32(cast(uint)symoff);
        c.put32(nsyms);
        c.put32(cast(uint)stroff);
        c.put32(cast(uint)strtab.length);
        c.put32(LC_DYSYMTAB);
        c.put32(dysymtab_command.sizeof);
        c.put32(0);
        c.put32(nlocal);
        c.put32(nlocal);
        c.put32(nextdef);
        c.put32(nlocal + nextdef);
        c.put32(nundef);
        c.zeros(dysymtab_command.sizeof - 32);
        assert(c.length == sizeofcmds);
        f.buf[cmds .. cmds + sizeofcmds] = c[];
        if (f.length > uint.max)
            fail("object file too large");
        output = f.buf[0 .. f.length];
    }
}
