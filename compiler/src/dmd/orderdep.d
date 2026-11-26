/**
 * Prototype instrumentation that detects order-dependent semantics.
 *
 * D lets `static if`, `static foreach`, `mixin` declarations and template
 * mixins add symbols to a scope lazily, while semantic analysis is already
 * running. A query answered before such an insertion can then observe a
 * different answer than a query answered after it, so the meaning of the
 * program depends on the order in which the compiler happens to evaluate
 * declarations.
 *
 * This module records the facts that such an insertion could invalidate and
 * checks every insertion against them:
 *
 * $(UL
 *   $(LI `absent`: a lookup of `id` failed in the local symbol table of scope
 *        `S`, and `id` is later inserted into `S`.)
 *   $(LI `overload`: overload resolution ran on `id` in `S`, and a new
 *        overload of `id` is later inserted into `S`.)
 *   $(LI `sealed`: `__traits(allMembers/derivedMembers)` listed `S`, and a
 *        new member is later inserted into `S`.)
 *   $(LI `import`: a lookup of `id` failed in `S`, and `S` later imports a
 *        module or mixes in a template that declares `id`.)
 *   $(LI `fwdref`: a speculative (gagged) lookup inside an aggregate failed
 *        only because the aggregate's members were not determined yet. This
 *        is the "not yet known" case: the gagged result is order dependent
 *        even though no insertion is observed.)
 * )
 *
 * Facts are recorded at compiler primitives (scope lookup, overload
 * resolution, member listing), never inside CTFE, so arbitrary compile-time
 * code is covered as long as it reaches scopes through those primitives.
 *
 * Lookups whose answer a later insertion cannot change are not recorded:
 * $(UL
 *   $(LI an unqualified, non-speculative lookup that fails everywhere: it is an
 *        error or the compiler defers and retries ("not yet known"), see `orderCheckRetract`)
 *   $(LI UFCS probes of non-module scopes: UFCS only considers module-level symbols)
 *   $(LI `Foo!(...)` inside an instance of `Foo`: always resolves to the template)
 *   $(LI the lookup of a template mixin's own name, against that mixin's members)
 *   $(LI compiler generated members (`opAssign`, `__xdtor`, ...) and `static foreach` variables)
 * )
 *
 * Enabled by setting the environment variable `DMD_ORDERCHECK` (any value).
 * Diagnostics are written to stderr as single `ORDERDEP` lines, they never
 * change compilation results.
 *
 * Copyright:   Copyright (C) 1999-2026 by The D Language Foundation, All Rights Reserved
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 */
module dmd.orderdep;

import core.stdc.stdio;
import core.stdc.stdlib : getenv, atexit;

import dmd.dmodule;
import dmd.astenums : STC;
import dmd.declaration;
import dmd.dsymbol;
import dmd.dtemplate;
import dmd.func;
import dmd.globals;
import dmd.identifier;
import dmd.location;
import dmd.root.array;

nothrow:

private __gshared int state = -1;   // -1 unknown, 0 off, 1 on
private __gshared int suspended;    // > 0 while lookups must not be recorded (speller)

/// Returns: true if order-dependence checking is enabled
bool orderCheck() @trusted
{
    if (state < 0)
        init();
    return state > 0 && suspended == 0;
}

/// Suspend / resume recording, e.g. during spelling correction
void orderCheckSuspend() @trusted { ++suspended; }
/// ditto
void orderCheckResume() @trusted { --suspended; }

private __gshared Identifier templateName; // set while resolving `templateName!(...)`

/// Mark the start (id) / end (null) of the lookup of a template instance's template name
void orderCheckTemplateName(Identifier id) @trusted { templateName = id; }

private:

struct Key
{
    const(void)* sds;
    const(void)* id;
}

struct Fact
{
    Loc loc;
    bool gagged;
}

struct Seal
{
    Loc loc;
    bool[const(void)*] idents;
}

__gshared Fact[Key] absent;       // (scope, ident) looked up and not found locally
__gshared Fact[Key] overloads;    // (scope, ident) overload set resolved
__gshared Seal*[const(void)*] seals; // scope listed by allMembers/derivedMembers
__gshared bool[Key] reported;     // (scope, ident) already reported, any kind
__gshared Array!Key journal;      // absent facts in insertion order, for retraction (malloc based: the compiler's GC is off)

// statistics
__gshared size_t nAbsent, nRetracted, nOverloads, nSeals, nInserts, nImports;
__gshared size_t[5] nViolations;

enum Kind { absent, overload, sealed, import_, fwdref }
immutable string[5] kindNames = ["absent", "overload", "sealed", "import", "fwdref"];

void init() @trusted
{
    state = getenv("DMD_ORDERCHECK") !is null ? 1 : 0;
    if (state)
        atexit(&summary);
}

extern (C) void summary() @trusted
{
    if (!getenv("DMD_ORDERCHECK_STATS"))
        return;
    fprintf(stderr, "ORDERDEP-STATS absent-facts=%zu retracted=%zu overload-facts=%zu seals=%zu inserts-checked=%zu imports-checked=%zu" ~
        " absent=%zu overload=%zu sealed=%zu import=%zu fwdref=%zu\n",
        nAbsent, nRetracted, nOverloads, nSeals, nInserts, nImports,
        nViolations[0], nViolations[1], nViolations[2], nViolations[3], nViolations[4]);
}

/// Resolve forwarding scopes (`static foreach` bodies) to the scope that owns the table
ScopeDsymbol owner(ScopeDsymbol s) @safe
{
    while (s)
    {
        auto f = s.isForwardingScopeDsymbol();
        if (!f)
            break;
        s = f.parent ? f.parent.isScopeDsymbol() : null;
    }
    return s;
}

/// Scopes whose member set is meant to be order independent
bool tracked(ScopeDsymbol s) @safe
{
    if (!s)
        return false;
    if (s.isModule())
        return true;
    if (s.isPackage())          // packages grow as modules get imported
        return false;
    return s.isAggregateDeclaration() || s.isTemplateInstance() || s.isTemplateMixin() || s.isNspace();
}

const(char)* str(Loc loc) @trusted
{
    if (!loc.isValid())
        return "<internal>";
    return loc.toChars();
}

void report(Kind k, ScopeDsymbol s, Identifier id, Loc insertLoc, Loc factLoc, bool gagged) @trusted
{
    nViolations[k]++;
    // Build the name from identifiers only: toPrettyChars() on a template
    // instance prints its arguments, which can run semantic and change the result.
    import dmd.common.outbuffer;
    OutBuffer buf;
    void name(Dsymbol d)
    {
        if (!d)
            return;
        if (d.parent)
        {
            name(d.parent);
            buf.writeByte('.');
        }
        auto ti = d.isTemplateInstance();
        if (ti && !d.isTemplateMixin())
        {
            buf.writestring(ti.name ? ti.name.toChars() : "?");
            buf.writestring("!(...)");
        }
        else
            buf.writestring(d.ident ? d.ident.toChars() : "?");
    }
    name(s);
    const(char)* sname = buf.peekChars();
    const(char)* skind = s.isModule() ? "module" : s.isTemplateMixin() ? "mixin" :
        s.isTemplateInstance() ? "template instance" : s.isClassDeclaration() ? "class" :
        s.isAggregateDeclaration() ? "struct/union" : "scope";
    fprintf(stderr, "ORDERDEP %s %s `%s` in %s `%s` | observed %s%s\n",
        kindNames[k].ptr, str(insertLoc), id ? id.toChars() : "?", skind, sname,
        str(factLoc), gagged ? " (speculative)".ptr : "".ptr);
}

bool isInternal(Identifier id) @trusted
{
    // compiler generated names, never listed by allMembers
    auto s = id.toString();
    return s.length >= 2 && s[0] == '_' && s[1] == '_';
}

public:

/***********************************
 * Record that `id` was looked up in the local table of `s` and not found.
 */
void noteAbsent(ScopeDsymbol s, Identifier id, Loc loc) @trusted
{
    s = owner(s);
    if (!tracked(s))
        return;
    // `Foo!(...)` inside an instance of template `Foo` always refers to the
    // template, even after a member named `Foo` exists (findTempDecl), so a
    // member inserted later cannot change the answer.
    if (id is templateName)
        if (auto ti = s.isTemplateInstance())
            if (!ti.isTemplateMixin() && ti.tempdecl && ti.tempdecl.ident is id)
                return;
    auto key = Key(cast(void*) s, cast(void*) id);
    if (key in absent)
        return;
    absent[key] = Fact(loc, global.gag != 0);
    journal.push(key);
    nAbsent++;
}

/***********************************
 * Absent facts are journaled so that an unqualified lookup can retract the
 * facts it produced: a lookup that fails everywhere outside a speculative
 * context is either an error or makes the compiler defer and retry the
 * declaration (e.g. a forward reference to a `mixin`). It is "not yet
 * known", not a negative answer the program depends on.
 * Returns: a mark to pass to `orderCheckRetract`
 */
size_t orderCheckMark() @trusted
{
    return journal.length;
}

/// ditto
void orderCheckRetract(size_t mark) @trusted
{
    size_t keep = mark;
    foreach (key; journal[][mark .. $])
    {
        auto f = key in absent;
        if (f && f.gagged)     // made by a nested speculative lookup, still a fact
        {
            journal[keep++] = key;
            continue;
        }
        absent.remove(key);
        nAbsent--;
        nRetracted++;
    }
    journal.setDim(keep);
}

/***********************************
 * Record that the overload set `os` (or the single symbol) was resolved.
 */
void noteOverloadUse(Dsymbol sym, Loc loc) @trusted
{
    if (!sym || !sym.ident)
        return;
    if (auto os = sym.isOverloadSet())
    {
        foreach (a; os.a)
            noteOverloadUse(a, loc);
        return;
    }
    auto p = sym.parent ? owner(sym.parent.isScopeDsymbol()) : null;
    if (!tracked(p))
        return;
    auto key = Key(cast(void*) p, cast(void*) sym.ident);
    if (key in overloads)
        return;
    overloads[key] = Fact(loc, global.gag != 0);
    nOverloads++;
}

/***********************************
 * Record that the members of `s` were listed.
 */
void noteSeal(ScopeDsymbol s, Identifier[] ids, Loc loc) @trusted
{
    s = owner(s);
    if (!tracked(s))
        return;
    if (cast(void*) s in seals)
        return;
    auto seal = new Seal(loc);
    foreach (id; ids)
        seal.idents[cast(void*) id] = true;
    seals[cast(void*) s] = seal;
    nSeals++;
}

/***********************************
 * Record a speculative lookup failing because aggregate `s` is still incomplete.
 */
void noteForwardRef(ScopeDsymbol s, Identifier id, Loc loc) @trusted
{
    if (!global.gag)
        return;         // a real error, compilation fails anyway
    s = owner(s);
    if (!tracked(s))
        return;
    auto key = Key(cast(void*) s, cast(void*) id);
    if (key in reported)
        return;
    reported[key] = true;
    report(Kind.fwdref, s, id, loc, loc, true);
}

/***********************************
 * Check the insertion of `sym` into the table of `s`.
 * Params:
 *  s = scope receiving the symbol
 *  sym = inserted symbol
 *  overload = true if `sym` joined an existing overload set
 */
void checkInsert(ScopeDsymbol s, Dsymbol sym, bool overload) @trusted
{
    if (!sym || !sym.ident)
        return;
    // compiler generated members (opAssign, __xdtor, ...) are inserted after
    // the compiler itself probed for a user-defined one, that is not a user-visible order dependence
    if (auto fd = sym.isFuncDeclaration())
        if (fd.isGenerated)
            return;
    if (isInternal(sym.ident))
        return;
    // `static foreach` loop variables live in the forwarding scope's own table
    if (auto d = sym.isDeclaration())
        if (d.storage_class & STC.local)
            return;
    s = owner(s);
    if (!tracked(s))
        return;
    nInserts++;
    auto key = Key(cast(void*) s, cast(void*) sym.ident);
    if (key in reported)
        return;
    if (auto f = key in absent)
    {
        reported[key] = true;
        return report(Kind.absent, s, sym.ident, sym.loc, f.loc, f.gagged);
    }
    if (overload)
    {
        if (auto f = key in overloads)
        {
            reported[key] = true;
            return report(Kind.overload, s, sym.ident, sym.loc, f.loc, f.gagged);
        }
    }
    // members of a template mixin are visible in the scope it is mixed into
    if (auto tm = s.isTemplateMixin())
    {
        auto ps = tm.parent ? owner(tm.parent.isScopeDsymbol()) : null;
        if (tracked(ps))
        {
            auto pkey = Key(cast(void*) ps, cast(void*) sym.ident);
            if (!(pkey in reported))
                if (auto f = pkey in absent)
                // the lookup of the mixin's own template name precedes its expansion by definition
                if (f.loc != tm.loc)
                {
                    reported[pkey] = true;
                    return report(Kind.import_, ps, sym.ident, sym.loc, f.loc, f.gagged);
                }
        }
    }
    if (auto seal = cast(void*) s in seals)
    {
        if (!isInternal(sym.ident) && !(cast(void*) sym.ident in (*seal).idents))
        {
            reported[key] = true;
            return report(Kind.sealed, s, sym.ident, sym.loc, (*seal).loc, false);
        }
    }
}

/***********************************
 * Returns: true if `imported` is already visible through `s`'s imported scopes
 */
bool isImported(ScopeDsymbol s, Dsymbol imported) @trusted
{
    s = owner(s);
    if (!s || !s.importedScopes)
        return false;
    foreach (ss; *s.importedScopes)
        if (ss == imported)
            return true;
    return false;
}

/***********************************
 * Check `imported` (a module or template mixin) newly made visible in `s`
 * against the names already found absent in `s`.
 */
void checkImport(ScopeDsymbol s, Dsymbol imported, Loc loc) @trusted
{
    s = owner(s);
    if (!tracked(s))
        return;
    auto sds = imported.isScopeDsymbol();
    if (!sds || !sds.symtab)
        return;
    nImports++;
    if (!absent.length)
        return;
    // Walk the (usually small) table of the imported scope rather than all absent facts
    foreach (kv; sds.symtab.tab.asRange)
    {
        auto key = Key(cast(void*) s, cast(void*) kv.key);
        if (key in reported)
            continue;
        if (auto f = key in absent)
        {
            reported[key] = true;
            Loc l = kv.value.loc.isValid() ? kv.value.loc : loc;
            report(Kind.import_, s, cast(Identifier) kv.key, l, f.loc, f.gagged);
        }
    }
}
