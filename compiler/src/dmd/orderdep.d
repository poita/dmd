/**
 * Order independence of declarations (`-preview=orderIndependence`).
 *
 * `static if`, `static foreach`, `mixin` declarations and template mixins add
 * symbols to a scope while semantic analysis is already running. Without
 * further rules, a query answered before such an insertion observes a
 * different answer than the same query answered after it, so the meaning of
 * the program depends on the order in which the compiler evaluates declarations.
 *
 * With the preview enabled the compiler makes these results order independent:
 *
 * $(UL
 *   $(LI Forcing: when a lookup of `id` in scope `S` misses, or finds an
 *        overloadable symbol, every pending `static if` / `static foreach`
 *        of `S` that may declare `id` is expanded first, so a later
 *        declaration is never missed.)
 *   $(LI Cycles: if such a `static if` / `static foreach` is itself being
 *        expanded, the question cannot be answered and is an error, unless
 *        the lookup fails everywhere outside a speculative context (then it
 *        is an ordinary undefined identifier or a deferral).)
 *   $(LI Negative facts: a declaration that cannot be forced (string mixin,
 *        template mixin, import inside a `static if`) is checked when it is
 *        inserted: inserting a name whose absence was already observed, a new
 *        overload of an already resolved overload set, or a member into a
 *        scope whose members were already listed, is an error.)
 * )
 *
 * Copyright:   Copyright (C) 1999-2026 by The D Language Foundation, All Rights Reserved
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 */
module dmd.orderdep;

import dmd.astenums : STC;
import dmd.attrib;
import dmd.cond : Include;
import dmd.declaration;
import dmd.denum;
import dmd.dmodule;
import dmd.dscope;
import dmd.dsymbol;
import dmd.dtemplate;
import dmd.errors;
import dmd.func;
import dmd.globals;
import dmd.identifier;
import dmd.location;
import dmd.root.aav : AssocArray;
import dmd.root.array;
import dmd.arraytypes : Dsymbols;



private __gshared int suspended;    // > 0 while lookups must not be recorded (speller, UFCS)

/// Returns: true if order independence is enforced
bool orderCheck() @trusted
{
    return (global.params.orderIndependence || global.params.orderIndependenceLexical) && suspended == 0;
}

/// Returns: true if conditions only see the conditionals before them in their scope
private bool lexical() @trusted
{
    return global.params.orderIndependenceLexical;
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

    // the default hash runs MurmurHash over the bytes, too slow for a lookup on every miss
    size_t toHash() const @trusted pure nothrow @nogc
    {
        return (cast(size_t) sds >> 4) * 0x9E3779B97F4A7C15 ^ (cast(size_t) id >> 4);
    }

    bool opEquals(ref const Key k) const @safe pure nothrow @nogc
    {
        return sds is k.sds && id is k.id;
    }
}

struct Fact
{
    Loc loc;
    bool gagged;
    Cond* horizon;  // lexical mode: the condition that made the lookup, it does not see itself and later conditionals
    bool modules;   // imported modules were searched too, not just the local table
}

struct Seal
{
    Loc loc;
    bool[const(void)*] idents;
}

/// A `static if` / `static foreach` that may still add symbols to a scope
struct Pending
{
    AttribDeclaration d;
    Pending* next;
}

/// Position of a `static if` / `static foreach` in the source order of its scope:
/// the path of indices from the scope through enclosing conditionals
struct Cond
{
    Cond* parent;       // enclosing conditional, or the scope's root
    uint seq;           // index among the parent's conditionals
    uint nchildren;
}

/// A `static if` / `static foreach` being evaluated
struct Frame
{
    AttribDeclaration d;
    ScopeDsymbol s;     // owner of the table it adds to
    bool expanding;     // false while its condition / aggregate is evaluated
}

/// A lookup that hit a `static if` / `static foreach` being expanded
struct Cycle
{
    Loc loc;
    ScopeDsymbol s;
    Identifier id;
    AttribDeclaration d;
}

__gshared Fact[Key] absent;       // (scope, ident) looked up and not found locally
__gshared Fact[Key] overloads;    // (scope, ident) overload set resolved
__gshared Seal*[const(void)*] seals; // scope listed by allMembers/derivedMembers
__gshared bool[Key] reported;     // (scope, ident) already reported, any kind
__gshared Array!Key journal;      // absent facts in insertion order, for retraction (malloc based: the compiler's GC is off)
__gshared Pending*[Key] byName;   // (scope, ident) -> conditionals that may declare ident
__gshared Pending*[const(void)*] byScope; // scope -> all its conditionals
__gshared AssocArray!(void*, void*) growable; // scopes in `byScope`, as a pointer-keyed table: queried on every lookup miss
__gshared Array!Cycle cycles;     // cycles found by the lookups in progress
__gshared int searchDepth;        // nesting of `Scope.search` in the current forcing level
__gshared Array!Module inSearch;  // modules with `insearch` set by the current lookup
__gshared AssocArray!(void*, Cond*) conds; // conditional -> its position
__gshared AssocArray!(void*, Cond*) roots; // scope -> root of its positions
__gshared Array!Frame frames;     // conditionals being evaluated, innermost last

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

/// Build the name from identifiers only: toPrettyChars() on a template
/// instance prints its arguments, which can run semantic.
const(char)* scopeName(ScopeDsymbol s) @trusted
{
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
    return buf.extractChars();
}

const(char)* scopeKind(ScopeDsymbol s) @safe
{
    return s.isModule() ? "module" : s.isTemplateMixin() ? "mixin" :
        s.isTemplateInstance() ? "template instance" : s.kind();
}

/// Report errors even from speculative contexts: the speculative result is what changed
void ungagged(scope void delegate() dg) @trusted
{
    const gag = global.gag;
    global.gag = 0;
    dg();
    global.gag = gag;
}

enum Kind { absent, overload, sealed, import_ }

void report(Kind k, ScopeDsymbol s, Identifier id, Loc insertLoc, Loc factLoc, bool gagged) @trusted
{
    const(char)* spec = gagged ? " in a speculative context" : "";
    ungagged({
        final switch (k)
        {
        case Kind.absent:
            error(insertLoc, "declaration of `%s` changes the result of an earlier lookup", id.toChars());
            errorSupplemental(factLoc, "`%s` was looked up in %s `%s` here%s, and not found",
                id.toChars(), scopeKind(s), scopeName(s), spec);
            break;
        case Kind.overload:
            error(insertLoc, "overload of `%s` added after overload resolution", id.toChars());
            errorSupplemental(factLoc, "overloads of `%s` in %s `%s` were resolved here%s",
                id.toChars(), scopeKind(s), scopeName(s), spec);
            break;
        case Kind.sealed:
            error(insertLoc, "member `%s` added to %s `%s` after its members were listed",
                id.toChars(), scopeKind(s), scopeName(s));
            errorSupplemental(factLoc, "members were listed here");
            break;
        case Kind.import_:
            error(insertLoc, "`%s` made visible here changes the result of an earlier lookup", id.toChars());
            errorSupplemental(factLoc, "`%s` was looked up in %s `%s` here%s, and not found",
                id.toChars(), scopeKind(s), scopeName(s), spec);
            break;
        }
    });
}

void reportCycle(ref Cycle c) @trusted
{
    auto key = Key(cast(void*) c.s, cast(void*) c.id);
    if (key in reported)
        return;
    reported[key] = true;
    ungagged({
        error(c.loc, "cannot look up `%s` in %s `%s`: whether it exists depends on this lookup",
            c.id.toChars(), scopeKind(c.s), scopeName(c.s));
        errorSupplemental(c.d.loc, "`%s` may be declared by this `%s`, which is still being evaluated",
            c.id.toChars(), c.d.kind());
    });
}

bool isInternal(Identifier id) @trusted
{
    // compiler generated names, never listed by allMembers
    auto s = id.toString();
    return s.length >= 2 && s[0] == '_' && s[1] == '_';
}

/// Returns: true if `a` comes before `b` in the source order of their scope
bool before(const(Cond)* a, const(Cond)* b) @trusted
{
    uint[16] pa, pb;
    size_t na, nb;
    for (auto c = a; c.parent; c = c.parent)
        pa[na++ % pa.length] = c.seq;
    for (auto c = b; c.parent; c = c.parent)
        pb[nb++ % pb.length] = c.seq;
    if (na > pa.length || nb > pb.length)
        return false;   // too deep to tell, treat as not before
    foreach (i; 0 .. na < nb ? na : nb)
    {
        const x = pa[na - 1 - i], y = pb[nb - 1 - i];
        if (x != y)
            return x < y;
    }
    return na < nb;     // an enclosing conditional comes first
}

/***********************************
 * Lexical mode: the conditional of scope `s` whose condition is being
 * evaluated by the innermost frame, if the lookup comes straight from it.
 */
Cond* origin(ScopeDsymbol s) @trusted
{
    if (!lexical() || !frames.length)
        return null;
    auto f = &frames[frames.length - 1];
    if (f.expanding || f.s !is s)
        return null;
    return conds[cast(void*) f.d];
}

/// The conditional of scope `s` adding members right now, if any
Cond* inserter(ScopeDsymbol s) @trusted
{
    if (!frames.length)
        return null;
    auto f = &frames[frames.length - 1];
    if (!f.expanding || f.s !is s)
        return null;
    return conds[cast(void*) f.d];
}

/// `Foo!(...)` inside an instance of template `Foo` always refers to the
/// template, even after a member named `Foo` exists (findTempDecl), so a
/// member inserted later cannot change the answer.
bool isOwnTemplateName(ScopeDsymbol s, Identifier id) @trusted
{
    if (id !is templateName)
        return false;
    auto ti = s.isTemplateInstance();
    return ti && !ti.isTemplateMixin() && ti.tempdecl && ti.tempdecl.ident is id;
}

bool isPending(AttribDeclaration d) @trusted
{
    if (d.errors)
        return false;
    if (auto sif = d.isStaticIfDeclaration())
        return sif.condition.inc == Include.notComputed;
    if (d.dsym == DSYM.staticForeachDeclaration)
        return !(cast(StaticForeachDeclaration) d).cached;
    return false;
}

bool isOnStack(AttribDeclaration d) @trusted
{
    if (auto sif = d.isStaticIfDeclaration())
        return sif.onStack;
    return (cast(StaticForeachDeclaration) d).onStack;
}

size_t timesForced(ref Array!AttribDeclaration forced, AttribDeclaration d) @trusted
{
    size_t n;
    foreach (f; forced[])
        n += f is d;
    return n;
}

/// Expand `d`, outside of the lookup that triggered it
void force(AttribDeclaration d) @trusted
{
    import dmd.dsymbolsem : include;

    // The lookup in progress marks the modules it searches to stop import
    // cycles. Expanding `d` is a fresh lookup context: clear the marks.
    const depth = searchDepth;
    const mark = inSearch.length;
    foreach (m; inSearch[])
        m.insearch = false;
    searchDepth = 0;
    Scope* sc = d._scope;
    include(d, sc);
    foreach (m; inSearch[][0 .. mark])
        m.insearch = true;
    inSearch.setDim(mark);
    searchDepth = depth;
}

/// Calls `dg` with each identifier `ds` may declare in the enclosing scope
void collectIdents(Dsymbols* ds, scope void delegate(Identifier) dg) @trusted
{
    if (!ds)
        return;
    foreach (d; *ds)
    {
        if (!d)
            continue;
        if (auto ad = d.isAttribDeclaration())
        {
            // string mixins are not known yet, they are checked on insertion
            if (ad.isMixinDeclaration())
                continue;
            collectIdents(ad.decl, dg);
            if (ad.dsym == DSYM.conditionalDeclaration || ad.dsym == DSYM.staticIfDeclaration)
                collectIdents((cast(ConditionalDeclaration) ad).elsedecl, dg);
            continue;
        }
        if (auto ed = d.isEnumDeclaration())
        {
            if (ed.isAnonymous())
            {
                collectIdents(ed.members, dg);
                continue;
            }
        }
        if (d.ident && !d.isAnonymous() && !isInternal(d.ident))
            dg(d.ident);
    }
}

public:

/***********************************
 * Register a `static if` / `static foreach` added to scope `s`, so that
 * lookups in `s` can expand it before answering.
 */
void notePending(ScopeDsymbol s, AttribDeclaration d) @trusted
{
    s = owner(s);
    if (!tracked(s))
        return;
    auto sk = cast(void*) s;
    auto p = sk in byScope;
    byScope[sk] = new Pending(d, p ? *p : null);
    *growable.getLvalue(sk) = sk;

    Cond* parent = inserter(s);
    if (!parent)
    {
        auto r = roots.getLvalue(sk);
        if (!*r)
            *r = new Cond();
        parent = *r;
    }
    *conds.getLvalue(cast(void*) d) = new Cond(parent, parent.nchildren++);

    void add(Identifier id)
    {
        auto key = Key(sk, cast(void*) id);
        if (auto q = key in byName)
        {
            if ((*q).d is d)    // declared in both branches
                return;
            *q = new Pending(d, *q);
        }
        else
            byName[key] = new Pending(d, null);
    }
    collectIdents(d.decl, &add);
    if (auto sif = d.isStaticIfDeclaration())
        collectIdents(sif.elsedecl, &add);
}

/***********************************
 * Register scope `s` as one that can still receive declarations after
 * semantic analysis started (it holds a `mixin` or a template mixin).
 */
void noteGrowable(ScopeDsymbol s) @trusted
{
    s = owner(s);
    if (!tracked(s))
        return;
    auto sk = cast(void*) s;
    if (!(sk in byScope))
        byScope[sk] = null;
    *growable.getLvalue(sk) = sk;
}

/***********************************
 * Returns: true if declarations may still be added to `sds` after
 * semantic analysis started. Lookups in other scopes need no bookkeeping.
 */
bool mayGrow(ScopeDsymbol sds) @trusted
{
    return growable.length && growable[cast(void*) owner(sds)] !is null;
}

/***********************************
 * Expand the pending conditionals of `sds` that may declare `id`.
 * Returns: true if any was expanded, the caller should look again
 */
bool forcePending(ScopeDsymbol sds, Identifier id, Loc loc) @trusted
{
    if (sds.isForwardingScopeDsymbol())
        return false;
    auto s = owner(sds);
    if (isOwnTemplateName(s, id))
        return false;
    auto key = Key(cast(void*) s, cast(void*) id);
    auto from = origin(s);
    Array!AttribDeclaration forced;
    bool any;
    for (bool progress = true; progress; )
    {
        progress = false;
        auto p = key in byName;   // re-fetch: expansions register nested conditionals
        if (!p)
            break;
        Pending** link = p;
        for (Pending* e = *p; e; )
        {
            if (!isPending(e.d))
            {
                *link = e.next;     // done, unlink
                e = e.next;
                continue;
            }
            if (from)
            {
                auto c = conds[cast(void*) e.d];
                if (c is from || !before(c, from))
                {
                    // not visible to this condition
                    link = &e.next;
                    e = e.next;
                    continue;
                }
            }
            if (isOnStack(e.d))
            {
                // `id` depends on the result of this very lookup
                if (!(key in reported))
                {
                    auto c = Cycle(loc, s, id, e.d);
                    if (searchDepth == 0)
                        reportCycle(c);
                    else
                        cycles.push(c);
                }
            }
            else if (e.d._scope && timesForced(forced, e.d) < 2)
            {
                // A forced conditional can stay pending: a `static foreach`
                // whose aggregate is not ready, or a speculative condition
                // that hit an error (retried once, after the error was reported).
                forced.push(e.d);
                force(e.d);
                progress = any = true;
                break;      // the list may have changed
            }
            link = &e.next;
            e = e.next;
        }
    }
    return any;
}

/***********************************
 * Track modules marked `insearch` by the lookup in progress.
 */
void enterModuleSearch(Module m) @trusted { inSearch.push(m); }
/// ditto
void leaveModuleSearch() @trusted { inSearch.pop(); }

/***********************************
 * Bracket the evaluation of a `static if` / `static foreach`: its
 * condition first, then (`orderCheckExpanding`) the addition of its members.
 */
void orderCheckEnter(AttribDeclaration d, ScopeDsymbol scopesym) @trusted
{
    frames.push(Frame(d, owner(scopesym), false));
}

/***********************************
 * Lexical mode: start the semantic analysis of another declaration. A
 * lookup it makes does not come straight from the condition being
 * evaluated, and its result can be cached and seen from anywhere, so it
 * must see every conditional.
 * Returns: true if a frame was pushed, to pop with `orderCheckLeave`
 */
bool orderCheckBarrier() @trusted
{
    if (!frames.length || !lexical())
        return false;
    frames.push(Frame(null, null, false));
    return true;
}

/// ditto
void orderCheckExpanding() @trusted
{
    frames[frames.length - 1].expanding = true;
}

/// ditto
void orderCheckLeave() @trusted
{
    frames.pop();
}

/***********************************
 * Record that `id` was looked up in the local table of `s` and not found.
 */
void noteAbsent(ScopeDsymbol s, Identifier id, Loc loc, bool modules) @trusted
{
    s = owner(s);
    if (!tracked(s))
        return;
    if (isOwnTemplateName(s, id))
        return;
    auto key = Key(cast(void*) s, cast(void*) id);
    bool added;
    auto f = &absent.require(key, { added = true; return Fact(loc, global.gag != 0, origin(s)); }());
    f.modules |= modules;
    if (added)
        journal.push(key);
}

/// State of the recording at the start of an unqualified lookup
struct SearchMark
{
    size_t absent, cycles;
}

/***********************************
 * Bracket an unqualified lookup (`Scope.search`).
 * A lookup that fails everywhere outside a speculative context is either an
 * error or makes the compiler defer and retry the declaration (e.g. a
 * forward reference to a `mixin`). It is "not yet known", not a negative
 * answer the program depends on: its facts and cycles are dropped.
 */
SearchMark orderCheckBegin() @trusted
{
    ++searchDepth;
    return SearchMark(journal.length, cycles.length);
}

/// ditto
void orderCheckEnd(SearchMark mark, bool found) @trusted
{
    --searchDepth;
    const keepAll = found || global.gag;
    if (cycles.length > mark.cycles)
    {
        if (keepAll)
            foreach (ref c; cycles[][mark.cycles .. $])
                reportCycle(c);
        cycles.setDim(mark.cycles);
    }
    if (keepAll)
        return;
    size_t keep = mark.absent;
    foreach (key; journal[][mark.absent .. $])
    {
        auto f = key in absent;
        if (f && f.gagged)     // made by a nested speculative lookup, still a fact
        {
            journal[keep++] = key;
            continue;
        }
        absent.remove(key);
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
    // the compiler itself probed for a user-defined one
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
    auto key = Key(cast(void*) s, cast(void*) sym.ident);
    if (key in reported)
        return;
    if (auto f = key in absent)
    {
        // lexical mode: the lookup was not meant to see this conditional
        if (f.horizon)
            if (auto c = inserter(s))
                if (c is f.horizon || !before(c, f.horizon))
                    goto Lnotabsent;
        reported[key] = true;
        return report(Kind.absent, s, sym.ident, sym.loc, f.loc, f.gagged);
    }
Lnotabsent:
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
                    return report(Kind.import_, ps, sym.ident, tm.loc, f.loc, f.gagged);
                }
        }
    }
    if (auto seal = cast(void*) s in seals)
    {
        if (!(cast(void*) sym.ident in (*seal).idents))
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
    if (!tracked(s) || !absent.length)
        return;
    auto sds = imported.isScopeDsymbol();
    if (!sds || !sds.symtab)
        return;
    // Walk the (usually small) table of the imported scope rather than all absent facts
    foreach (kv; sds.symtab.tab.asRange)
    {
        auto key = Key(cast(void*) s, cast(void*) kv.key);
        if (key in reported)
            continue;
        if (auto f = key in absent)
        {
            // a module import cannot hide a local symbol
            if (!f.modules && imported.isModule())
                continue;
            reported[key] = true;
            report(Kind.import_, s, cast(Identifier) kv.key, loc, f.loc, f.gagged);
        }
    }
}
