/**
 * Global optimizer main loop
 *
 * Compiler implementation of the
 * $(LINK2 https://www.dlang.org, D programming language).
 *
 * Copyright:   Copyright (C) 1986-1998 by Symantec
 *              Copyright (C) 2000-2026 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 https://www.digitalmars.com, Walter Bright)
 * License:     Distributed under the Boost Software License, Version 1.0.
 *              https://www.boost.org/LICENSE_1_0.txt
 * Source:      https://github.com/dlang/dmd/blob/master/src/dmd/backend/go.d
 */

module dmd.backend.go;

import core.stdc.stdio;
import core.stdc.stdlib;
import core.stdc.string;

import dmd.backend.barray;
import dmd.backend.cc;
import dmd.backend.cdef;
import dmd.backend.dvec;
import dmd.backend.oper;
import dmd.backend.el;
import dmd.backend.symbol;
import dmd.backend.ty;
import dmd.backend.type;

import dmd.backend.backconfig : debugb, debugc, debuge, debugf;
import dmd.backend.blockopt : BlockOpt, bo;
import dmd.backend.blockopt : bc_goal, block_optimizer_free, blockopt, duplicateTests;
import dmd.backend.cg : localgot;
import dmd.backend.cgelem : combineByteLoads, doptelem, postoptelem;
import dmd.backend.debugprint : WRfunc;
import dmd.backend.dout : out_regcand;
import dmd.backend.util2 : binary;
import dmd.backend.inliner;
import dmd.backend.grange : rangeopt;

public import dmd.backend.gdag : builddags, boolopt;
public import dmd.backend.gflow : flowrd, flowlv, flowvbe, flowcp, flowae, genkillae, numberae;
public import dmd.backend.glocal : localize;
public import dmd.backend.gloop : blockinit, compdom, loopopt, loopConstants, updaterd;
public import dmd.backend.gother : constprop, copyprop, rmdeadass, elimass, deadvar, verybusyexp, listrds;
public import dmd.backend.gsroa : sliceStructs, sliceFloatStructs;

nothrow:
@safe:

/***************************************
 * Bit masks for various optimizations.
 */

alias mftype = uint;        /* a type big enough for all the flags  */
enum
{
    MFdc    = 1,               // dead code
    MFda    = 2,               // dead assignments
    MFdv    = 4,               // dead variables
    MFreg   = 8,               // register variables
    MFcse   = 0x10,            // global common subexpressions
    MFvbe   = 0x20,            // very busy expressions
    MFtime  = 0x40,            // favor time (speed) over space
    MFli    = 0x80,            // loop invariants
    MFliv   = 0x100,           // loop induction variables
    MFcp    = 0x200,           // copy propagation
    MFcnp   = 0x400,           // constant propagation
    MFloop  = 0x800,           // loop till no more changes
    MFtree  = 0x1000,          // optelem (tree optimization)
    MFlocal = 0x2000,          // localize expressions
    MFall   = 0xFFFF,          // do everything
}

enum Aetype { cse, arraybounds }

/**********************************
 * Definition elem vector, used for reaching definitions.
 */

struct DefNode
{
    elem    *DNelem;        // pointer to definition elem
    block   *DNblock;       // pointer to block that the elem is in
    /* For an assignment to a variable: the variable and the bytes of it
     * assigned, as they were when go.defnod[] was filled in
     */
    const(Symbol)* DNsym;
    targ_size_t DNoff, DNtop;
}

// which kind of flow analysisis being done
enum
{
    AE = 1,
    CP,
    VBE
}

/* Global Optimizer variables
 */
struct GlobalOptimizer
{
    bool AArch64;       // AArch64 is the target
    mftype mfoptim;
    Aetype aetype;      // cse, arraybounds
    uint changes;       // # of optimizations performed
    uint unswitched;    // # of loops unswitched in the function
    int flowxx;         // AE, CP or VBE

    Barray!DefNode defnod;    // array of definition elems
    uint unambigtop;    // number of unambiguous defininitions ( <= deftop )


    Barray!(elem*) expnod;      // array of expression elems
    uint exptop;        // top of expnod[]
    Barray!(block*) expblk;     // parallel array of block pointers

    vec_t defkill;      // vector of AEs killed by an ambiguous definition
    vec_t starkill;     // vector of AEs killed by a definition of something that somebody could be
                        // pointing to
    vec_t vptrkill;     // vector of AEs killed by an access
}

__gshared GlobalOptimizer go;




nothrow:
@safe:

__gshared bool OPTIMIZER = false;             // indicate we're in the optimizer


@trusted
void go_term(ref GlobalOptimizer go)
{
    vec_free(go.defkill);
    vec_free(go.starkill);
    vec_free(go.vptrkill);
    go.defnod.dtor();
    go.expnod.dtor();
    go.expblk.dtor();
}

debug
{
                        // to print progress message and current trees set to
                        // DEBUG_TREES to 1 and uncomment next 2 lines
//debug = DEBUG_TREES;
debug (DEBUG_TREES)
    void dbg_optprint(const(char) *);
else
    @trusted
    void dbg_optprint(const(char) *c)
    {
        // to print progress message, undo comment
        // printf(c);
    }
}
else
{
    void dbg_optprint(const(char) *c) { }
}

/**************************************
 * Parse optimizer command line flag.
 * Input:
 *      cp      flag string
 * Returns:
 *      0       not recognized
 *      !=0     recognized
 */
@trusted
int go_flag(ref GlobalOptimizer go, char* cp)
{
    enum GL     // indices of various flags in flagtab[]
    {
        O,all,cnp,cp,cse,da,dc,dv,li,liv,local,loop,
        none,o,reg,space,speed,time,tree,vbe,MAX
    }
    static immutable char*[GL.MAX] flagtab =
    [   "O","all","cnp","cp","cse","da","dc","dv","li","liv","local","loop",
        "none","o","reg","space","speed","time","tree","vbe"
    ];
    static immutable mftype[GL.MAX] flagmftab =
    [   0,MFall,MFcnp,MFcp,MFcse,MFda,MFdc,MFdv,MFli,MFliv,MFlocal,MFloop,
        0,0,MFreg,0,MFtime,MFtime,MFtree,MFvbe
    ];

    //printf("go_flag('%s')\n", cp);
    uint flag = binary(cp + 1,cast(const(char)**)flagtab.ptr,GL.MAX);
    if (go.mfoptim == 0 && flag != -1)
        go.mfoptim = MFall & ~MFvbe;

    if (*cp == '-')                     /* a regular -whatever flag     */
    {                                   /* cp -> flag string            */
        switch (flag)
        {
            case GL.all:
            case GL.cnp:
            case GL.cp:
            case GL.dc:
            case GL.da:
            case GL.dv:
            case GL.cse:
            case GL.li:
            case GL.liv:
            case GL.local:
            case GL.loop:
            case GL.reg:
            case GL.speed:
            case GL.time:
            case GL.tree:
            case GL.vbe:
                go.mfoptim &= ~flagmftab[flag];    /* clear bits   */
                break;
            case GL.o:
            case GL.O:
            case GL.none:
                go.mfoptim |= MFall & ~MFvbe;      // inverse of -all
                break;
            case GL.space:
                go.mfoptim |= MFtime;      /* inverse of -time     */
                break;
            case -1:                    /* not in flagtab[]     */
                goto badflag;
            default:
                assert(0);
        }
    }
    else if (*cp == '+')                /* a regular +whatever flag     */
    {                           /* cp -> flag string            */
        switch (flag)
        {
            case GL.all:
            case GL.cnp:
            case GL.cp:
            case GL.dc:
            case GL.da:
            case GL.dv:
            case GL.cse:
            case GL.li:
            case GL.liv:
            case GL.local:
            case GL.loop:
            case GL.reg:
            case GL.speed:
            case GL.time:
            case GL.tree:
            case GL.vbe:
                go.mfoptim |= flagmftab[flag];     /* set bits     */
                break;
            case GL.none:
                go.mfoptim &= ~MFall;      /* inverse of +all      */
                break;
            case GL.space:
                go.mfoptim &= ~MFtime;     /* inverse of +time     */
                break;
            case -1:                    /* not in flagtab[]     */
                goto badflag;
            default:
                assert(0);
        }
    }
    if (go.mfoptim)
    {
        go.mfoptim |= MFtree | MFdc;       // always do at least this much
        config.flags4 |= (go.mfoptim & MFtime) ? CFG4speed : CFG4space;
    }
    else
    {
        config.flags4 &= ~CFG4optimized;
    }
    return 1;                   // recognized

badflag:
    return 0;
}

debug (DEBUG_TREES)
{
void dbg_optprint(char* title)
{
    block* b;
    for (b = startblock; b; b = b.Bnext)
        if (b.Belem)
        {
            printf("%s\n",title);
            elem_print(b.Belem);
        }
}
}

/* A local aggregate whose every assignment copies all of the same read-only data, as
 * a struct's .init, and whose address is never taken, is read from that data instead,
 * and the copies are dropped, so it needs no place of its own: a large one copied from
 * .init to be read costs no stack
 */
@trusted
private void forwardReadonlyCopies(ref BlockOpt bo)
{
    Barray!(Symbol*) source;    // for each local, the data all its copies are of
    Barray!bool excluded;       // for each local, whether it is written otherwise
    scope (exit)
    {
        source.dtor();
        excluded.dtor();
    }
    source.setLength(globsym.length);
    excluded.setLength(globsym.length);
    source[][] = null;
    excluded[][] = false;

    static bool isLocal(const Symbol* s)
    {
        return (s.Sclass == SC.auto_ || s.Sclass == SC.register) && !(s.ty() & (mTYvolatile | mTYshared)) &&
               tyaggregate(s.ty());
    }

    // the read-only data e copies to all of local s, or null
    static Symbol* copyOfReadonly(const(elem)* e, const Symbol* s)
    {
        if (e.Eoper != OPstreq || e.Ecount || e.E1.Eoper != OPvar || e.E1.Voffset != 0)
            return null;
        const(elem)* e2 = e.E2;
        if (e2.Eoper != OPind || e2.E1.Eoper != OPrelconst || e2.E1.Voffset != 0 ||
            !(e2.E1.Vsym.Sflags & SFLreadonly) || !e.ET || type_size(e.ET) != type_size(s.Stype))
            return null;
        return cast(Symbol*)e2.E1.Vsym;
    }

    // the address of a local in e, which is it or it plus an index, or null
    static elem* addressPart(elem* e)
    {
        if (e.Eoper == OPadd)
            e = e.E1.Eoper == OPrelconst ? e.E1 : e.E2;
        if (e.Eoper != OPrelconst)
            return null;
        Symbol* s = e.Vsym;
        return s.Ssymnum < globsym.length && globsym[s.Ssymnum] is s ? e : null;
    }
    // the index added to the address of a local in e, or null
    static elem* indexPart(elem* e)
    {
        if (e.Eoper != OPadd)
            return null;
        return e.E1.Eoper == OPrelconst ? e.E2 : e.E1;
    }
    static Symbol* localAddress(elem* e)
    {
        elem* a = addressPart(e);
        return a ? a.Vsym : null;
    }

    bool any;
    void gather(elem* e)
    {
        while (1)
        {
            if (OTassign(e.Eoper) && e.E1.Eoper == OPind)
            {
                // a store through the address of a local writes it
                if (Symbol* s = localAddress(e.E1.E1))
                {
                    excluded[s.Ssymnum] = true;
                    if (elem* i = indexPart(e.E1.E1))
                        gather(i);
                }
                else
                    gather(e.E1);
                if (OTbinary(e.Eoper))
                {
                    e = e.E2;
                    continue;
                }
                return;
            }
            if (e.Eoper == OPind && localAddress(e.E1))
            {
                // a load from it reads it
                if (elem* i = indexPart(e.E1))
                {
                    e = i;
                    continue;
                }
                return;
            }
            if (OTassign(e.Eoper) && e.E1.Eoper == OPvar)
            {
                Symbol* s = e.E1.Vsym;
                if (s.Ssymnum < globsym.length && globsym[s.Ssymnum] is s && isLocal(s))
                {
                    Symbol* r = copyOfReadonly(e, s);
                    if (!r || (source[s.Ssymnum] && source[s.Ssymnum] !is r))
                        excluded[s.Ssymnum] = true;
                    else
                    {
                        source[s.Ssymnum] = r;
                        any = true;
                    }
                }
                if (OTbinary(e.Eoper))
                {
                    e = e.E2;
                    continue;
                }
                return;
            }
            if (e.Eoper == OPrelconst)
            {
                Symbol* s = e.Vsym;
                if (s.Ssymnum < globsym.length && globsym[s.Ssymnum] is s)
                    excluded[s.Ssymnum] = true;
                return;
            }
            if (OTbinary(e.Eoper))
            {
                gather(e.E2);
                e = e.E1;
            }
            else if (OTunary(e.Eoper))
                e = e.E1;
            else
                return;
        }
    }
    foreach (b; BlockRange(bo.startblock))
        if (b.Belem)
            gather(b.Belem);
    if (!any)
        return;

    bool forwarded(const Symbol* s)
    {
        return s.Ssymnum < globsym.length && globsym[s.Ssymnum] is s && source[s.Ssymnum] &&
               !excluded[s.Ssymnum];
    }
    void rewrite(ref elem* e)
    {
        if (e.Eoper == OPstreq && e.E1.Eoper == OPvar && forwarded(e.E1.Vsym))
        {
            // the copy goes, its source read for nothing
            elem* e2 = e.E2;
            e.E2 = null;
            el_free(e);
            e = e2;
            rewrite(e);
            return;
        }
        if (e.Eoper == OPvar && forwarded(e.Vsym))
        {
            // a load through the data's address, which every code generator handles
            elem* a = el_ptr(source[e.Vsym.Ssymnum]);
            a.Voffset = e.Voffset;
            elem* load = el_una(OPind, e.Ety, a);
            load.ET = e.ET;
            load.Esrcpos = e.Esrcpos;
            el_free(e);
            e = load;
            return;
        }
        if (e.Eoper == OPind)
            if (Symbol* s = localAddress(e.E1))
                if (forwarded(s))
                {
                    addressPart(e.E1).Vsym = source[s.Ssymnum];
                    if (e.E1.Eoper == OPadd)
                        rewrite(e.E1.E1.Eoper == OPrelconst ? e.E1.E2 : e.E1.E1);
                    return;
                }
        if (OTbinary(e.Eoper))
        {
            rewrite(e.E1);
            rewrite(e.E2);
        }
        else if (OTunary(e.Eoper))
            rewrite(e.E1);
    }
    foreach (b; BlockRange(bo.startblock))
        if (b.Belem)
            rewrite(b.Belem);
    foreach (i, s; globsym[])
        if (source[i] && !excluded[i])
            s.Sflags |= SFLdead;
}

/****************************
 * Optimize function.
 */

@trusted
void optfunc(ref GlobalOptimizer go, ref BlockOpt bo)
{
    if (debugc) printf("optfunc()\n");
    dbg_optprint("optfunc\n");

    debug if (debugb)
    {
        WRfunc("before optimization", funcsym_p, bo.startblock);
    }

    if (localgot)
    {   // Initialize with:
        //      localgot = OPgot;
        elem* e = el_long(TYnptr, 0);
        e.Eoper = OPgot;
        e = el_bin(OPeq, TYnptr, el_var(localgot), e);
        bo.startblock.Belem = el_combine(e, bo.startblock.Belem);
    }

    // Each pass through the loop can reduce only one level of comma expression.
    // The infinite loop check needs to take this into account.
    // Add 100 just to give optimizer more rope to try to converge.
    int iterationLimit = 100;
    for (block* b = bo.startblock; b; b = b.Bnext)
    {
        if (!b.Belem)
            continue;
        ++iterationLimit;
        int d = el_countCommas(b.Belem);
        if (d > iterationLimit)
            iterationLimit = d;
    }

    bo.assertsSplit = false;
    bo.exitsFound = false;
    go.unswitched = 0;
    int iter = 0;           // iteration count
    /* The loop optimizations and boolopt() run again only after a round in which
     * they changed something: what the other optimizations change rarely gives
     * them more to do, and they are costly
     */
    bool loopChanged = true;
    bool boolChanged = true;
    do
    {
        //printf("iter = %d\n", iter);
        // the rounds are limited, as some functions could take enormous amounts of time
        if (++iter > 200)
        {   assert(iter < iterationLimit);      // infinite loop check
            break;
        }

        //printf("optelem\n");
        /* canonicalize the trees        */
        foreach (b; BlockRange(bo.startblock))
            if (b.Belem)
            {
                debug if (debuge)
                {
                    printf("before\n");
                    elem_print(b.Belem);
                    //el_check(b.Belem);
                }

                b.Belem = doptelem(b.Belem, bc_goal(b.bc) | Goal.again);

                debug if (0 && debugf)
                {
                    printf("after\n");
                    elem_print(b.Belem);
                }
            }
        //printf("blockopt\n");

        /* Only scan once to prevent recursive functions from endlessly being inlined
         * https://issues.dlang.org/show_bug.cgi?id=23857
         */
        if (iter == 1)
        {
            scanForInlines(funcsym_p);
            forwardReadonlyCopies(bo);
        }

        if (go.mfoptim & MFdc)
            blockopt(go, bo, go.changes); // do block optimization
        /* The register candidates are recomputed by each copyprop(). What runs
         * after it in a round can remove the uses that disqualify a symbol,
         * which leaves the candidates conservative, but adds none
         */
        if (iter == 1)
            out_regcand(globsym[]);     // recompute register candidates
        else debug
        {
            // check the candidates kept claim nothing a recomputation does not, and keep them
            Barray!uint before;
            foreach (sym; globsym[])
                before.push(sym.Sflags & (GTregcand | SFLdistinct));
            Barray!SYMIDX nums;
            foreach (sym; globsym[])
                nums.push(sym.Ssymnum);
            out_regcand(globsym[]);
            foreach (i, sym; globsym[])
            {
                const now = sym.Sflags & (GTregcand | SFLdistinct);
                assert((before[i] & ~now) == 0 && nums[i] == sym.Ssymnum);
                sym.Sflags = (sym.Sflags & ~(GTregcand | SFLdistinct)) | before[i];
            }
            before.dtor();
            nums.dtor();
        }
        go.changes = 0;                 // no changes yet
        sliceStructs(globsym, bo.startblock);
        if (iter == 1)
            sliceFloatStructs(globsym, bo.startblock);
        if (go.mfoptim & MFcnp)
            constprop(go, bo, go.changes);  /* make relationals unsigned     */
        /* Conditions proven by the relations holding where they are tested,
         * such as array bounds checks, go before the loop optimizations, which
         * then have fewer uses of the induction variables to keep
         */
        if (iter == 1 && go.mfoptim & MFcnp)
            rangeopt(go, bo);
        if (go.mfoptim & (MFli | MFliv))
        {
            if (loopChanged)
            {
                const before = go.changes;
                loopopt(go, bo);            /* remove loop invariants and    */
                                            /* induction vars                */
                                            /* do loop rotation              */
                loopChanged = go.changes != before;
            }
        }
        else
            foreach (b; BlockRange(bo.startblock))
                b.Bweight = 1;
        dbg_optprint("boolopt\n");

        // AArch64 does without boolopt(), which costs more than it gains
        if (go.mfoptim & MFcnp && boolChanged && config.target_cpu != TARGET_AArch64)
        {
            const before = go.changes;
            boolopt(go, bo);              // optimize boolean values
            boolChanged = go.changes != before;
        }
        /* The rest of the round runs whatever changed so far, as starting the
         * next round at once takes more rounds to settle. Constant propagation
         * runs once a round, at its start.
         */
        if (go.mfoptim & MFcp)
            copyprop(go, bo);           /* do copy propagation           */

        /* Floating point constants and string literals need to be
         * replaced with loads from variables in read-only data.
         * This can result in localgot getting needed.
         */
        Symbol* localgotsave = localgot;
        for (block* b = bo.startblock; b; b = b.Bnext)
        {
            if (b.Belem)
            {
                b.Belem = doptelem(b.Belem, bc_goal(b.bc) | Goal.struct_);
                if (b.Belem)
                    b.Belem = el_convert(go, b.Belem);
            }
        }
        if (localgot != localgotsave)
        {   /* Looks like we did need localgot, initialize with:
             *  localgot = OPgot;
             */
            elem* e = el_long(TYnptr, 0);
            e.Eoper = OPgot;
            e = el_bin(OPeq, TYnptr, el_var(localgot), e);
            bo.startblock.Belem = el_combine(e, bo.startblock.Belem);
        }

        /* localize() is after localgot, otherwise we wind up with
         * more than one OPgot in a function, which mucks up OSX
         * code generation which assumes at most one (localgotoffset).
         */
        if (go.mfoptim & MFlocal)
            localize(bo, go.changes);      // improve expression locality
        if (go.mfoptim & MFda)
            rmdeadass(go, bo, go.changes); /* remove dead assignments       */

        if (debugc) printf("changes = %d\n", go.changes);
        if (!(go.changes && go.mfoptim & MFloop))
            break;
    } while (1);
    if (debugc) printf("%d iterations\n",iter);

    if (go.mfoptim & MFdc)
    {
        blockopt(go, bo, go.changes);         // do block optimization
        duplicateTests(bo);
    }

    pairSinCos(bo);

    for (block* b = bo.startblock; b; b = b.Bnext)
    {
        if (b.Belem)
        {
            postoptelem(b.Belem);
            combineByteLoads(b.Belem, !(b.bc == BC.goto_ || b.bc == BC.exit));
        }
    }
    if (go.mfoptim & MFli)
        loopConstants(bo);
    if (go.mfoptim & MFvbe)
        verybusyexp(go, bo, go.changes); /* very busy expressions         */
    if (go.mfoptim & MFcse)
        builddags(go, bo);            /* common subexpressions         */
    if (go.mfoptim & MFdv)
        deadvar();                  /* eliminate dead variables      */

    debug if (debugb)
    {
        WRfunc("after optimization", funcsym_p, bo.startblock);
    }

    // Prepare for code generator
    for (block* b = bo.startblock; b; b = b.Bnext)
    {
        block_optimizer_free(b);
    }
}

/************************************* Sine and cosine pairs ***********************************/

/* The sine and cosine of one value, both computed in the same straight-line
 * code, are taken from one call to Darwin's __sincosf_stret or __sincos_stret,
 * which is how LLVM selects them on Darwin. The combined call and the separate
 * libm calls differ in the last bit for some arguments, so optimized code makes
 * the same choice as LLVM to compute the same bits as code built by LDC.
 *
 * A pair is two calls of the C functions sinf and cosf, or sin and cos (sinl
 * and cosl where real is double), in one block, outside of conditional code
 * that has calls or assignments, with matching arguments that nothing assigns
 * between the calls. A call with a constant argument is folded instead.
 */

private struct SinCosCand
{
    elem* e;            // the call
    bool isCos;
}

private struct SinCosGroup
{
    elem* arg;          // the argument of its first call
    bool dbl;           // double, not float
    bool open;          // calls further on can join it
    bool hasSin, hasCos;
    elem** stmt;        // the statement its first call is in
    bool hoist;         // the combined call can go before that statement
    Barray!(elem*) path;    // the elems from its first call up to that statement
    Barray!SinCosCand cands;
}

private __gshared
{
    Barray!SinCosGroup sinCosGroups;
    size_t sinCosFloor;             // the first group the current code can join
    elem** sinCosStmt;              // the statement being walked
    Barray!(elem*) sinCosPath;      // the elems being walked, outermost first
    Barray!(Symbol*) sinCosStmtWrites;  // the variables it assigns
    bool sinCosStmtMemWrite;            // whether it writes memory
    bool sinCosStmtCond;                // whether it has conditional code
    type*[2] sinCosType;            // { float s, c; } and { double s, c; }
    Symbol*[2] sinCosFunc;          // __sincosf_stret and __sincos_stret
}

/* Which of sin or cos call e is: 1 for sine, 2 for cosine, 0 for neither,
 * with whether it is the double function
 */
@trusted
private int sinCosKind(const(elem)* e, out bool dbl)
{
    if (e.Eoper != OPcall || e.E1.Eoper != OPvar || e.E2.Eoper == OPparam)
        return 0;
    const s = e.E1.Vsym;
    if (!s.Stype || !tyfunc(s.Stype.Tty) || type_mangle(s.Stype) != Mangle.c)
        return 0;
    if (s.Sclass != SC.extern_ && s.Sclass != SC.global)
        return 0;
    const ty = tybasic(e.Ety);
    if (!tyfloating(ty) || tycomplex(ty) || tyimaginary(ty) || tybasic(e.E2.Ety) != ty)
        return 0;
    const sz = tysize(ty);
    const(char)[] name = s.Sident.ptr[0 .. strlen(s.Sident.ptr)];
    if (sz == 4)
    {
        if (name == "sinf") return 1;
        if (name == "cosf") return 2;
    }
    else if (sz == 8)
    {
        dbl = true;
        if (name == "sin" || name == "sinl") return 1;
        if (name == "cos" || name == "cosl") return 2;
    }
    return 0;
}

/* Replace the call e of sin or cos of a constant with its value, computed the
 * way LLVM folds the libm call: in double with the host's libm, then rounded
 * to the type of the call. Like LLVM, a call that raises a floating point
 * exception other than inexact stays.
 */
@trusted
private void sinCosFold(elem* e, bool isCos)
{
    import core.stdc.errno : errno, EDOM, ERANGE;
    import core.stdc.fenv : feclearexcept, fetestexcept, FE_ALL_EXCEPT, FE_INEXACT;
    import core.stdc.math : cos, sin;

    const isFloat = tysize(e.Ety) == 4;
    const double x = isFloat ? e.E2.Vfloat : e.E2.Vdouble;
    if (x != x || x - x != 0)
        return;                         // NaN or infinity
    feclearexcept(FE_ALL_EXCEPT);
    errno = 0;
    const double r = isCos ? cos(x) : sin(x);
    if (errno == EDOM || errno == ERANGE || fetestexcept(FE_ALL_EXCEPT & ~FE_INEXACT))
        return;
    el_free(e.E1);
    el_free(e.E2);
    e.Eoper = OPconst;
    e.EV = Vconst.init;
    if (isFloat)
        e.Vfloat = cast(float) r;
    else
        e.Vdouble = r;
}

/* Whether e is an argument a pair can share: arithmetic on variables and
 * loads, with no call or assignment
 */
@trusted
private bool sinCosArg(const(elem)* e)
{
    switch (e.Eoper)
    {
        case OPvar:
            return !(e.Vsym.ty() & mTYvolatile);
        case OPconst:
            return true;
        case OPind:
            return !(e.Ety & mTYvolatile) && sinCosArg(e.E1);
        case OPrelconst:
            return true;
        case OPadd: case OPmin: case OPmul: case OPdiv:
            return sinCosArg(e.E1) && sinCosArg(e.E2);
        case OPneg:
        case OPd_f: case OPf_d:
        case OPs32_d: case OPu32_d: case OPs64_d: case OPu64_d:
        case OPs16_d:
            return sinCosArg(e.E1);
        default:
            return false;
    }
}

/* Whether a and b compute the same value, whatever their type modifiers
 */
@trusted
private bool sinCosMatch(const(elem)* a, const(elem)* b)
{
    if (a.Eoper != b.Eoper || tybasic(a.Ety) != tybasic(b.Ety))
        return false;
    switch (a.Eoper)
    {
        case OPvar:
        case OPrelconst:
            return a.Vsym == b.Vsym && a.Voffset == b.Voffset;
        case OPconst:
            return el_match(a, b);
        default:
            if (OTbinary(a.Eoper))
                return sinCosMatch(a.E1, b.E1) && sinCosMatch(a.E2, b.E2);
            if (OTunary(a.Eoper))
                return sinCosMatch(a.E1, b.E1);
            return false;
    }
}

/* Whether e reads the variable s, or reads memory and s is null
 */
@trusted
private bool sinCosReads(const(elem)* e, const(Symbol)* s)
{
    if (!e)
        return false;
    switch (e.Eoper)
    {
        case OPvar:
            return s ? e.Vsym == s : Symbol_isAffected(*e.Vsym);
        case OPind:
            return !s || sinCosReads(e.E1, s);
        case OPconst:
        case OPrelconst:
            return false;
        default:
            if (OTbinary(e.Eoper) && sinCosReads(e.E2, s))
                return true;
            return OTunary(e.Eoper) || OTbinary(e.Eoper) ? sinCosReads(e.E1, s) : false;
    }
}

/* Close the groups the write of s (or of memory, for null) changes the
 * argument of
 */
@trusted
private void sinCosWrite(const(Symbol)* s)
{
    foreach (ref g; sinCosGroups[])
        if (g.open && sinCosReads(g.arg, s))
            g.open = false;
}

/* Close the groups from first on
 */
@trusted
private void sinCosClose(size_t first)
{
    foreach (ref g; sinCosGroups[first .. $])
        g.open = false;
}

/* What the statement e assigns, into sinCosStmtWrites and sinCosStmtMemWrite
 */
@trusted
private void sinCosStmtScan(const(elem)* e)
{
    if (!e)
        return;
    const op = e.Eoper;
    bool dbl;
    if (OTcall(op) && sinCosKind(e, dbl) == 0)
        sinCosStmtMemWrite = true;
    if (OTassign(op))
    {
        if (e.E1.Eoper == OPvar)
        {
            sinCosStmtWrites.push(cast(Symbol*)e.E1.Vsym);
            if (Symbol_isAffected(*e.E1.Vsym))
                sinCosStmtMemWrite = true;
        }
        else
            sinCosStmtMemWrite = true;
    }
    else if (op == OPmemcpy || op == OPmemset || op == OPstrcpy || op == OPstrcat)
        sinCosStmtMemWrite = true;
    if (op == OPandand || op == OPoror || op == OPcond || op == OPhalt)
        sinCosStmtCond = true;
    if (OTbinary(op))
    {
        sinCosStmtScan(e.E1);
        sinCosStmtScan(e.E2);
    }
    else if (OTunary(op))
        sinCosStmtScan(e.E1);
}

/* Whether e has a call or an assignment
 */
@trusted
private bool sinCosEffects(const(elem)* e)
{
    if (!e)
        return false;
    const op = e.Eoper;
    if (OTcall(op) || OTassign(op) || op == OPmemcpy || op == OPmemset || op == OPstrcpy ||
        op == OPstrcat || op == OPhalt || op == OPvp_fp || op == OPcvp_fp)
        return true;
    if (OTbinary(op))
        return sinCosEffects(e.E1) || sinCosEffects(e.E2);
    if (OTunary(op))
        return sinCosEffects(e.E1);
    return false;
}

/* Walk the code at *pe, a statement or a sequence of them
 */
@trusted
private void sinCosStatements(elem** pe)
{
    elem* e = *pe;
    if (e.Eoper == OPcomma)
    {
        sinCosStatements(&e.E1);
        sinCosStatements(&e.E2);
        return;
    }
    auto saveStmt = sinCosStmt;
    const saveMem = sinCosStmtMemWrite;
    const saveCond = sinCosStmtCond;
    const saveWrites = sinCosStmtWrites.length;
    sinCosStmt = pe;
    sinCosStmtMemWrite = false;
    sinCosStmtCond = false;
    sinCosStmtScan(e);
    sinCosWalk(e);
    sinCosStmt = saveStmt;
    sinCosStmtMemWrite = saveMem;
    sinCosStmtCond = saveCond;
    sinCosStmtWrites.setLength(saveWrites);
}

/* Walk the code at *pe, which runs only under a condition
 */
@trusted
private void sinCosArm(elem** pe)
{
    const saveFloor = sinCosFloor;
    const first = sinCosGroups.length;
    sinCosFloor = first;
    sinCosStatements(pe);
    sinCosClose(first);
    sinCosFloor = saveFloor;
}

/* Whether the call being walked is evaluated after the call path leads to:
 * in another statement, or after a comma or a condition evaluated first
 */
@trusted
private bool sinCosSequenced(elem*[] path)
{
    auto cur = sinCosPath[];
    size_t i = 0;
    while (i < path.length && i < cur.length && path[i] == cur[i])
        ++i;
    if (i == 0)
        return true;                    // another statement
    if (i == path.length || i == cur.length)
        return false;
    const lca = path[i - 1];
    switch (lca.Eoper)
    {
        case OPcomma:
        case OPandand:
        case OPoror:
        case OPcond:
            return path[i] == lca.E1 && cur[i] == lca.E2;
        default:
            return false;
    }
}

/* Walk e in the order it is evaluated
 */
@trusted
private void sinCosWalk(elem* e)
{
    if (!e)
        return;
    sinCosPath.push(e);
    scope (exit) sinCosPath.setLength(sinCosPath.length - 1);
    const op = e.Eoper;
    switch (op)
    {
        case OPcomma:
            sinCosWalk(e.E1);
            sinCosWalk(e.E2);
            return;

        case OPandand:
        case OPoror:
            sinCosWalk(e.E1);
            sinCosArm(&e.E2);
            if (sinCosEffects(e.E2))
                sinCosClose(0);         // the rest is in other basic blocks
            return;

        case OPcond:
            sinCosWalk(e.E1);
            if (e.E2.Eoper == OPcolon || e.E2.Eoper == OPcolon2)
            {
                sinCosArm(&e.E2.E1);
                sinCosArm(&e.E2.E2);
            }
            else
                sinCosArm(&e.E2);
            if (sinCosEffects(e.E2))
                sinCosClose(0);
            return;

        default:
            break;
    }

    if (OTcall(op))
    {
        if (OTbinary(op))
            sinCosWalk(e.E2);
        if (e.E1.Eoper != OPvar)
            sinCosWalk(e.E1);
        bool dbl;
        const kind = sinCosKind(e, dbl);
        if (kind == 0)
        {
            sinCosWrite(null);          // a call can write memory
            return;
        }
        /* The value of the argument is what calls match on: the variable an
         * argument assigns stands for it
         */
        elem* arg = e.E2;
        const assigns = arg.Eoper == OPeq && arg.E1.Eoper == OPvar;
        elem* key = assigns ? arg.E1 : arg;
        if (arg.Eoper == OPconst)
        {
            sinCosFold(e, kind == 2);
            return;
        }
        if (!sinCosArg(key))
            return;
        SinCosGroup* g;
        foreach (ref gi; sinCosGroups[sinCosFloor .. $])
            if (gi.open && gi.dbl == dbl && sinCosMatch(gi.arg, key))
            {
                g = &gi;
                break;
            }
        if (g)
        {
            /* Where the combined call replaces the first call, the others must
             * be evaluated after it
             */
            if (!g.hoist && !sinCosSequenced(g.path[]))
                return;
        }
        else
        {
            g = sinCosGroups.push();
            *g = SinCosGroup.init;
            g.arg = key;
            g.dbl = dbl;
            g.open = true;
            g.stmt = sinCosStmt;
            /* The combined call goes before the statement if the statement
             * does not change the argument and has no test that may guard a
             * load of it; otherwise it replaces the first call
             */
            g.hoist = !assigns && !(sinCosStmtCond && sinCosReads(arg, null)) &&
                !(sinCosStmtMemWrite && sinCosReads(arg, null));
            foreach (s; sinCosStmtWrites[])
                if (sinCosReads(arg, s))
                    g.hoist = false;
            foreach (p; sinCosPath[])
                g.path.push(p);
        }
        g.cands.push(SinCosCand(e, kind == 2));
        if (kind == 2)
            g.hasCos = true;
        else
            g.hasSin = true;
        return;
    }

    if (OTassign(op))
    {
        sinCosWalk(e.E2);
        elem* e1 = e.E1;
        if (e1.Eoper == OPvar)
        {
            sinCosWrite(e1.Vsym);
            if (Symbol_isAffected(*e1.Vsym))
                sinCosWrite(null);
        }
        else
        {
            sinCosWalk(e1);
            sinCosWrite(null);
        }
        return;
    }

    if (OTbinary(op))
    {
        sinCosWalk(e.E1);
        sinCosWalk(e.E2);
    }
    else if (OTunary(op))
        sinCosWalk(e.E1);
    if (op == OPmemcpy || op == OPmemset || op == OPstrcpy || op == OPstrcat)
        sinCosWrite(null);
}

/* Rewrite the calls of g as reads of one combined call's result
 */
@trusted
private void sinCosFuse(ref SinCosGroup g)
{
    const i = g.dbl;
    const tyf = g.dbl ? TYdouble : TYfloat;
    const esz = g.dbl ? 8 : 4;
    if (!sinCosType[i])
    {
        type* te = tstypes[tyf];
        type* t = type_struct_class(g.dbl ? "__double2" : "__float2", esz, 2 * esz, te, te,
            false, false, true, false);
        sinCosType[i] = t;
        type*[1] params = [te];
        type* tf = type_function(TYnfunc, params[], false, t);
        tf.Tmangle = Mangle.c;
        sinCosFunc[i] = symbol_name(g.dbl ? "__sincos_stret" : "__sincosf_stret", SC.extern_, tf);
    }
    type* t = sinCosType[i];
    Symbol* tmp = symbol_genauto(t);
    tmp.Sfl = FL.auto_;

    elem* first = g.cands[0].e;
    elem* arg = g.hoist ? el_copytree(first.E2) : first.E2;
    elem* call = el_bin(OPcall, TYstruct, el_var(sinCosFunc[i]), arg);
    call.ET = t;
    elem* lhs = el_var(tmp);
    lhs.ET = t;
    elem* eq = el_bin(OPstreq, TYstruct, lhs, call);
    eq.ET = t;
    if (g.hoist)
    {
        *g.stmt = el_bin(OPcomma, (*g.stmt).Ety, eq, *g.stmt);
        if (tyaggregate((*g.stmt).Ety))
            (*g.stmt).ET = (*g.stmt).E2.ET;
    }

    foreach (k, ref c; g.cands[])
    {
        elem* e = c.e;
        el_free(e.E1);
        const ty = e.Ety;
        elem* ev = el_var(tmp);
        ev.Ety = ty;
        ev.Voffset = c.isCos ? esz : 0;
        if (k == 0 && !g.hoist)
        {
            // the first call becomes (tmp = combined call, its part)
            e.Eoper = OPcomma;
            e.E1 = eq;
            e.E2 = ev;
        }
        else
        {
            el_free(e.E2);
            *e = *ev;
            ev.Eoper = OPconst;         // no longer refers to tmp
            el_free(ev);
        }
    }
}

/* Whether b continues the straight-line code of the block before it
 */
@trusted
private bool sinCosContinues(ref BlockOpt bo, block* b)
{
    if (b == bo.startblock || b.Bpred.length != 1)
        return false;
    block* p = b.Bpred[0];
    return p != b && p.bc == BC.goto_ && p.Bsucc[0] == b && p.Btry == b.Btry;
}

/***************************************
 * Pair the sine and cosine calls of the function's straight-line code, each
 * a block and the blocks that continue it, on Darwin AArch64.
 * Params:
 *      bo = the function's blocks
 */
@trusted
void pairSinCos(ref BlockOpt bo)
{
    if (config.target_cpu != TARGET_AArch64 || config.exe != EX_OSX64)
        return;
    for (block* b = bo.startblock; b; b = b.Bnext)
    {
        if (sinCosContinues(bo, b))
            continue;
        foreach (ref g; sinCosGroups[])
        {
            g.cands.dtor();
            g.path.dtor();
        }
        sinCosGroups.setLength(0);
        sinCosFloor = 0;
        for (block* x = b; ; x = x.Bsucc[0])
        {
            if (x.Belem)
                sinCosStatements(&x.Belem);
            if (x.bc != BC.goto_ || !sinCosContinues(bo, x.Bsucc[0]))
                break;
        }
        foreach (ref g; sinCosGroups[])
            if (g.hasSin && g.hasCos)
                sinCosFuse(g);
    }
}
