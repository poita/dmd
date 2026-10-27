/**
 * Code to do the Data Flow Analysis (doesn't act on the data).
 *
 * Copyright:   Copyright (C) 1985-1998 by Symantec
 *              Copyright (C) 2000-2026 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 https://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/compiler/src/dmd/backend/gflow.d, backend/gflow.d)
 * Documentation:  https://dlang.org/phobos/dmd_backend_gflow.html
 * Coverage:    https://codecov.io/gh/dlang/dmd/src/master/compiler/src/dmd/backend/gflow.d
 */

module dmd.backend.gflow;

import core.stdc.stdio;
import core.stdc.stdlib;
import core.stdc.string;

import dmd.backend.cc;
import dmd.backend.blockopt : BlockOpt, bo;
import dmd.backend.cdef;
import dmd.backend.oper;
import dmd.backend.global : err_nomem;
import dmd.backend.blockopt : blockopt;
import dmd.backend.evalu8 : iftrue;
import dmd.backend.go;
import dmd.backend.gother : buildDefIndex, defIndex, isCopy;
import dmd.backend.el;
import dmd.backend.symbol;
import dmd.backend.ty;
import dmd.backend.type;

import dmd.backend.barray;
import dmd.backend.dvec;

nothrow:
@safe:

void vec_setclear(size_t b, vec_t vs, vec_t vc) { vec_setbit(b, vs); vec_clearbit(b, vc); }

@trusted
bool Eunambig(elem* e) { return OTassign(e.Eoper) && e.E1.Eoper == OPvar; }

@trusted
char symbol_isintab(const Symbol* s) { return sytab[s.Sclass] & SCSS; }

@trusted
void util_free(void* p) { if (p) free(p); }

@trusted
void* util_calloc(uint n, uint size)
{
    void* p = calloc(n, size);
    if (n * size && !p)
        err_nomem();
    return p;
}

@trusted
void* util_realloc(void* p, size_t n, size_t size)
{
    void* q = realloc(p, n * size);
    if (n * size && !q)
        err_nomem();
    return q;
}

/***************** EXCEPTION EDGES *********************/

/* The flow graph has no edges for exceptions. A block of the body a try guards
 * that calls a function may throw, from anywhere in it, before or after any of
 * its definitions, to the handlers of each try enclosing it: the catch blocks,
 * or the landing pad of a finally. The data flow analyses and the loops take
 * these edges from here.
 */
struct EhEdges
{
    bool any;                   // a block may throw to a handler
    vec_t throws;               // by dfo index: the block may throw to a handler
    Barray!uint tryIndex;       // by dfo index: index in tries[] of a try block, or of the try
                                // a handler is entered by, or uint.max
    Barray!(block*) tries;      // the try blocks in the flow graph
    Barray!uint guardStart;     // by index in tries[]: start of its blocks in guarded[]
    Barray!uint guarded;        // the dfo indices of the blocks that may throw to each try's handlers

  nothrow:

    /*******************************
     * Find the exception edges of the flow graph bo.dfo[].
     */
    @trusted
    void compute(ref BlockOpt bo)
    {
        any = false;
        tries.setLength(0);
        guarded.setLength(0);
        const n = bo.dfo.length;
        bool anyTry;
        foreach (b; bo.dfo[])
        {
            if (b.bc == BC.try_)
                anyTry = true;
        }
        if (!anyTry)
            return;

        tryIndex.setLength(n);
        tryIndex[][] = uint.max;
        foreach (b; bo.dfo[])
        {
            if (b.bc != BC.try_)
                continue;
            const t = cast(uint)tries.length;
            tries.push(b);
            tryIndex[b.Bdfoidx] = t;
            foreach (h; b.Bsucc[1 .. $])
            {
                h = handlerEntry(h);
                if (inDfo(bo, h))
                    tryIndex[h.Bdfoidx] = t;
            }
        }

        vec_free(throws);
        throws = vec_calloc(n);
        guardStart.setLength(tries.length + 1);
        guardStart[][] = 0;
        foreach (i, b; bo.dfo[])
        {
            if (!b.Btry || !(b.bc == BC.asm_ || b.Belem && mayThrow(b.Belem)))
                continue;
            bool guards;
            for (block* t = b.Btry; t; t = t.Btry)
            {
                if (isTry(bo, t))
                {
                    ++guardStart[tryIndex[t.Bdfoidx] + 1];
                    guards = true;
                }
            }
            if (guards)
            {
                vec_setbit(i, throws);
                any = true;
            }
        }
        if (!any)
            return;
        foreach (t; 1 .. guardStart.length)
            guardStart[t] += guardStart[t - 1];
        guarded.setLength(guardStart[tries.length]);
        Barray!uint fill;
        fill.setLength(tries.length);
        fill[][] = 0;
        foreach (i; VecRange(throws))
        {
            for (block* t = bo.dfo[i].Btry; t; t = t.Btry)
            {
                if (isTry(bo, t))
                {
                    const ti = tryIndex[t.Bdfoidx];
                    guarded[guardStart[ti] + fill[ti]++] = cast(uint)i;
                }
            }
        }
        fill.dtor();
    }

    /// Whether t is a try block of the flow graph
    bool isTry(ref BlockOpt bo, const block* t) const
    {
        return t.bc == BC.try_ && inDfo(bo, t);
    }

    /// The dfo indices of the blocks that may throw to the handlers of tries[t]
    uint[] guardedBy(uint t)
    {
        return guarded[guardStart[t] .. guardStart[t + 1]];
    }

    /// Whether block b of the flow graph is entered by an exception
    bool isHandler(const block* b) const
    {
        return any && b.bc != BC.try_ && tryIndex[b.Bdfoidx] != uint.max;
    }

    /// The try whose handler block b is, an index in tries[]
    uint handlerOf(const block* b) const
    {
        return tryIndex[b.Bdfoidx];
    }

    /// Whether block b may throw to a handler
    bool mayThrowAt(const block* b) const
    {
        return any && vec_testbit(b.Bdfoidx, throws);
    }

    /*********************************
     * Call dg(h) for each handler h of each try enclosing block b of the
     * flow graph, innermost first.
     */
    @trusted
    void forHandlers(ref BlockOpt bo, block* b, scope void delegate(block*) nothrow dg)
    {
        for (block* t = b.Btry; t; t = t.Btry)
        {
            if (!isTry(bo, t))
                continue;
            foreach (h; t.Bsucc[1 .. $])
            {
                h = handlerEntry(h);
                if (inDfo(bo, h))
                    dg(h);
            }
        }
    }
}

__gshared EhEdges ehEdges;

/* The block an exception enters handler h of a try by: the landing pad of a
 * finally, or the catch block itself
 */
@trusted
private block* handlerEntry(block* h)
{
    if (h.bc == BC.finally_ && h.Bsucc.length && h.Bsucc[0].bc == BC.lpad)
        return h.Bsucc[0];
    return h;
}

/// Whether b is a block of the flow graph of bo
@trusted
private bool inDfo(ref BlockOpt bo, const block* b)
{
    return b.Bdfoidx < bo.dfo.length && bo.dfo[b.Bdfoidx] is b;
}

/// Whether evaluating e may throw an exception
@trusted
private bool mayThrow(const(elem)* e)
{
    while (1)
    {
        const op = e.Eoper;
        if (OTcall(op) || op == OPasm)
            return true;
        if (OTbinary(op))
        {
            if (mayThrow(e.E2))
                return true;
        }
        else if (!OTunary(op))
            return false;
        e = e.E1;
    }
}

/***************** REACHING DEFINITIONS *********************/

/************************************
 * Compute reaching definitions (RDs).
 * That is, for each block B and each program variable X
 * find all elems that could be the last elem that defines
 * X along some path to B.
 * Binrd = the set of defs reaching the beginning of B.
 * Boutrd = the set of defs reaching the end of B.
 * Bkillrd = set of defs that are killed by some def in B.
 * Bgenrd = set of defs in B that reach the end of B.
 */

@trusted
void flowrd(ref GlobalOptimizer go, ref BlockOpt bo)
{
    rdgenkill(go, bo);        /* Compute Bgen and Bkill for RDs       */
    if (go.defnod.length == 0)     /* if no definition elems               */
        return;             /* no analysis to be done               */

    /* The transfer equation is:                                    */
    /*      Bin = union of Bouts of all predecessors of B.          */
    /*      Bout = (Bin - Bkill) | Bgen                             */
    /* Using Ullman's algorithm:                                    */

    foreach (b; bo.dfo[])
        vec_copy(b.Boutrd, b.Bgen);

    /* An exception reaches a handler from anywhere in the body its try guards,
     * entered only by the try block, so what reaches the handler is what
     * reaches the try block, and any definition in the body:
     *      i = 0;
     *      try { i = 1; f(); i = 2; } catch () { x = i; }
     */
    ehEdges.compute(bo);
    Barray!vec_t bodyDefs;      // by index in ehEdges.tries[]: the definitions in its body
    if (ehEdges.any)
    {
        bodyDefs.setLength(ehEdges.tries.length);
        bodyDefs[][] = null;
        foreach (t; 0 .. ehEdges.tries.length)
        {
            if (ehEdges.guardedBy(cast(uint)t).length)
                bodyDefs[t] = vec_calloc(go.defnod.length);
        }
        foreach (i, ref dn; go.defnod[])
        {
            for (block* t = dn.DNblock.Btry; t; t = t.Btry)
            {
                if (ehEdges.isTry(bo, t))
                {
                    if (vec_t v = bodyDefs[ehEdges.tryIndex[t.Bdfoidx]])
                        vec_setbit(i, v);
                }
            }
        }
    }

    bool anychng;
    vec_t tmp = vec_calloc(go.defnod.length);
    Dirty dirty;                // only a change to the Boutrd of a predecessor changes Binrd
    dirty.init(bo.dfo.length);
    do
    {
        anychng = false;
        foreach (i, b; bo.dfo[])    // for each block
        {
            if (!dirty.p[i])
                continue;
            dirty.p[i] = false;
            /* Binrd = union of Boutrds of all predecessors of b */
            vec_clear(b.Binrd);
            if (b.bc != BC.catch_ /*&& b.bc != BC.jcatch*/)
            {
                /* Set Binrd to 0 to account for:
                 * i = 0;
                 * try { i = 1; throw; } catch () { x = i; }
                 */
                foreach (bp; b.Bpred[])
                    vec_orass(b.Binrd,bp.Boutrd);
            }
            if (ehEdges.isHandler(b))
            {
                if (vec_t v = bodyDefs[ehEdges.handlerOf(b)])
                    vec_orass(b.Binrd, v);
            }
            /* Bout = (Bin - Bkill) | Bgen */
            vec_sub(tmp,b.Binrd,b.Bkill);
            vec_orass(tmp,b.Bgen);
            if (!vec_equal(tmp,b.Boutrd))
            {
                anychng = true;
                dirty.mark(bo, b.Bsucc[]);
            }
            vec_copy(b.Boutrd,tmp);
        }
    } while (anychng);              /* while any changes to Boutrd  */
    dirty.free();
    vec_free(tmp);
    foreach (v; bodyDefs[])
        vec_free(v);
    bodyDefs.dtor();

    static if (0)
    {
        dbg_printf("Reaching definitions\n");
        foreach (i, b; dfo[])    // for each block
        {
            assert(vec_numbits(b.Binrd) == go.defnod.length);
            dbg_printf("B%d Bin ", cast(int)i); vec_println(b.Binrd);
            dbg_printf("  Bgen "); vec_println(b.Bgen);
            dbg_printf(" Bkill "); vec_println(b.Bkill);
            dbg_printf("  Bout "); vec_println(b.Boutrd);
        }
    }
}

/* Whether each block of bo.dfo[] needs its data flow equation evaluated again,
 * because the IN or OUT of a block next to it changed
 */
private struct Dirty
{
    bool* p;
    size_t n;

    @trusted nothrow void init(size_t n)
    {
        this.n = n;
        p = cast(bool*)malloc(n ? n : 1);
        if (!p)
            err_nomem();
        p[0 .. n] = true;
    }

    @trusted nothrow void free() { .free(p); }

    /// Mark the blocks in `blocks` that are in bo.dfo[]
    @trusted nothrow void mark(ref BlockOpt bo, block*[] blocks)
    {
        foreach (b; blocks)
        {
            const i = b.Bdfoidx;
            if (i < n && bo.dfo[i] is b)
                p[i] = true;
        }
    }
}

/***************************
 * Compute Bgen and Bkill for RDs.
 */

@trusted
private void rdgenkill(ref GlobalOptimizer go, ref BlockOpt bo)
{
    if (!numberDefs(go, bo))
        return;

    const deftop = cast(uint)go.defnod.length;
    foreach (b; bo.dfo[])    // for each block
    {
        /* dump any existing vectors */
        vec_free(b.Bgen);
        vec_free(b.Bkill);
        vec_free(b.Binrd);
        vec_free(b.Boutrd);

        /* calculate and create new vectors */
        rdelem(go, b.Bgen, b.Bkill, b.Belem, deftop);
        if (b.bc == BC.asm_)
        {
            vec_clear(b.Bkill);        // KILL nothing
            vec_set(b.Bgen);           // GEN everything
        }
        b.Binrd = vec_calloc(deftop);
        b.Boutrd = vec_calloc(deftop);
    }
}

/***************************************
 * Fill in go.defnod[] with the definition elems in dfo order, without the
 * reaching definitions data flow.
 * Returns:
 *      false if there are no definition elems
 */
@trusted
private bool numberDefs(ref GlobalOptimizer go, ref BlockOpt bo)
{
    /* go.defnod[] holds the definition elems in dfo order, each block's in
     * order of execution, with the enclosing block
     */
    go.defnod.setLength(0);
    foreach (b; bo.dfo[])    // for each block
        if (b.Belem)
            asgdefelems(go.defnod, b, b.Belem);
    buildDefIndex(go);
    return go.defnod.length != 0;
}

/**************************
 * Append the definition elems of n to defnod[] in order of execution,
 * numbering them.
 */

@trusted
private void asgdefelems(ref Barray!DefNode defnod, block* b, elem* n)
{
    assert(b && n);
    const op = n.Eoper;
    if (ERTOL(n))
    {
        asgdefelems(defnod, b, n.E2);
        asgdefelems(defnod, b, n.E1);
    }
    else if (OTbinary(op))
    {
        asgdefelems(defnod, b, n.E1);
        asgdefelems(defnod, b, n.E2);
    }
    else if (OTunary(op))
        asgdefelems(defnod, b, n.E1);

    if (OTdef(op))
    {
        n.Edef = cast(uint)defnod.length;
        DefNode* dn = defnod.push();
        *dn = DefNode(n, b);
        if (OTassign(op) && n.E1.Eoper == OPvar)
        {
            const t = n.E1;
            dn.DNsym = t.Vsym;
            dn.DNoff = t.Voffset;
            dn.DNtop = t.Voffset + (op == OPstreq ? type_size(n.ET) : tysize(t.Ety));
        }
    }
    else
        n.Edef = ~0;       // just to ensure it is not in the array
}

/*************************************
 * Allocate and compute rd GEN and KILL.
 * Params:
 *      GEN = gen vector to create
 *      KILL = kill vector to create
 *      n = elem tree to evaluate for GEN and KILL
 *      deftop = number of bits in vectors
 */
private void rdelem(ref GlobalOptimizer go, out vec_t GEN, out vec_t KILL, elem* n, uint deftop)
{
    GEN  = vec_calloc(deftop);
    KILL = vec_calloc(deftop);
    if (n)
        accumrd(go, GEN, KILL, n, deftop);
}

/**************************************
 * Accumulate GEN and KILL vectors for this elem.
 */

@trusted
private void accumrd(ref GlobalOptimizer go, vec_t GEN,vec_t KILL,elem* n,uint deftop)
{
    assert(GEN && KILL && n);
    const op = n.Eoper;
    if (OTunary(op))
        accumrd(go, GEN, KILL, n.E1, deftop);
    else if (OTbinary(op))
    {
        if (op == OPcolon || op == OPcolon2)
        {
            vec_t Gl,Kl,Gr,Kr;
            rdelem(go, Gl, Kl, n.E1, deftop);
            rdelem(go, Gr, Kr, n.E2, deftop);

            switch (el_returns(n.E1) * 2 | int(el_returns(n.E2)))
            {
                case 3: // E1 and E2 return
                    /* GEN = (GEN - Kl) | Gl |
                     *       (GEN - Kr) | Gr
                     * KILL |= Kl & Kr
                     * This simplifies to:
                     * GEN = GEN | (Gl | Gr) | (GEN - (Kl & Kr)
                     * KILL |= Kl & Kr
                     */
                    vec_andass(Kl,Kr);
                    vec_orass(KILL,Kl);

                    vec_orass(Gl,Gr);
                    vec_sub(Gr,GEN,Kl);  // (GEN - (Kl & Kr)
                    vec_or(GEN,Gl,Gr);
                    break;

                case 2: // E1 returns
                    /* GEN = (GEN - Kl) | Gl
                     * KILL |= Kl
                     */
                    vec_subass(GEN,Kl);
                    vec_orass(GEN,Gl);
                    vec_orass(KILL,Kl);
                    break;

                case 1: // E2 returns
                    /* GEN = (GEN - Kr) | Gr
                     * KILL |= Kr
                     */
                    vec_subass(GEN,Kr);
                    vec_orass(GEN,Gr);
                    vec_orass(KILL,Kr);
                    break;

                case 0: // neither returns
                    break;

                default:
                    assert(0);
            }

            vec_free(Gl);
            vec_free(Kl);
            vec_free(Gr);
            vec_free(Kr);
        }
        else if (op == OPandand || op == OPoror)
        {
            accumrd(go, GEN, KILL, n.E1, deftop);
            vec_t Gr,Kr;
            rdelem(go, Gr, Kr, n.E2, deftop);
            if (el_returns(n.E2))
                vec_orass(GEN,Gr);      // GEN |= Gr

            vec_free(Gr);
            vec_free(Kr);
        }
        else if (OTrtol(op) && ERTOL(n))
        {
            accumrd(go, GEN, KILL, n.E2, deftop);
            accumrd(go, GEN, KILL, n.E1, deftop);
        }
        else
        {
            accumrd(go, GEN, KILL, n.E1, deftop);
            accumrd(go, GEN, KILL, n.E2, deftop);
        }
    }

    if (OTdef(op))                  /* if definition elem           */
        updaterd(go.defnod, n, GEN, KILL);
}

/******************** AVAILABLE EXPRESSIONS ***********************/

/************************************
 * Compute available expressions (AEs).
 * That is, expressions whose result is still current.
 * Bin = the set of AEs reaching the beginning of B.
 * Bout = the set of AEs reaching the end of B.
 */

@trusted
void flowae(ref GlobalOptimizer go, ref BlockOpt bo)
{
    go.flowxx = AE;
    flowaecp(go, bo);
}

/****************************************
 * Number the available expressions in go.expnod[] and compute go.defkill,
 * go.starkill and go.vptrkill as flowae() does, without the data flow, for
 * walks that look at the expressions available within extended basic blocks.
 */
@trusted
void numberae(ref GlobalOptimizer go, ref BlockOpt bo)
{
    go.flowxx = AE;
    aecpgenkill(go, bo, false);
}

/**************************** COPY PROPAGATION ************************/

/***************************************
 * Compute copy propagation info (CPs).
 * Very similar to AEs (the same code is used).
 * Using RDs for copy propagation is WRONG!
 * That is, set of copy statements still valid.
 * Bin = the set of CPs reaching the beginning of B.
 * Bout = the set of CPs reaching the end of B.
 */

@trusted
void flowcp(ref GlobalOptimizer go, ref BlockOpt bo)
{
    go.flowxx = CP;
    flowaecp(go, bo);
    copyBlocks.valid = false;
}

/*****************************************
 * Common flow analysis routines for Available Expressions and
 * Copy Propagation.
 */

@trusted
private void flowaecp(ref GlobalOptimizer go, ref BlockOpt bo)
{
    aecpgenkill(go, bo);   // Compute Bgen and Bkill for AEs or CPs
    if (go.exptop <= 1)        /* if no expressions                    */
        return;

    /* The transfer equation is:                    */
    /*      Bin = & Bout(all predecessors P of B)   */
    /*      Bout = (Bin - Bkill) | Bgen             */
    /* Using Ullman's algorithm:                    */

    vec_clear(bo.startblock.Bin);
    vec_copy(bo.startblock.Bout,bo.startblock.Bgen); /* these never change */
    if (bo.startblock.bc == BC.iftrue)
        vec_copy(bo.startblock.Bout2,bo.startblock.Bgen2); // these never change

    /* For all blocks except startblock     */
    foreach (b; bo.dfo[1 .. $])
    {
        vec_set(b.Bin);        /* Bin = all expressions        */

        /* Bout = (Bin - Bkill) | Bgen  */
        vec_sub(b.Bout,b.Bin,b.Bkill);
        vec_orass(b.Bout,b.Bgen);
        if (b.bc == BC.iftrue)
        {
            vec_sub(b.Bout2,b.Bin,b.Bkill2);
            vec_orass(b.Bout2,b.Bgen2);
        }
    }

    vec_t tmp = vec_calloc(go.exptop);
    bool anychng;
    Dirty dirty;                // only a change to the Bout of a predecessor changes Bin
    dirty.init(bo.dfo.length);
    do
    {
        anychng = false;

        // For all blocks except startblock
        foreach (i, b; bo.dfo[1 .. $])
        {
            if (!dirty.p[i + 1])
                continue;
            dirty.p[i + 1] = false;

            // Bin = & of Bout of all predecessors
            // Bout = (Bin - Bkill) | Bgen

            bool first = true;
            foreach (bp; b.Bpred[])
            {
                if (bp.bc == BC.iftrue && bp.Bsucc[0] != b)
                {
                    if (first)
                        vec_copy(b.Bin,bp.Bout2);
                    else
                        vec_andass(b.Bin,bp.Bout2);
                }
                else
                {
                    if (first)
                        vec_copy(b.Bin,bp.Bout);
                    else
                        vec_andass(b.Bin,bp.Bout);
                }
                first = false;
            }
            assert(!first);     // it must have had predecessors

            if (b.bc == BC.jcatch || b.bc == BC.lpad)
            {
                /* An exception enters a handler from anywhere in the body of
                 * its try. Set Bin to 0 to account for:
                    void* pstart = p;
                    try
                    {
                        p = null; // account for this
                        throw;
                    }
                    catch (Throwable o) { assert(p != pstart); }
                */
                vec_clear(b.Bin);
            }

            bool changed;
            vec_sub(tmp,b.Bin,b.Bkill);
            vec_orass(tmp,b.Bgen);
            if (!vec_equal(tmp,b.Bout))
            {   // Swap Bout and tmp instead of
                // copying tmp over Bout
                vec_t v = tmp;
                tmp = b.Bout;
                b.Bout = v;
                changed = true;
            }

            if (b.bc == BC.iftrue)
            {   // Bout2 = (Bin - Bkill2) | Bgen2
                vec_sub(tmp,b.Bin,b.Bkill2);
                vec_orass(tmp,b.Bgen2);
                if (!vec_equal(tmp,b.Bout2))
                {   // Swap Bout2 and tmp instead of
                    // copying tmp over Bout2
                    vec_t v = tmp;
                    tmp = b.Bout2;
                    b.Bout2 = v;
                    changed = true;
                }
            }
            if (changed)
            {
                anychng = true;
                dirty.mark(bo, b.Bsucc[]);
            }
        }
    } while (anychng);
    dirty.free();
    vec_free(tmp);
}

/***************************************
 * Find the copies with `s` as an operand, valid after flowcp().
 * Params:
 *      s = symbol
 *      list = set to the go.expnod[] indices of the copies, in increasing order
 * Returns:
 *      false if `s` is not in globsym[], so the copies are not indexed
 */
@trusted
bool copiesOf(const Symbol* s, out const(uint)[] list)
{
    const si = localIndex(s);
    if (si == size_t.max)
        return false;
    list = killIndex.symList[killIndex.symStart[si] .. killIndex.symStart[si + 1]];
    return true;
}

/* Where the elems that can make a copy available or not are, for flowcpBit()
 */
private struct CopyBlocks
{
    bool valid;                 // built for the current flowcp()

    /* For each globsym[] index i, defList[defStart[i] .. defStart[i + 1]] are the
     * bo.dfo[] indices of the blocks with an unambiguous definition of globsym[i]
     */
    Barray!uint defStart;
    Barray!uint defList;

    Barray!bool ambig;          // for each block, whether it has an ambiguous definition
    Barray!bool asmish;         // for each block, whether it has an OPasm or OPddtor
    Barray!uint copyBlock;      // for each go.expnod[] index, the block of the copy
}

private __gshared CopyBlocks copyBlocks;

@trusted
private void buildCopyBlocks(ref GlobalOptimizer go, ref BlockOpt bo)
{
    alias cb = copyBlocks;
    const nblocks = bo.dfo.length;
    const nsyms = globsym.length;
    cb.ambig.setLength(nblocks);
    cb.ambig[][] = false;
    cb.asmish.setLength(nblocks);
    cb.asmish[][] = false;
    cb.copyBlock.setLength(go.exptop);
    cb.copyBlock[][] = uint.max;

    Barray!ulong pairs;         // symbol index in the high half, block index in the low half
    void walk(elem* n, uint bi)
    {
        while (1)
        {
            const op = n.Eoper;
            if (op == OPasm || op == OPddtor)
                cb.asmish[bi] = true;
            if (OTdef(op))
            {
                if (!Eunambig(n))
                    cb.ambig[bi] = true;
                else
                {
                    const si = localIndex(n.E1.Vsym);
                    if (si != size_t.max)
                        pairs.push((cast(ulong)si << 32) | bi);
                }
            }
            if ((op == OPeq || op == OPstreq) && n.Eexp)
                cb.copyBlock[n.Eexp] = bi;
            if (OTbinary(op))
            {
                walk(n.E2, bi);
                n = n.E1;
            }
            else if (OTunary(op))
                n = n.E1;
            else
                break;
        }
    }
    foreach (i, b; bo.dfo[])
    {
        if (b.Belem)
            walk(b.Belem, cast(uint)i);
    }

    cb.defStart.setLength(nsyms + 1);
    cb.defStart[][] = 0;
    foreach (pr; pairs[])
        ++cb.defStart[cast(size_t)(pr >> 32) + 1];
    foreach (k; 0 .. nsyms)
        cb.defStart[k + 1] += cb.defStart[k];
    cb.defList.setLength(pairs.length);
    foreach (pr; pairs[])
        cb.defList[cb.defStart[cast(size_t)(pr >> 32)]++] = cast(uint)pr;
    foreach_reverse (k; 0 .. nsyms)
        cb.defStart[k + 1] = cb.defStart[k];
    cb.defStart[0] = 0;
    pairs.dtor();
    cb.valid = true;
}

/***************************************
 * Returns: the bo.dfo[] index of the block with copy go.expnod[j], valid after flowcp()
 */
@trusted
uint copyBlockOf(ref GlobalOptimizer go, ref BlockOpt bo, uint j)
{
    if (!copyBlocks.valid)
        buildCopyBlocks(go, bo);
    return copyBlocks.copyBlock[j];
}

/***************************************
 * Recompute after flowcp() whether copy go.expnod[j] reaches the start of each
 * block, as flowcp() would compute it for the current elem trees. The data flow
 * of each copy is independent of the others, so this is the same as rerunning
 * flowcp() when only copy j has changed.
 * Params:
 *      go = global optimizer state, with go.defkill updated for copy j
 *      bo = blocks, in bo.dfo[] order
 *      j = go.expnod[] index of the copy
 *      ins = for each block in bo.dfo[], the copies reaching its start; bit j is updated
 */
@trusted
void flowcpBit(ref GlobalOptimizer go, ref BlockOpt bo, uint j, vec_t[] ins)
{
    const elem* c = go.expnod[j];
    const Symbol* s1 = c.E1.Vsym;
    const Symbol* s2 = c.E2.Vsym;
    const bool defkilled = vec_testbit(j, go.defkill) != 0;

    /* GEN and KILL of copy j for elem n, following accumaecpx()
     */
    void accum(elem* n, ref bool gen, ref bool kill)
    {
        elem* t;
        const op = n.Eoper;
        switch (op)
        {
            case OPvar:
            case OPconst:
            case OPrelconst:
                return;

            case OPcolon:
            case OPcolon2:
            {
                bool gl, kl, gr, kr;
                accum(n.E1, gl, kl);
                accum(n.E2, gr, kr);
                kill |= kl | kr;
                gen = ((gen && !kl) || gl) && ((gen && !kr) || gr);
                break;
            }

            case OPandand:
            case OPoror:
            {
                accum(n.E1, gen, kill);
                bool gr, kr;
                accum(n.E2, gr, kr);
                if (el_returns(n.E2))
                {
                    kill |= kr;
                    gen = gen && ((gen && !kr) || gr);
                }
                break;
            }

            case OPddtor:
            case OPasm:
                kill = true;
                gen = false;
                return;

            case OPeq:
            case OPstreq:
                accum(n.E2, gen, kill);
                goto case OPnegass;

            case OPnegass:
                accum(n.E1, gen, kill);
                t = n.E1;
                break;

            case OPvp_fp:
            case OPcvp_fp:
                break;

            case OPprefetch:
                accum(n.E1, gen, kill);
                break;

            default:
                if (OTunary(op))
                    accum(n.E1, gen, kill);
                else if (OTbinary(op))
                {
                    if (OTrtol(op) && ERTOL(n))
                    {
                        accum(n.E2, gen, kill);
                        accum(n.E1, gen, kill);
                    }
                    else
                    {
                        accum(n.E1, gen, kill);
                        accum(n.E2, gen, kill);
                    }
                    if (OTassign(op))
                        t = n.E1;
                }
                break;
        }

        if (!OTdef(op))
            return;
        if (!Eunambig(n))
        {
            if (defkilled)
            {
                kill = true;
                gen = false;
            }
        }
        else if (t.Vsym == s1 || t.Vsym == s2)
        {
            kill = true;
            gen = false;
        }
        if (n.Eexp == j)
        {
            gen = true;
            kill = false;
        }
    }

    /* GEN and KILL of each block, the second ones for the false branch of a BC.iftrue
     */
    const nblocks = bo.dfo.length;
    auto gen = cast(bool*)calloc(nblocks, 8);
    if (!gen)
        err_nomem();
    scope (exit) free(gen);
    bool* kill = gen + nblocks;
    bool* gen2 = kill + nblocks;
    bool* kill2 = gen2 + nblocks;
    bool* bin = kill2 + nblocks;
    bool* bout = bin + nblocks;
    bool* bout2 = bout + nblocks;

    /* Only the blocks with a definition of an operand of copy j, an ambiguous
     * definition killing it, an OPasm or OPddtor, or copy j itself can have a
     * GEN or KILL of it
     */
    if (!copyBlocks.valid)
        buildCopyBlocks(go, bo);
    alias cb = copyBlocks;
    bool* walkBlock = cast(bool*)calloc(nblocks, 1);
    if (!walkBlock)
        err_nomem();
    scope (exit) free(walkBlock);
    bool all;
    const(Symbol)*[2] operands = [s1, s2];
    foreach (sym; operands)
    {
        const si = localIndex(sym);
        if (si == size_t.max)
            all = true;
        else
            foreach (bi; cb.defList[cb.defStart[si] .. cb.defStart[si + 1]])
                walkBlock[bi] = true;
    }
    foreach (i; 0 .. nblocks)
    {
        if (all || cb.asmish[i] || (defkilled && cb.ambig[i]))
            walkBlock[i] = true;
    }
    if (cb.copyBlock[j] != uint.max)
        walkBlock[cb.copyBlock[j]] = true;

    foreach (i, b; bo.dfo[])
    {
        assert(b.Bdfoidx == i);
        if (!walkBlock[i] && b.bc != BC.asm_)
            continue;           // GEN and KILL are 0
        bool g, k;
        switch (b.bc)
        {
            case BC.iftrue:
            {
                elem* e;
                for (e = b.Belem; e.Eoper == OPcomma; e = e.E2)
                    accum(e.E1, g, k);
                if (e.Eoper == OPandand || e.Eoper == OPoror)
                {
                    accum(e.E1, g, k);
                    bool gr, kr;
                    accum(e.E2, gr, kr);

                    // the same combination as aecpgenkill()
                    const k1 = k || kr;
                    const g1 = g && ((g && !kr) || gr);
                    const k2 = (k && !gr) || kr;
                    const g2 = (g && !kr) || gr;
                    if (e.Eoper == OPandand)
                    {
                        gen[i] = g2; kill[i] = k2;
                        gen2[i] = g1; kill2[i] = k1;
                    }
                    else
                    {
                        gen[i] = g1; kill[i] = k1;
                        gen2[i] = g2; kill2[i] = k2;
                    }
                }
                else
                {
                    accum(e, g, k);
                    gen[i] = gen2[i] = g;
                    kill[i] = kill2[i] = k;
                }
                break;
            }

            case BC.asm_:
                kill[i] = true;
                break;

            default:
                if (b.Belem)
                    accum(b.Belem, g, k);
                gen[i] = g;
                kill[i] = k;
                break;
        }
    }

    // The same iteration as flowaecp()
    bout[0] = gen[0];
    bout2[0] = gen2[0];
    foreach (i; 1 .. nblocks)
    {
        bin[i] = true;
        bout[i] = !kill[i] || gen[i];
        bout2[i] = !kill2[i] || gen2[i];
    }
    bool anychng;
    do
    {
        anychng = false;
        foreach (i, b; bo.dfo[1 .. $])
        {
            ++i;
            bool v = true;
            foreach (bp; b.Bpred[])
            {
                const p = bp.Bdfoidx;
                assert(p < nblocks && bo.dfo[p] is bp);
                v &= (bp.bc == BC.iftrue && bp.Bsucc[0] != b) ? bout2[p] : bout[p];
            }
            if (b.bc == BC.jcatch || b.bc == BC.lpad)
                v = false;      // entered from anywhere in the body of its try
            bin[i] = v;
            const o = (v && !kill[i]) || gen[i];
            const o2 = (v && !kill2[i]) || gen2[i];
            if (o != bout[i] || (b.bc == BC.iftrue && o2 != bout2[i]))
                anychng = true;
            bout[i] = o;
            bout2[i] = o2;
        }
    } while (anychng);

    foreach (i; 0 .. nblocks)
    {
        if (bin[i])
            vec_setbit(j, ins[i]);
        else
            vec_clearbit(j, ins[i]);
    }
}


/***********************************
 * Compute Bgen and Bkill for AEs, CPs, and VBEs.
 */

/* Indexes of go.expnod[] that let accumaecpx() find the elems a definition kills
 * without looking at every elem
 */
private struct KillIndex
{
    /* For each globsym[] index i, symList[symStart[i] .. symStart[i + 1]] are the
     * go.expnod[] indices of the elems that a definition of globsym[i] kills directly
     */
    Barray!uint symStart;
    Barray!uint symList;

    /* For each go.expnod[] index c, parentList[parentStart[c] .. parentStart[c + 1]]
     * are the go.expnod[] indices of the AEs that have expnod[c] as an operand
     */
    Barray!uint parentStart;
    Barray!uint parentList;

    Barray!uint mark;           // the round in which each elem was last killed
    uint round;
    Barray!uint work;
}

private __gshared KillIndex killIndex;

/* Returns: the globsym[] index of `s`, or size_t.max if it is not in it
 */
@trusted
private size_t localIndex(const Symbol* s)
{
    const si = s.Ssymnum;
    return si < globsym.length && globsym[si] is s ? si : size_t.max;
}

/* Build `killIndex` for the elems in go.expnod[]
 */
@trusted
private void buildKillIndex(ref GlobalOptimizer go)
{
    alias ki = killIndex;
    const nsyms = globsym.length;
    const nexp = go.exptop;

    /* Fill start[] and list[] with the pairs (key, value) that each(dg) passes to dg,
     * the values of each key being in list[start[key] .. start[key + 1]]
     */
    static void group(ref Barray!uint start, ref Barray!uint list, size_t nkeys,
        scope void delegate(scope void delegate(size_t key, uint value) nothrow) nothrow each)
    {
        start.setLength(nkeys + 1);
        start[][] = 0;
        each((key, value) { ++start[key + 1]; });
        foreach (k; 0 .. nkeys)
            start[k + 1] += start[k];
        list.setLength(start[nkeys]);
        each((key, value) { list[start[key]++] = value; });
        foreach_reverse (k; 0 .. nkeys)         // restore the starts the stores advanced
            start[k + 1] = start[k];
        start[0] = 0;
    }

    group(ki.symStart, ki.symList, nsyms, (scope add) {
        foreach (uint i; 1 .. nexp)
        {
            elem* e = go.expnod[i];
            if (go.flowxx == CP)
            {
                const s1 = localIndex(e.E1.Vsym);
                const s2 = localIndex(e.E2.Vsym);
                if (s1 != size_t.max)
                    add(s1, i);
                if (s2 != size_t.max && s2 != s1)
                    add(s2, i);
            }
            else if (e.Eoper == OPvar)
            {
                const si = localIndex(e.Vsym);
                if (si != size_t.max)
                    add(si, i);
            }
        }
    });

    group(ki.parentStart, ki.parentList, nexp, (scope add) {
        if (go.flowxx == CP)
            return;
        foreach (uint i; 1 .. nexp)
        {
            elem* e = go.expnod[i];
            const op = e.Eoper;
            if (OTunary(op))
                add(e.E1.Eexp, i);
            else if (OTbinary(op))
            {
                add(e.E1.Eexp, i);
                if (e.E2.Eexp != e.E1.Eexp)
                    add(e.E2.Eexp, i);
            }
        }
    });

    ki.mark.setLength(nexp);
    ki.mark[][] = 0;
    ki.round = 0;
}

@trusted
private void aecpgenkill(ref GlobalOptimizer go, ref BlockOpt bo, bool genkill = true)
{
    block* this_block;

    /********************************
     * Assign cp elems to go.expnod[] (in order of evaluation).
     */
    void asgcpelems(elem* n)
    {
        while (1)
        {
            const op = n.Eoper;
            if (OTunary(op))
            {
                n.Eexp = 0;
                n = n.E1;
                continue;
            }
            else if (OTbinary(op))
            {
                if (ERTOL(n))
                {
                    asgcpelems(n.E2);
                    asgcpelems(n.E1);
                }
                else
                {
                    asgcpelems(n.E1);
                    asgcpelems(n.E2);
                }

                /* look for elem of the form OPvar=OPvar, where they aren't the
                 * same variable.
                 * Don't mix XMM and integer registers.
                 */
                if (isCopy(n))
                {
                    n.Eexp = cast(uint)go.expnod.length;
                    go.expnod.push(n);
                }
                else
                    n.Eexp = 0;
            }
            else
                n.Eexp = 0;
            return;
        }
    }

    /********************************
     * Assign ae and vbe elems to go.expnod[] (in order of evaluation).
     */
    bool asgaeelems(elem* n)
    {
        bool ae;

        assert(n);
        const op = n.Eoper;
        if (OTunary(op))
        {
            ae = asgaeelems(n.E1);
            // Disallow starred references to avoid problems with VBE's
            // being hoisted before tests of an invalid pointer.
            if (go.flowxx == VBE && op == OPind)
            {
                n.Eexp = 0;
                return false;
            }
        }
        else if (OTbinary(op))
        {
            if (ERTOL(n))
                ae = asgaeelems(n.E2) & asgaeelems(n.E1);
            else
                ae = asgaeelems(n.E1) & asgaeelems(n.E2);
        }
        else
            ae = true;

        if (ae && (OTae(op) || isReadNoneCall(n)) && !(n.Ety & (mTYvolatile | mTYshared)) &&
            // Disallow struct AEs, because we can't handle CSEs that are structs
            tybasic(n.Ety) != TYstruct &&
            tybasic(n.Ety) != TYarray)
        {
            n.Eexp = cast(uint)go.expnod.length;       // remember index into go.expnod[]
            go.expnod.push(n);
            if (go.flowxx == VBE)
                go.expblk.push(this_block);
            return true;
        }
        else
        {
            n.Eexp = 0;
            return false;
        }
    }

    go.expnod.setLength(0);             // dump any existing one
    go.expnod.push(null);
    aeCandKILL = null;

    go.expblk.setLength(0);             // dump any existing one
    go.expblk.push(null);

    foreach (b; bo.dfo[])
    {
        if (b.Belem)
        {
            if (go.flowxx == CP)
                asgcpelems(b.Belem);
            else
            {
                this_block = b;    // so asgaeelems knows about this
                asgaeelems(b.Belem);
            }
        }
    }
    go.exptop = cast(uint)go.expnod.length;
    if (go.exptop <= 1)
        return;

    defstarkill(go);                  /* compute go.defkill and go.starkill */
    if (!genkill)
        return;
    buildKillIndex(go);

    static if (0)
    {
        assert(vec_numbits(go.defkill) == go.expnod.length);
        assert(vec_numbits(go.starkill) == go.expnod.length);
        assert(vec_numbits(go.vptrkill) == go.expnod.length);
        dbg_printf("defkill  "); vec_println(go.defkill);
        if (go.starkill)
        {   dbg_printf("starkill "); vec_println(go.starkill);}
        if (go.vptrkill)
        {   dbg_printf("vptrkill "); vec_println(go.vptrkill); }
    }

    foreach (i, b; bo.dfo[])
    {
        /* dump any existing vectors    */
        vec_free(b.Bin);
        vec_free(b.Bout);
        vec_free(b.Bgen);
        vec_free(b.Bkill);
        b.Bgen = vec_calloc(go.expnod.length);
        b.Bkill = vec_calloc(go.expnod.length);
        switch (b.bc)
        {
            case BC.iftrue:
                vec_free(b.Bout2);
                vec_free(b.Bgen2);
                vec_free(b.Bkill2);
                elem* e;
                for (e = b.Belem; e.Eoper == OPcomma; e = e.E2)
                    accumaecp(go, b.Bgen,b.Bkill,e.E1);
                if (e.Eoper == OPandand || e.Eoper == OPoror)
                {
                    accumaecp(go, b.Bgen,b.Bkill,e.E1);
                    vec_t Kr = vec_calloc(go.expnod.length);
                    vec_t Gr = vec_calloc(go.expnod.length);
                    accumaecp(go, Gr,Kr,e.E2);

                    // We might or might not have executed E2
                    // KILL1 = KILL | Kr
                    // GEN1 = GEN & ((GEN - Kr) | Gr)

                    // We definitely executed E2
                    // KILL2 = (KILL - Gr) | Kr
                    // GEN2 = (GEN - Kr) | Gr

                    const uint dim = cast(uint)vec_dim(Kr);
                    vec_t KILL = b.Bkill;
                    vec_t GEN = b.Bgen;

                    foreach (j; 0 .. dim)
                    {
                        vec_base_t KILL1 = KILL[j] | Kr[j];
                        vec_base_t GEN1  = GEN[j] & ((GEN[j] & ~Kr[j]) | Gr[j]);

                        vec_base_t KILL2 = (KILL[j] & ~Gr[j]) | Kr[j];
                        vec_base_t GEN2  = (GEN[j] & ~Kr[j]) | Gr[j];

                        KILL[j] = KILL1;
                        GEN[j] = GEN1;
                        Kr[j] = KILL2;
                        Gr[j] = GEN2;
                    }

                    if (e.Eoper == OPandand)
                    {   b.Bkill  = Kr;
                        b.Bgen   = Gr;
                        b.Bkill2 = KILL;
                        b.Bgen2  = GEN;
                    }
                    else
                    {   b.Bkill  = KILL;
                        b.Bgen   = GEN;
                        b.Bkill2 = Kr;
                        b.Bgen2  = Gr;
                    }
                }
                else
                {
                    accumaecp(go, b.Bgen,b.Bkill,e);
                    b.Bgen2 = vec_clone(b.Bgen);
                    b.Bkill2 = vec_clone(b.Bkill);
                }
                b.Bout2 = vec_calloc(go.expnod.length);
                break;

            case BC.asm_:
                vec_set(b.Bkill);              // KILL everything
                vec_clear(b.Bgen);             // GEN nothing
                break;

            default:
                // calculate GEN & KILL vectors
                if (b.Belem)
                    accumaecp(go, b.Bgen,b.Bkill,b.Belem);
                break;
        }
        static if (0)
        {
            printf("block %d Bgen ",i); vec_println(b.Bgen);
            printf("       Bkill "); vec_println(b.Bkill);
        }
        b.Bin = vec_calloc(go.expnod.length);
        b.Bout = vec_calloc(go.expnod.length);
    }
}

/********************************
 * Compute defkill, starkill and vptrkill vectors.
 *      starkill:       set of expressions killed when a variable is
 *                      changed that somebody could be pointing to.
 *                      (not needed for cp)
 *                      starkill is a subset of defkill.
 *      defkill:        set of expressions killed by an ambiguous
 *                      definition.
 *      vptrkill:       set of expressions killed by an access to a vptr.
 */

@trusted
private void defstarkill(ref GlobalOptimizer go)
{
    const exptop = go.exptop;
    vec_recycle(go.defkill, exptop);
    if (go.flowxx == CP)
    {
        vec_recycle(go.starkill, 0);
        vec_recycle(go.vptrkill, 0);
    }
    else
    {
        vec_recycle(go.starkill, exptop);      // and create new ones
        vec_recycle(go.vptrkill, exptop);      // and create new ones
    }

    if (!exptop)
        return;

    auto defkill = go.defkill;

    if (go.flowxx == CP)
    {
        foreach (i, n; go.expnod[1 .. exptop])
        {
            const op = n.Eoper;
            assert(op == OPeq || op == OPstreq);
            assert(n.E1.Eoper==OPvar && n.E2.Eoper==OPvar);

            // Set bit in defkill if either the left or the
            // right variable is killed by an ambiguous def.

            if (Symbol_isAffected(*n.E1.Vsym) ||
                Symbol_isAffected(*n.E2.Vsym))
            {
                vec_setbit(i + 1,defkill);
            }
        }
    }
    else
    {
        auto starkill = go.starkill;
        auto vptrkill = go.vptrkill;

        foreach (j, n; go.expnod[1 .. exptop])
        {
            const i = j + 1;
            const op = n.Eoper;
            switch (op)
            {
                case OPvar:
                    // no assignment changes the address of a function
                    if (Symbol_isAffected(*n.Vsym) && !tyfunc(n.Vsym.ty()))
                        vec_setbit(i,defkill);
                    break;

                case OPind:         // if a 'starred' ref
                    if (tybasic(n.E1.Ety) == TYimmutPtr)
                        break;
                    goto case OPstrlen;

                case OPstrlen:
                case OPstrcmp:
                case OPmemcmp:
                case OPbt:          // OPbt is like OPind
                    vec_setbit(i,defkill);
                    vec_setbit(i,starkill);
                    break;

                case OPvp_fp:
                case OPcvp_fp:
                    vec_setbit(i,vptrkill);
                    goto Lunary;

                default:
                    if (OTunary(op))
                    {
                    Lunary:
                        if (vec_testbit(n.E1.Eexp,defkill))
                            vec_setbit(i,defkill);
                        if (vec_testbit(n.E1.Eexp,starkill))
                            vec_setbit(i,starkill);
                    }
                    else if (OTbinary(op))
                    {
                        if (vec_testbit(n.E1.Eexp,defkill) ||
                            vec_testbit(n.E2.Eexp,defkill))
                                vec_setbit(i,defkill);
                        if (vec_testbit(n.E1.Eexp,starkill) ||
                            vec_testbit(n.E2.Eexp,starkill))
                                vec_setbit(i,starkill);
                    }
                    break;
            }
        }
    }
}

/********************************
 * Compute GEN and KILL vectors only for AEs.
 * defkill and starkill are assumed to be already set up correctly.
 * go.expnod[] is assumed to be set up correctly.
 */

@trusted
void genkillae(ref GlobalOptimizer go, ref BlockOpt bo)
{
    go.flowxx = AE;
    assert(go.exptop > 1);
    foreach (b; bo.dfo[])
    {
        assert(b);
        vec_clear(b.Bgen);
        vec_clear(b.Bkill);
        if (b.Belem)
            accumaecp(go, b.Bgen,b.Bkill,b.Belem);
        else if (b.bc == BC.asm_)
        {
            vec_set(b.Bkill);          // KILL everything
            vec_clear(b.Bgen);         // GEN nothing
        }
    }
}

/************************************
 * Allocate and compute KILL and GEN vectors for a elem.
 * Params:
 *      gen = GEN vector to create and compute
 *      kill = KILL vector to create and compute
 *      e = elem used to conpute GEN and KILL
 *      exptop = number of elems in vectors
 */

@trusted
private void aecpelem(ref GlobalOptimizer go, out vec_t gen, out vec_t kill, elem* n, uint exptop)
{
    gen = vec_calloc(exptop);
    kill = vec_calloc(exptop);
    if (n)
    {
        if (go.flowxx == VBE)
            accumvbe(go, gen,kill,n);
        else
            accumaecp(go, gen,kill,n);
    }
}

/*************************************
 * Accumulate GEN and KILL sets for AEs and CPs for this elem.
 */

private __gshared
{
    vec_t GEN;       // use static copies to save on parameter passing
    vec_t KILL;

    /* For AEs: the AEs that may be in no KILL while an operand is, which a
     * definition kills along with the uses of the variable it defines.
     * aeCand[aeCandBase .. $] are those of the current GEN and KILL.
     */
    Barray!uint aeCand;
    size_t aeCandBase;
    uint aeDepth;               // nesting of accumaecp() calls
    vec_t aeCandKILL;           // the KILL aeCand[0 .. $] was last kept for
}

/* Returns: whether an operand of AE go.expnod[i] is in KILL
 */
@trusted
private bool killedOperand(ref GlobalOptimizer go, uint i)
{
    elem* e = go.expnod[i];
    const op = e.Eoper;
    if (OTunary(op))
        return vec_testbit(e.E1.Eexp, KILL) != 0;
    if (OTbinary(op))
        return vec_testbit(e.E1.Eexp, KILL) || vec_testbit(e.E2.Eexp, KILL);
    return false;
}

/* Elem b has been added to GEN, so removed from KILL
 */
@trusted
private void noteGen(ref GlobalOptimizer go, uint b)
{
    if (go.flowxx == AE && killedOperand(go, b))
        aeCand.push(b);
}

/* KILL |= x, noting the AEs whose operands that kills
 */
@trusted
private void killBits(ref GlobalOptimizer go, const vec_t x)
{
    if (go.flowxx != AE)
    {
        vec_orass(KILL, x);
        return;
    }
    /* Only the AEs that end up outside KILL with an operand in it are noted
     */
    alias ki = killIndex;
    killAdded.setLength(0);
    foreach (w; 0 .. vec_dim(KILL))
    {
        if (auto added = x[w] & ~KILL[w])
        {
            killAdded.push(w);
            killAdded.push(added);
            KILL[w] |= added;
        }
    }
    for (size_t j = 0; j < killAdded.length; j += 2)
    {
        const w = killAdded[j];
        auto added = killAdded[j + 1];
        while (added)
        {
            import core.bitop : bsf;
            const c = cast(uint)(w * VECBITS + bsf(added));
            added &= added - 1;
            if (c < go.exptop)
                foreach (p; ki.parentList[ki.parentStart[c] .. ki.parentStart[c + 1]])
                {
                    if (!vec_testbit(p, KILL))
                        aeCand.push(p);
                }
        }
    }
}

private __gshared Barray!vec_base_t killAdded;  // for killBits(): word index, then the bits it added

@trusted
private void accumaecp(ref GlobalOptimizer go, vec_t g,vec_t k,elem* n)
{   vec_t GENsave,KILLsave;

    assert(g && k);
    GENsave = GEN;
    KILLsave = KILL;
    GEN = g;
    KILL = k;
    const baseSave = aeCandBase;
    if (go.flowxx == AE)
    {
        if (aeDepth == 0)
        {
            if (k !is aeCandKILL)
            {
                /* Find the AEs in no KILL with an operand that is
                 */
                aeCand.setLength(0);
                if (!vec_disjoint(k, k))
                {
                    foreach (uint i; 1 .. go.exptop)
                    {
                        if (!vec_testbit(i, KILL) && killedOperand(go, i))
                            aeCand.push(i);
                    }
                }
            }
            aeCandKILL = k;
        }
        aeCandBase = aeDepth ? aeCand.length : 0;
        ++aeDepth;
    }
    accumaecpx(go, n);
    if (go.flowxx == AE)
    {
        --aeDepth;
        if (aeDepth)
            aeCand.setLength(aeCandBase);
        aeCandBase = baseSave;
    }
    GEN = GENsave;
    KILL = KILLsave;
}

/* Whether to check that the kills found through `killIndex` are those found by
 * looking at every elem, set by the environment variable DMD_CHECK_KILL_INDEX
 */
private __gshared int checkKillIndexState = -1;

@trusted
private bool checkKillIndex()
{
    if (checkKillIndexState < 0)
        checkKillIndexState = getenv("DMD_CHECK_KILL_INDEX") !is null;
    return checkKillIndexState != 0;
}

/* Abort if the KILL and GEN computed through `killIndex` differ from `checkKILL`
 * and `checkGEN`, which are freed
 */
@trusted
private void checkKills(vec_t checkKILL, vec_t checkGEN)
{
    if (!vec_equal(checkKILL, KILL) || !vec_equal(checkGEN, GEN))
    {
        import dmd.backend.debugprint : oper_str;
        fprintf(stderr, "kill index mismatch in %s flowxx=%d\n", funcsym_p ? funcsym_p.Sident.ptr : "?".ptr, go.flowxx);
        foreach (uint i; 1 .. go.exptop)
        {
            const ok = vec_testbit(i, checkKILL) != 0, nk = vec_testbit(i, KILL) != 0;
            const og = vec_testbit(i, checkGEN) != 0, ng = vec_testbit(i, GEN) != 0;
            if (ok != nk || og != ng)
            {
                elem* e = go.expnod[i];
                fprintf(stderr, " i=%u op=%s oldKILL=%d newKILL=%d oldGEN=%d newGEN=%d", i, oper_str(e.Eoper), ok, nk, og, ng);
                if (!OTleaf(e.Eoper))
                {
                    const c1 = e.E1.Eexp;
                    fprintf(stderr, " E1.Eexp=%u(K%d) ", c1, vec_testbit(c1, checkKILL) != 0);
                    if (OTbinary(e.Eoper)) fprintf(stderr, " E2.Eexp=%u(K%d)", e.E2.Eexp, vec_testbit(e.E2.Eexp, checkKILL) != 0);
                }
                fprintf(stderr, "\n");
            }
        }
        abort();
    }
    vec_free(checkKILL);
    vec_free(checkGEN);
}

@trusted
private void accumaecpx(ref GlobalOptimizer go, elem* n)
{
    elem* t;

    assert(n);
    elem_debug(n);
    const op = n.Eoper;

    switch (op)
    {
        case OPvar:
        case OPconst:
        case OPrelconst:
            if ((go.flowxx == AE) && n.Eexp)
            {   uint b;
                debug assert(go.expnod[n.Eexp] == n);
                b = n.Eexp;
                vec_setclear(b,GEN,KILL);
            }
            return;

        case OPcolon:
        case OPcolon2:
        {   vec_t Gl,Kl,Gr,Kr;

            aecpelem(go, Gl,Kl, n.E1, go.exptop);
            aecpelem(go, Gr,Kr, n.E2, go.exptop);

            /* KILL |= Kl | Kr           */
            /* GEN =((GEN - Kl) | Gl) &  */
            /*     ((GEN - Kr) | Gr)     */

            killBits(go, Kl);
            killBits(go, Kr);

            vec_sub(Kl,GEN,Kl);
            vec_sub(Kr,GEN,Kr);
            vec_orass(Kl,Gl);
            vec_orass(Kr,Gr);
            vec_and(GEN,Kl,Kr);

            vec_free(Gl);
            vec_free(Gr);
            vec_free(Kl);
            vec_free(Kr);
            break;
        }

        case OPandand:
        case OPoror:
        {   vec_t Gr,Kr;

            accumaecpx(go, n.E1);
            aecpelem(go, Gr,Kr, n.E2, go.exptop);

            if (el_returns(n.E2))
            {
                // KILL |= Kr
                // GEN &= (GEN - Kr) | Gr

                killBits(go, Kr);
                vec_sub(Kr,GEN,Kr);
                vec_orass(Kr,Gr);
                vec_andass(GEN,Kr);
            }

            vec_free(Gr);
            vec_free(Kr);
            break;
        }

        case OPddtor:
        case OPasm:
            assert(!n.Eexp);                   // no ASM available expressions
            vec_set(KILL);                      // KILL everything
            vec_clear(GEN);                     // GEN nothing
            if (go.flowxx == AE)
                aeCand.setLength(aeCandBase);   // every AE is in KILL
            return;

        case OPeq:
        case OPstreq:
            accumaecpx(go, n.E2);
            goto case OPnegass;

        case OPnegass:
            accumaecpx(go, n.E1);
            t = n.E1;
            break;

        case OPvp_fp:
        case OPcvp_fp:                          // if vptr access
            if ((go.flowxx == AE) && n.Eexp)
                killBits(go, go.vptrkill);         // kill all other vptr accesses
            break;

        case OPprefetch:
            accumaecpx(go, n.E1);                  // don't check E2
            break;

        default:
            if (OTunary(op))
            {
        case OPind:                             // most common unary operator
                accumaecpx(go, n.E1);
                debug assert(!OTassign(op));
            }
            else if (OTbinary(op))
            {
                if (OTrtol(op) && ERTOL(n))
                {
                    accumaecpx(go, n.E2);
                    accumaecpx(go, n.E1);
                }
                else
                {
                    accumaecpx(go, n.E1);
                    accumaecpx(go, n.E2);
                }
                if (OTassign(op))               // if assignment operator
                    t = n.E1;
            }
            break;
    }


    /* Do copy propagation stuff first  */

    if (go.flowxx == CP)
    {
        if (!OTdef(op))                         /* if not def elem      */
            return;
        if (!Eunambig(n))                       /* if ambiguous def elem */
        {
            killBits(go, go.defkill);
            vec_subass(GEN,go.defkill);
        }
        else                                    /* unambiguous def elem */
        {
            assert(t.Eoper == OPvar);
            Symbol* s = t.Vsym;                  // ptr to var being def'd
            void killAll(vec_t KILL, vec_t GEN)
            {
                foreach (uint i; 1 .. go.exptop)        // for each ae elem
                {
                    elem* e = go.expnod[i];

                    /* If it could be changed by the definition,     */
                    /* set bit in KILL.                              */

                    if (e.E1.Vsym == s || e.E2.Vsym == s)
                        vec_setclear(i,KILL,GEN);
                }
            }
            const si = localIndex(s);
            if (si == size_t.max)
                killAll(KILL, GEN);
            else
            {
                vec_t checkKILL, checkGEN;
                if (checkKillIndex)
                {
                    checkKILL = vec_clone(KILL);
                    checkGEN = vec_clone(GEN);
                    killAll(checkKILL, checkGEN);
                }
                foreach (i; killIndex.symList[killIndex.symStart[si] .. killIndex.symStart[si + 1]])
                    vec_setclear(i,KILL,GEN);
                if (checkKillIndex)
                    checkKills(checkKILL, checkGEN);
            }
        }

        /* GEN CP elems */
        if (n.Eexp)
        {
            const uint b = n.Eexp;
            vec_setclear(b,GEN,KILL);
        }

        return;
    }

    /* Else Available Expression stuff  */

    if (n.Eexp)
    {
        const uint b = n.Eexp;             // add elem to GEN
        assert(go.expnod[b] == n);
        vec_setclear(b,GEN,KILL);
        noteGen(go, b);
    }
    else if (OTdef(op))                         /* else if definition elem */
    {
        if (!Eunambig(n))                       /* if ambiguous def elem */
        {
            killBits(go, go.defkill);
            vec_subass(GEN,go.defkill);
            if (OTcalldef(op))
            {
                killBits(go, go.vptrkill);
                vec_subass(GEN,go.vptrkill);
            }
        }
        else                                    /* unambiguous def elem */
        {
            assert(t.Eoper == OPvar);
            Symbol* s = t.Vsym;             // idx of var being def'd
            if (!(s.Sflags & SFLdistinct))
            {
                killBits(go, go.starkill);         /* kill all 'starred' refs */
                vec_subass(GEN,go.starkill);
            }
            void killAll(vec_t KILL, vec_t GEN)
            {
                foreach (uint i; 1 .. go.exptop)        // for each ae elem
                {
                    elem* e = go.expnod[i];
                    const int eop = e.Eoper;

                    /* If it could be changed by the definition,     */
                    /* set bit in KILL.                              */
                    if (eop == OPvar)
                    {
                        if (e.Vsym != s)
                            continue;
                    }
                    else if (OTunary(eop))
                    {
                        if (!vec_testbit(e.E1.Eexp,KILL))
                            continue;
                    }
                    else if (OTbinary(eop))
                    {
                        if (!vec_testbit(e.E1.Eexp,KILL) &&
                            !vec_testbit(e.E2.Eexp,KILL))
                            continue;
                    }
                    else
                            continue;

                    vec_setclear(i,KILL,GEN);
                }
            }
            const si = localIndex(s);
            if (si == size_t.max)
            {
                killAll(KILL, GEN);
                aeCand.setLength(aeCandBase);   // no AE outside KILL has an operand in it
            }
            else
            {
                vec_t checkKILL, checkGEN;
                if (checkKillIndex)
                {
                    checkKILL = vec_clone(KILL);
                    checkGEN = vec_clone(GEN);
                    killAll(checkKILL, checkGEN);
                }

                /* Kill the uses of s and the AEs outside KILL with an operand
                 * in it, then the AEs with an operand killed by that
                 */
                alias ki = killIndex;
                if (++ki.round == 0)
                {
                    ki.mark[][] = 0;
                    ki.round = 1;
                }
                ki.work.setLength(0);
                foreach (i; ki.symList[ki.symStart[si] .. ki.symStart[si + 1]])
                {
                    ki.mark[i] = ki.round;
                    vec_setclear(i,KILL,GEN);
                    ki.work.push(i);
                }
                foreach (i; aeCand[aeCandBase .. aeCand.length])
                {
                    if (ki.mark[i] != ki.round && !vec_testbit(i, KILL) && killedOperand(go, i))
                    {
                        ki.mark[i] = ki.round;
                        vec_setclear(i,KILL,GEN);
                        ki.work.push(i);
                    }
                }
                aeCand.setLength(aeCandBase);
                while (ki.work.length)
                {
                    const c = ki.work[ki.work.length - 1];
                    ki.work.setLength(ki.work.length - 1);
                    foreach (p; ki.parentList[ki.parentStart[c] .. ki.parentStart[c + 1]])
                    {
                        if (ki.mark[p] != ki.round)
                        {
                            ki.mark[p] = ki.round;
                            vec_setclear(p,KILL,GEN);
                            ki.work.push(p);
                        }
                    }
                }
                if (checkKillIndex)
                    checkKills(checkKILL, checkGEN);
            }
        }

        /* GEN the lvalue of an assignment operator      */
        if (OTassign(op) && !OTpost(op) && t.Eexp)
        {
            uint b = t.Eexp;

            vec_setclear(b,GEN,KILL);
            noteGen(go, b);
        }
    }
}

/************************* LIVE VARIABLES **********************/

/*********************************
 * Do live variable analysis (LVs).
 * A variable is 'live' at some point if there is a
 * subsequent use of it before a redefinition.
 * Binlv = the set of variables live at the beginning of B.
 * Boutlv = the set of variables live at the end of B.
 * Bgen = set of variables used before any definition in B.
 * Bkill = set of variables unambiguously defined before
 *       any use in B.
 * Note that Bgen & Bkill = 0.
 */

@trusted
void flowlv(ref BlockOpt bo)
{
    lvgenkill(bo);            /* compute Bgen and Bkill for LVs.      */
    //assert(globsym.length);  /* should be at least some symbols      */

    /* Create a vector of all the variables that are live on exit   */
    /* from the function.                                           */

    vec_t livexit = vec_calloc(globsym.length);
    foreach (i; 0 .. globsym.length)
    {
        if (globsym[i].Sflags & SFLlivexit)
            vec_setbit(i,livexit);
    }

    /* The transfer equation is:                            */
    /*      Bin = (Bout - Bkill) | Bgen                     */
    /*      Bout = union of Bin of all successors to B.     */
    /* Using Ullman's algorithm:                            */

    foreach (b; bo.dfo[])
    {
        vec_copy(b.Binlv, b.Bgen);   // Binlv = Bgen
    }

    vec_t tmp = vec_calloc(globsym.length);

    /* A block that may throw does so from anywhere in it, before or after its
     * definitions, so what is live on entry to the handlers it may throw to is
     * live on entry to and exit from it, but for the registers a landing pad
     * receives the exception in, which only the landing pad defines
     */
    ehEdges.compute(bo);
    vec_t ehlv;
    vec_t notPseudo;
    if (ehEdges.any)
    {
        ehlv = vec_calloc(globsym.length);
        notPseudo = vec_calloc(globsym.length);
        foreach (i, s; globsym[])
        {
            if (s.Sclass != SC.pseudo)
                vec_setbit(i, notPseudo);
        }
    }

    uint cnt = 0;
    bool anychng;
    Dirty dirty;                // only a change to the Binlv of a successor changes Boutlv
    dirty.init(bo.dfo.length);
    do
    {
        anychng = false;

        /* For each block B in reverse DFO order        */
        foreach_reverse (i, b; bo.dfo[])
        {
            if (!dirty.p[i])
                continue;
            dirty.p[i] = false;
            /* Bout = union of Bins of all successors to B. */
            bool first = true;
            foreach (bl; b.Bsucc[])
            {
                const inlv = bl.Binlv;
                if (first)
                    vec_copy(b.Boutlv, inlv);
                else
                    vec_orass(b.Boutlv, inlv);
                first = false;
            }

            if (first) /* no successors, Boutlv = livexit */
            {   //assert(b.bc==BC.ret||b.bc==BC.retexp||b.bc==BC.exit);
                vec_copy(b.Boutlv,livexit);
            }

            /* Bin = (Bout - Bkill) | Bgen                  */
            vec_sub(tmp,b.Boutlv,b.Bkill);
            vec_orass(tmp,b.Bgen);
            if (ehEdges.mayThrowAt(b))
            {
                vec_clear(ehlv);
                ehEdges.forHandlers(bo, b, (block* h) { vec_orass(ehlv, h.Binlv); });
                vec_andass(ehlv, notPseudo);
                vec_orass(b.Boutlv, ehlv);
                vec_orass(tmp, ehlv);
            }
            if (!vec_equal(tmp,b.Binlv))
            {
                anychng = true;
                dirty.mark(bo, b.Bpred[]);
                if (ehEdges.isHandler(b))
                {
                    foreach (g; ehEdges.guardedBy(ehEdges.handlerOf(b)))
                        dirty.p[g] = true;
                }
            }
            vec_copy(b.Binlv,tmp);
        }
        cnt++;
        assert(cnt < 50);
    } while (anychng);

    dirty.free();
    vec_free(ehlv);
    vec_free(notPseudo);
    vec_free(tmp);
    vec_free(livexit);

    static if (0)
    {
        printf("Live variables\n");
        foreach (i, b; dfo[])
        {
            printf("B%d  IN\t", cast(int)i);
            vec_println(b.Binlv);
            printf("   GEN\t");
            vec_println(b.Bgen);
            printf("  KILL\t");
            vec_println(b.Bkill);
            printf("   OUT\t");
            vec_println(b.Boutlv);
        }
    }
}

/***********************************
 * Compute Bgen and Bkill for LVs.
 * Allocate Binlv and Boutlv vectors.
 */

@trusted
private void lvgenkill(ref BlockOpt bo)
{
    /* Compute ambigsym, a vector of all variables that could be    */
    /* referenced by a* e or a call.                                */
    Symbol*[] gsym = globsym[];
    const length = gsym.length;
    vec_t ambigsym = vec_calloc(length);
    foreach (i; 0 .. length)
        if (!(gsym[i].Sflags & SFLdistinct))
            vec_setbit(i,ambigsym);

    static if (0)
    {
        printf("ambigsym\n");
        foreach (i; 0 .. length)
        {
            if (vec_testbit(i, ambigsym))
                printf(" [%d] %s\n", i, gsym[i].Sident.ptr);
        }
    }

    foreach (b; bo.dfo[])
    {
        vec_free(b.Bgen);
        vec_free(b.Bkill);
        lvelem(b.Bgen,b.Bkill, b.Belem, ambigsym, length);
        if (b.bc == BC.asm_)
        {
            vec_set(b.Bgen);
            vec_clear(b.Bkill);
        }

        vec_free(b.Binlv);
        vec_free(b.Boutlv);
        b.Binlv = vec_calloc(length);
        b.Boutlv = vec_calloc(length);
    }

    vec_free(ambigsym);
}

/*****************************
 * Allocate and compute KILL and GEN for live variables.
 * Params:
 *      gen = create and fill in
 *      kill = create and fill in
 *      e = elem used to fill in gen and kill
 *      ambigsym = vector of symbols with ambiguous references
 *      length = number of global symbols
 */

private void lvelem(out vec_t gen, out vec_t kill, const elem* n, const vec_t ambigsym, size_t length)
{
    gen = vec_calloc(length);
    kill = vec_calloc(length);
    if (n && length)
        accumlv(gen, kill, n, ambigsym);
}

/**********************************************
 * Accumulate GEN and KILL sets for LVs for this elem.
 */

@trusted
private void accumlv(vec_t GEN, vec_t KILL, const(elem)* n, const vec_t ambigsym)
{
    assert(GEN && KILL && n);

    while (1)
    {
        elem_debug(n);
        const op = n.Eoper;
        switch (op)
        {
            case OPvar:
                if (symbol_isintab(n.Vsym))
                {
                    const si = n.Vsym.Ssymnum;

                    assert(cast(uint)si < globsym.length);
                    if (!vec_testbit(si,KILL))  // if not in KILL
                        vec_setbit(si,GEN);     // put in GEN
                }
                break;

            case OPcolon:
            case OPcolon2:
            {
                vec_t Gl,Kl,Gr,Kr;
                lvelem(Gl,Kl, n.E1,ambigsym, globsym.length);
                lvelem(Gr,Kr, n.E2,ambigsym, globsym.length);

                /* GEN |= (Gl | Gr) - KILL      */
                /* KILL |= (Kl & Kr) - GEN      */

                vec_orass(Gl,Gr);
                vec_subass(Gl,KILL);
                vec_orass(GEN,Gl);
                vec_andass(Kl,Kr);
                vec_subass(Kl,GEN);
                vec_orass(KILL,Kl);

                vec_free(Gl);
                vec_free(Gr);
                vec_free(Kl);
                vec_free(Kr);
                break;
            }

            case OPandand:
            case OPoror:
            {
                vec_t Gr,Kr;
                accumlv(GEN,KILL,n.E1,ambigsym);
                lvelem(Gr,Kr, n.E2,ambigsym, globsym.length);

                /* GEN |= Gr - KILL     */
                /* KILL |= 0            */

                vec_subass(Gr,KILL);
                vec_orass(GEN,Gr);

                vec_free(Gr);
                vec_free(Kr);
                break;
            }

            case OPasm:
                vec_set(GEN);           /* GEN everything not already KILLed */
                vec_subass(GEN,KILL);
                break;

            case OPcall:
            case OPcallns:
            case OPstrcpy:
            case OPmemcpy:
            case OPmemset:
                debug assert(OTrtol(op));
                accumlv(GEN,KILL,n.E2,ambigsym);
                accumlv(GEN,KILL,n.E1,ambigsym);
                goto L1;

            case OPstrcat:
                debug assert(!OTrtol(op));
                accumlv(GEN,KILL,n.E1,ambigsym);
                accumlv(GEN,KILL,n.E2,ambigsym);
            L1:
                vec_orass(GEN,ambigsym);
                vec_subass(GEN,KILL);
                break;

            case OPeq:
            case OPstreq:
            {
                /* Avoid GENing the lvalue of an =      */
                accumlv(GEN,KILL,n.E2,ambigsym);
                const t = n.E1;
                if (t.Eoper != OPvar)
                    accumlv(GEN,KILL,t.E1,ambigsym);
                else /* unambiguous assignment */
                {
                    const s = t.Vsym;
                    symbol_debug(s);

                    uint tsz = tysize(t.Ety);
                    if (op == OPstreq)
                        tsz = cast(uint)type_size(n.ET);

                    /* if not GENed already, KILL it */
                    if (symbol_isintab(s) &&
                        !vec_testbit(s.Ssymnum,GEN) &&
                        t.Voffset == 0 &&
                        tsz == type_size(s.Stype)
                       )
                    {
                        // printf("%s\n", s.Sident);
                        assert(cast(uint)s.Ssymnum < globsym.length);
                        vec_setbit(s.Ssymnum,KILL);
                    }
                }
                break;
            }

            case OPmemcmp:
            case OPstrcmp:
            case OPbt:                          // much like OPind
                accumlv(GEN,KILL,n.E1,ambigsym);
                accumlv(GEN,KILL,n.E2,ambigsym);
                vec_orass(GEN,ambigsym);
                vec_subass(GEN,KILL);
                break;

            case OPind:
            case OPucall:
            case OPucallns:
            case OPstrlen:
                accumlv(GEN,KILL,n.E1,ambigsym);

                /* If it was a* p elem, set bits in GEN for all symbols */
                /* it could have referenced, but only if bits in KILL   */
                /* are not already set.                                 */

                vec_orass(GEN,ambigsym);
                vec_subass(GEN,KILL);
                break;

            default:
                if (OTunary(op))
                {
                    n = n.E1;
                    continue;
                }
                else if (OTrtol(op) && ERTOL(n))
                {
                    accumlv(GEN,KILL,n.E2,ambigsym);

                    /* Note that lvalues of op=,i++,i-- elems */
                    /* are GENed.                               */
                    n = n.E1;
                    continue;
                }
                else if (OTbinary(op))
                {
                    accumlv(GEN,KILL,n.E1,ambigsym);
                    n = n.E2;
                    continue;
                }
                break;
        }
        break;
    }
}

/********************* VERY BUSY EXPRESSIONS ********************/

/**********************************************
 * Compute very busy expressions(VBEs).
 * That is,expressions that are evaluated along
 * separate paths.
 * Bin = the set of VBEs at the beginning of B.
 * Bout = the set of VBEs at the end of B.
 * Bgen = set of expressions X+Y such that X+Y is
 *      evaluated before any def of X or Y.
 * Bkill = set of expressions X+Y such that X or Y could
 *      be defined before X+Y is computed.
 * Note that gen and kill are mutually exclusive.
 */

@trusted
void flowvbe(ref GlobalOptimizer go, ref BlockOpt bo)
{
    if (&go) assert(0);
    go.flowxx = VBE;
    aecpgenkill(go, bo);   // compute Bgen and Bkill for VBEs
    if (go.exptop <= 1)     /* if no candidates for VBEs            */
        return;

    /*foreach (uint i; 0 .. go.exptop)
            printf("go.expnod[%d] = 0x%x\n",i,go.expnod[i]);*/

    /* The transfer equation is:                    */
    /*      Bout = & Bin(all successors S of B)     */
    /*      Bin =(Bout - Bkill) | Bgen              */
    /* Using Ullman's algorithm:                    */

    /*printf("defkill = "); vec_println(go.defkill);
    printf("starkill = "); vec_println(go.starkill);*/

    foreach (b; bo.dfo[])
    {
        /*printf("block %p\n",b);
        printf("Bgen = "); vec_println(b.Bgen);
        printf("Bkill = "); vec_println(b.Bkill);*/

        if (b.bc == BC.ret || b.bc == BC.retexp || b.bc == BC.exit)
            vec_clear(b.Bout);
        else
            vec_set(b.Bout);

        /* Bin = (Bout - Bkill) | Bgen  */
        vec_sub(b.Bin,b.Bout,b.Bkill);
        vec_orass(b.Bin,b.Bgen);
    }

    vec_t tmp = vec_calloc(go.exptop);
    bool anychng;
    do
    {
        anychng = false;

        /* for all blocks except return blocks in reverse dfo order */
        foreach_reverse (b; bo.dfo[])
        {
            if (b.bc == BC.ret || b.bc == BC.retexp || b.bc == BC.exit)
                continue;

            /* Bout = & of Bin of all successors */
            bool first = true;
            foreach (bl; b.Bsucc[])
            {
                const vin = bl.Bin;
                if (first)
                    vec_copy(b.Bout, vin);
                else
                    vec_andass(b.Bout, vin);

                first = false;
            }

            assert(!first);     // must have successors

            /* Bin = (Bout - Bkill) | Bgen  */
            vec_sub(tmp,b.Bout,b.Bkill);
            vec_orass(tmp,b.Bgen);
            if (!anychng)
                anychng = !vec_equal(tmp,b.Bin);
            vec_copy(b.Bin,tmp);
        }
    } while (anychng);      /* while any changes occurred to any Bin */
    vec_free(tmp);
}

/*************************************
 * Accumulate GEN and KILL sets for VBEs for this elem.
 */

@trusted
private void accumvbe(ref GlobalOptimizer go, vec_t GEN,vec_t KILL,elem* n)
{
    elem* t;

    assert(GEN && KILL && n);
    const op = n.Eoper;

    switch (op)
    {
        case OPcolon:
        case OPcolon2:
        {
            vec_t Gl,Gr,Kl,Kr;

            aecpelem(go, Gl,Kl, n.E1, go.exptop);
            aecpelem(go, Gr,Kr, n.E2, go.exptop);

            /* GEN |=((Gr - Kl) | (Gl - Kr)) - KILL */
            vec_subass(Gr,Kl);
            vec_subass(Gl,Kr);
            vec_orass(Gr,Gl);
            vec_subass(Gr,KILL);
            vec_orass(GEN,Gr);

            /* KILL |=(Kl | Kr) - GEN       */
            vec_orass(Kl,Kr);
            vec_subass(Kl,GEN);
            vec_orass(KILL,Kl);

            vec_free(Gl);
            vec_free(Kl);
            vec_free(Gr);
            vec_free(Kr);
            break;
        }

        case OPandand:
        case OPoror:
            accumvbe(go, GEN, KILL, n.E1);
            /* WARNING: just so happens that it works this way.     */
            /* Be careful about (b+c)||(b+c) being VBEs, only the   */
            /* first should be GENed. Doing things this way instead */
            /* of (GEN |= Gr - KILL) and (KILL |= Kr - GEN) will    */
            /* ensure this.                                         */
            accumvbe(go, GEN, KILL, n.E2);
            break;

        case OPnegass:
            t = n.E1;
            if (t.Eoper != OPvar)
            {
                accumvbe(go, GEN, KILL, t.E1);
                if (OTbinary(t.Eoper))
                    accumvbe(go, GEN, KILL, t.E2);
            }
            break;

        case OPcall:
        case OPcallns:
            accumvbe(go, GEN, KILL, n.E2);
            goto case OPucall;

        case OPucall:
        case OPucallns:
            t = n.E1;
            // Do not VBE indirect function calls
            if (t.Eoper == OPind)
                t = t.E1;
            accumvbe(go, GEN, KILL, t);
            break;

        case OPasm:                 // if the dreaded OPasm elem
            vec_set(KILL);          // KILL everything
            vec_subass(KILL, GEN);   // except for GENed stuff
            return;

        default:
            if (OTunary(op))
            {
                t = n.E1;
                accumvbe(go, GEN, KILL, t);
            }
            else if (ERTOL(n))
            {
                accumvbe(go, GEN, KILL, n.E2);
                t = n.E1;
                // do not GEN the lvalue of an assignment op
                if (OTassign(op))
                {
                    t = n.E1;
                    if (t.Eoper != OPvar)
                    {
                        accumvbe(go, GEN, KILL, t.E1);
                        if (OTbinary(t.Eoper))
                            accumvbe(go, GEN, KILL, t.E2);
                    }
                }
                else
                    accumvbe(go, GEN, KILL, t);
            }
            else if (OTbinary(op))
            {
                /* do not GEN the lvalue of an assignment op    */
                if (OTassign(op))
                {
                    t = n.E1;
                    if (t.Eoper != OPvar)
                    {
                        accumvbe(go, GEN, KILL, t.E1);
                        if (OTbinary(t.Eoper))
                            accumvbe(go, GEN, KILL, t.E2);
                    }
                }
                else
                    accumvbe(go, GEN, KILL, n.E1);
                accumvbe(go, GEN, KILL, n.E2);
            }
            break;
    }

    if (n.Eexp)                    /* if a vbe elem                */
    {
        const int ne = n.Eexp;

        assert(go.expnod[ne] == n);
        if (!vec_testbit(ne,KILL))      /* if not already KILLed */
        {
            /* GEN this expression only if it hasn't        */
            /* already been GENed in this block.            */
            /* (Don't GEN common subexpressions.)           */
            if (vec_testbit(ne,GEN))
                vec_clearbit(ne,GEN);
            else
            {
                vec_setbit(ne,GEN); /* GEN this expression  */
                /* GEN all identical expressions            */
                /* (operators only, as there is no point    */
                /* to hoisting out variables and constants) */
                if (!OTleaf(op))
                {
                    foreach (uint i; 1 .. go.exptop)
                    {
                        if (op == go.expnod[i].Eoper &&
                            i != ne &&
                            el_match(n,go.expnod[i]))
                        {
                            vec_setbit(i,GEN);
                            assert(!vec_testbit(i,KILL));
                        }
                    }
                }
            }
        }
        if (op == OPvp_fp || op == OPcvp_fp)
        {
            vec_orass(KILL,go.vptrkill);   /* KILL all vptr accesses */
            vec_subass(KILL,GEN);          /* except for GENed stuff */
        }
    }
    else if (OTdef(op))             /* if definition elem           */
    {
        if (!Eunambig(n))           /* if ambiguous definition      */
        {
            vec_orass(KILL,go.defkill);
            if (OTcalldef(op))
                vec_orass(KILL,go.vptrkill);
        }
        else                    /* unambiguous definition       */
        {
            assert(t.Eoper == OPvar);
            Symbol* s = t.Vsym;  // ptr to var being def'd
            if (!(s.Sflags & SFLdistinct))
                vec_orass(KILL,go.starkill);/* kill all 'starred' refs */
            foreach (uint i; 1 .. go.exptop)        // for each vbe elem
            {
                elem* e = go.expnod[i];
                uint eop = e.Eoper;

                /* If it could be changed by the definition,     */
                /* set bit in KILL.                              */
                if (eop == OPvar)
                {
                    if (e.Vsym != s)
                        continue;
                }
                else if (OTbinary(eop))
                {
                    if (!vec_testbit(e.E1.Eexp,KILL) &&
                        !vec_testbit(e.E2.Eexp,KILL))
                        continue;
                }
                else if (OTunary(eop))
                {
                    if (!vec_testbit(e.E1.Eexp,KILL))
                        continue;
                }
                else /* OPconst or OPrelconst or OPstring */
                    continue;

                vec_setbit(i,KILL);     // KILL it
            } /* for */
        } /* if */
        vec_subass(KILL,GEN);
    } /* if */
}
