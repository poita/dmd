/**
 * Decide which functions a call may be merged with an identical call to, or
 * evaluated earlier than written: those that read and write no memory, cannot throw,
 * cannot fail and always return, so that the result is a function of the
 * arguments only and evaluating the call has no effect but producing it.
 *
 * The answer for a function depends only on its declaration and the body that
 * semantic analysis and inlining leave it, which every worker of a split
 * compilation (see `dmd.parallel`) sees the same, so a call is generated the same
 * whichever worker generates it.
 *
 * Copyright:   Copyright (C) 2026 by The D Language Foundation, All Rights Reserved
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/compiler/src/dmd/glue/readnone.d, glue/readnone.d)
 */
module dmd.glue.readnone;

import dmd.astenums;
import dmd.declaration;
import dmd.expression;
import dmd.func;
import dmd.globals;
import dmd.id;
import dmd.identifier;
import dmd.init;
import dmd.mtype;
import dmd.statement;
import dmd.target;
import dmd.tokens;
import dmd.typesem;
import dmd.dsymbol : PASS;

import dmd.backend.oper;
import dmd.glue.toir : intrinsic_op;

/**
 * Whether `fd` reads and writes no memory, cannot throw, cannot fail and always
 * returns.
 */
bool isReadNone(FuncDeclaration fd)
{
    if (!fd)
        return false;
    if (auto p = cast(void*) fd in memo)
        return *p == State.yes;
    // A function reaching itself through its calls is not known to return
    memo[cast(void*) fd] = State.inProgress;
    const r = analyze(fd);
    memo[cast(void*) fd] = r ? State.yes : State.no;
    return r;
}

private:

enum State : ubyte { inProgress, yes, no }

/* Keyed by the address of the FuncDeclaration. A function found while it is in
 * progress is answered no, and so is every function between it and the call
 * reaching it again, as each of those is on a cycle of calls: the answers do not
 * depend on which function is asked about first.
 */
__gshared State[void*] memo;

/* The C functions of Darwin's libm that read and write no memory.
 *
 * Darwin's <math.h> defines math_errhandling as MATH_ERREXCEPT: libm reports errors
 * only through the floating point exception flags and never sets errno. The code
 * generator does not model the exception flags or the rounding mode (it folds and
 * moves floating point operations assuming the default environment), so a call to
 * one of these is a function of its arguments like an addition is. The functions
 * taking pointers (frexp, modf, remquo, sincos), the ones writing a global
 * (lgamma writes signgam) and the ones defined by the current rounding mode (rint,
 * nearbyint, lrint) are not listed.
 */
immutable string[] darwinLibm = [
    "acos", "acosf", "acosh", "acoshf", "asin", "asinf", "asinh", "asinhf",
    "atan", "atan2", "atan2f", "atanf", "atanh", "atanhf",
    "cbrt", "cbrtf", "ceil", "ceilf", "copysign", "copysignf",
    "cos", "cosf", "cosh", "coshf", "erf", "erfc", "erfcf", "erff",
    "exp", "exp2", "exp2f", "expf", "expm1", "expm1f",
    "fabs", "fabsf", "fdim", "fdimf", "floor", "floorf",
    "fmax", "fmaxf", "fmin", "fminf", "fmod", "fmodf",
    "hypot", "hypotf", "log", "log10", "log10f", "log1p", "log1pf",
    "log2", "log2f", "logf", "pow", "powf", "remainder", "remainderf",
    "round", "roundf", "sin", "sinf", "sinh", "sinhf", "sqrt", "sqrtf",
    "tan", "tanf", "tanh", "tanhf", "trunc", "truncf",
];

bool isDarwinLibm(FuncDeclaration fd)
{
    if (target.os != Target.OS.OSX || fd._linkage != LINK.c || !fd.ident)
        return false;
    auto tf = fd.type ? fd.type.isTypeFunction() : null;
    if (!tf || tf.parameterList.varargs != VarArg.none || tf.isRef)
        return false;
    if (!isScalarType(tf.next))
        return false;
    foreach (p; *tf.parameterList.parameters)
        if (p.storageClass & (STC.ref_ | STC.out_ | STC.lazy_) || !isScalarType(p.type))
            return false;
    // The name the symbol is linked by, which `pragma(mangle)` can set
    const name = fd.mangleOverride.length ? fd.mangleOverride : fd.ident.toString();
    foreach (n; darwinLibm)
        if (n == name)
            return true;
    return false;
}

/* The intrinsics the code generator turns into arithmetic or a libm call listed above */
bool isPureIntrinsic(FuncDeclaration fd)
{
    switch (intrinsic_op(fd))
    {
        case OPsin, OPcos, OPsqrt, OPabs, OPrint, OPrndtol, OPscale, OPyl2x, OPyl2xp1,
             OPbsf, OPbsr, OPbswap, OPpopcnt, OPtoprec, OProl, OPror:
            return true;
        default:
            return false;
    }
}

bool isScalarType(Type t)
{
    if (!t)
        return false;
    t = t.toBasetype();
    return t.ty != Tvoid && t.isTypeBasic() !is null;
}

bool analyze(FuncDeclaration fd)
{
    // Instrumentation writes counters into memory in every function
    if (global.params.cov || global.params.trace)
        return false;
    auto tf = fd.type ? fd.type.isTypeFunction() : null;
    if (!tf)
        return false;
    if (!fd.fbody)
        return isDarwinLibm(fd) || isPureIntrinsic(fd);
    if (fd.semanticRun < PASS.semantic3done || fd.hasSemantic3Errors)
        return false;
    if (fd.needThis() || fd.isNested() || fd.closureVars.length || fd.frequire || fd.fensure ||
        fd.isCtorDeclaration() || fd.isDtorDeclaration() || fd.isNaked)
        return false;
    if (tf.parameterList.varargs != VarArg.none || tf.isRef || !isScalarType(tf.next))
        return false;
    if (tf.parameterList.parameters)
        foreach (p; *tf.parameterList.parameters)
            if (p.storageClass & (STC.ref_ | STC.out_ | STC.lazy_) || !isScalarType(p.type))
                return false;
    return Checker(fd).stmt(fd.fbody);
}

/* Walks a body accepting only what computes on scalar locals and parameters: no
 * loops (so it returns), no throw, assert, switch or goto, no indirection, and calls
 * only to functions that are read-none themselves.
 */
struct Checker
{
    FuncDeclaration fd;

    bool stmt(Statement s)
    {
        if (!s)
            return true;
        switch (s.stmt)
        {
            case STMT.Exp:
                return exp(s.isExpStatement().exp);
            case STMT.Compound:
            case STMT.CompoundDeclaration:
                foreach (s2; s.isCompoundStatement().statements[])
                    if (!stmt(s2))
                        return false;
                return true;
            case STMT.Scope:
                return stmt(s.isScopeStatement().statement);
            case STMT.If:
            {
                auto ifs = s.isIfStatement();
                return !ifs.param && exp(ifs.condition) && stmt(ifs.ifbody) && stmt(ifs.elsebody);
            }
            case STMT.Return:
            {
                auto rs = s.isReturnStatement();
                return !rs.exp || exp(rs.exp);
            }
            default:
                return false;
        }
    }

    bool local(VarDeclaration v)
    {
        return v && !v.isDataseg() && !v.isField() && !(v.storage_class & (STC.ref_ | STC.out_ | STC.lazy_ | STC.manifest)) &&
            !v.nestedrefs.length && v.toParent2() is fd && isScalarType(v.type);
    }

    bool exp(Expression e)
    {
        if (!e)
            return true;
        if (e.type && e.type.toBasetype().ty != Tvoid && !isScalarType(e.type))
            return false;
        switch (e.op)
        {
            case EXP.int64:
            case EXP.float64:
                return true;
            case EXP.variable:
                return local(e.isVarExp().var.isVarDeclaration());
            case EXP.declaration:
            {
                auto v = e.isDeclarationExp().declaration.isVarDeclaration();
                if (!local(v))
                    return false;
                if (!v._init || v._init.isVoidInitializer())
                    return true;
                auto ei = v._init.isExpInitializer();
                return ei && exp(ei.exp);
            }
            case EXP.comma:
            case EXP.add, EXP.min, EXP.mul:
            case EXP.and, EXP.or, EXP.xor:
            case EXP.leftShift, EXP.rightShift, EXP.unsignedRightShift:
            case EXP.lessThan, EXP.lessOrEqual, EXP.greaterThan, EXP.greaterOrEqual:
            case EXP.equal, EXP.notEqual, EXP.identity, EXP.notIdentity:
            case EXP.andAnd, EXP.orOr:
            {
                auto be = cast(BinExp) e;
                return exp(be.e1) && exp(be.e2);
            }
            case EXP.div, EXP.mod:
            {
                // An integer division by zero traps except on AArch64
                auto be = cast(BinExp) e;
                if (!target.isAArch64 && !e.type.isFloating())
                    return false;
                return exp(be.e1) && exp(be.e2);
            }
            case EXP.assign, EXP.construct, EXP.blit:
            case EXP.addAssign, EXP.minAssign, EXP.mulAssign:
            case EXP.andAssign, EXP.orAssign, EXP.xorAssign:
            case EXP.leftShiftAssign, EXP.rightShiftAssign, EXP.unsignedRightShiftAssign:
            {
                auto be = cast(BinExp) e;
                auto ve = be.e1.isVarExp();
                return ve && local(ve.var.isVarDeclaration()) && exp(be.e2);
            }
            case EXP.negate, EXP.tilde, EXP.not, EXP.cast_:
                return exp((cast(UnaExp) e).e1);
            case EXP.question:
            {
                auto ce = e.isCondExp();
                return exp(ce.econd) && exp(ce.e1) && exp(ce.e2);
            }
            case EXP.call:
            {
                auto ce = e.isCallExp();
                auto f = ce.f;
                if (!f || !ce.e1.isVarExp() || ce.e1.isVarExp().var !is f)
                    return false;
                if (ce.arguments)
                    foreach (a; *ce.arguments)
                        if (!exp(a))
                            return false;
                return isReadNone(f);
            }
            default:
                return false;
        }
    }
}
