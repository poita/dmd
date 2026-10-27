/**
 * Performs inlining, which is an optimization pass enabled with the `-inline` flag.
 *
 * The AST is traversed, and every function call is considered for inlining using `inlinecost.d`.
 * The function call is then inlined if this cost is below a threshold.
 *
 * Copyright:   Copyright (C) 1999-2026 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 https://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:    $(LINK2 https://github.com/dlang/dmd/blob/master/compiler/src/dmd/inline.d, _inline.d)
 * Documentation:  https://dlang.org/phobos/dmd_inline.html
 * Coverage:    https://codecov.io/gh/dlang/dmd/src/master/compiler/src/dmd/inline.d
 */

module dmd.inline;

import core.stdc.stdio;
import core.stdc.string;

import dmd.aggregate;
import dmd.arraytypes;
import dmd.astenums;
import dmd.attrib;
import dmd.declaration;
import dmd.dmodule;
import dmd.dscope;
import dmd.dstruct;
import dmd.dsymbol;
import dmd.dsymbolsem;
import dmd.dtemplate;
import dmd.expression;
import dmd.expressionsem : canElideCopy, semanticTypeInfo;
import dmd.errorsink;
import dmd.func;
import dmd.funcsem;
import dmd.globals;
import dmd.hdrgen;
import dmd.id;
import dmd.identifier;
import dmd.init;
import dmd.initsem;
import dmd.location;
import dmd.mtype;
import dmd.opover;
import dmd.printast;
import dmd.sideeffect : hasSideEffect;
import dmd.statement;
import dmd.tokens;
import dmd.typesem;
import dmd.visitor;
import dmd.visitor.postorder;
import dmd.inlinecost;

/***********************************************************
 * Scan for always-inline functions in Module m to be inlined,
 * and inline them in situ.
 *
 * Params:
 *    m = module to scan
 *    eSink = where to report errors
 */
public void inlineScanPragmaInline(Module m, ErrorSink eSink)
{
    if (m.semanticRun != PASS.semantic3done)
        return;

    inlineScanModule(m, PASS.inlinePragma, eSink);
}

/***********************************************************
 * Scan all functions in Module m and try to inline them in situ.
 *
 * Params:
 *    m = module to scan
 *    eSink = where to report errors
 */
public void inlineScanAllFunctions(Module m, ErrorSink eSink)
{
    if (m.semanticRun != PASS.semantic3done && m.semanticRun != PASS.inlinePragma)
        return;

    inlineScanModule(m, PASS.inlineAll, eSink);
}

private:



enum LOG = false;
enum CANINLINE_LOG = false;
enum EXPANDINLINE_LOG = false;


/***********************************************************
 * Represent a context to inline statements and expressions.
 *
 * Todo:
 *  It would be better to make foundReturn an instance field of DoInlineAs visitor class,
 *  like as DoInlineAs!Result.result field, because it's one another result of inlining.
 *  The best would be to return a pair of result Expression and a bool value as foundReturn
 *  from doInlineAs function.
 */
private final class InlineDoState
{
    // inline context
    Expression eret;    // expression returned to in case of NRVO
    VarDeclaration vthis;
    Dsymbols from;      // old Dsymbols
    Dsymbols to;        // parallel array of new Dsymbols
    Dsymbol parent;     // new parent
    FuncDeclaration fd; // function being inlined (old parent)
    // inline result
    bool foundReturn;
    bool propagateNRVO;
    LabelDsymbol retLabel;      // where a return goes to, inlined as statements
    LabelDsymbol[void*] labels; // the labels made for the inlined function's labels

    this(Dsymbol parent, FuncDeclaration fd) scope
    {
        this.parent = parent;
        this.fd = fd;
    }
}

private Expression combineInlineSequence(Expression e1, Expression e2)
{
    auto result = Expression.combine(e1, e2);
    if (result)
        if (auto ce = result.isCommaExp())
            ce.isInlineSequence = true;
    return result;
}

/***********************************************************
 * Perform the inlining from (Statement or Expression) to (Statement or Expression).
 *
 * Inlining is done by:
 *  - Converting to an Expression
 *  - Copying the trees of the function to be inlined
 *  - Renaming the variables
 */
private extern (C++) final class DoInlineAs(Result) : Visitor
if (is(Result == Statement) || is(Result == Expression))
{
    alias visit = Visitor.visit;
public:
    InlineDoState ids;
    Result result;

    enum asStatements = is(Result == Statement);

    extern (D) this(InlineDoState ids) scope
    {
        this.ids = ids;
    }

    // Statement -> (Statement | Expression)

    override void visit(Statement s)
    {
        printf("Statement.doInlineAs!%s()\n%s\n", Result.stringof.ptr, s.toChars());
        fflush(stdout);
        assert(0); // default is we can't inline it
    }

    override void visit(ExpStatement s)
    {
        static if (LOG)
        {
            if (s.exp)
                printf("ExpStatement.doInlineAs!%s() '%s'\n", Result.stringof.ptr, s.exp.toChars());
        }

        auto exp = doInlineAs!Expression(s.exp, ids);
        static if (asStatements)
            result = new ExpStatement(s.loc, exp);
        else
            result = exp;
    }

    override void visit(CompoundStatement s)
    {
        //printf("CompoundStatement.doInlineAs!%s() %d\n", Result.stringof.ptr, s.statements.length);
        static if (asStatements)
        {
            auto as = Statements();
            as.reserve(s.statements.length);
        }

        foreach (i, sx; s.statements)
        {
            if (!sx)
                continue;
            static if (asStatements)
            {
                /* if (condition) return; rest, of a function returning void, as
                 * if (condition) {} else { rest }
                 */
                IfStatement ifs;
                if ((ifs = sx.isIfStatement()) !is null && ifs.ifbody && !ifs.elsebody && !ifs.param &&
                    ifs.ifbody.endsWithReturnStatement() && !ifs.ifbody.endsWithReturnStatement().exp &&
                    !restEndsWithReturn(s.statements, i + 1) && restHasNoReturn(s.statements, i + 1))
                {
                    auto rest = Statements();
                    foreach (st; s.statements[i + 1 .. $])
                        if (st)
                            rest.push(st);
                    auto restStatement = new CompoundStatement(sx.loc, rest.move());
                    auto cond = doInlineAs!Expression(ifs.condition, ids);
                    Statement ifbody = doInlineAs!Statement(ifs.ifbody, ids);
                    if (!ifbody)        // a bare return leaves nothing
                        ifbody = new CompoundStatement(ifs.loc, Statements());
                    ids.foundReturn = false;    // the return ends only the if's body
                    auto elsebody = doInlineAs!Statement(restStatement, ids);
                    auto ifs2 = new IfStatement(ifs.loc, null, cond, ifbody, elsebody, ifs.endloc);
                    ids.foundReturn = false;
                    as.push(ifs2);
                    break;
                }
                as.push(doInlineAs!Statement(sx, ids));
            }
            else
            {
                /* Specifically allow:
                 *  if (condition)
                 *      return exp1;
                 *  statements ending with return exp2;
                 */
                IfStatement ifs;
                if ((ifs = sx.isIfStatement()) !is null &&
                    ifs.ifbody &&
                    ifs.ifbody.endsWithReturnStatement() &&
                    !ifs.elsebody &&
                    restEndsWithReturn(s.statements, i + 1)
                   )
                {
                    /* Rewrite as condition ? exp1 : (statements, exp2)
                     */
                    auto econd = doInlineAs!Expression(ifs.condition, ids);
                    assert(econd);
                    auto e1 = doInlineAs!Expression(ifs.ifbody, ids);
                    assert(ids.foundReturn);
                    Statement s3 = s.statements[i + 1];
                    if (i + 2 < s.statements.length)
                    {
                        auto rest = Statements();
                        foreach (st; s.statements[i + 1 .. $])
                            rest.push(st);
                        s3 = new CompoundStatement(s3.loc, rest.move());
                    }
                    auto e2 = doInlineAs!Expression(s3, ids);
                    assert(e2);
                    Expression e = new CondExp(econd.loc, econd, e1, e2);
                    e.type = e1.type;
                    if (e.type.ty == Ttuple)
                    {
                        e1.type = Type.tvoid;
                        e2.type = Type.tvoid;
                        e.type = Type.tvoid;
                    }
                    result = combineInlineSequence(result, e);
                }
                else
                {
                    ids.foundReturn = false;
                    auto e = doInlineAs!Expression(sx, ids);
                    result = combineInlineSequence(result, e);
                }
            }

            if (ids.foundReturn)
                break;
        }

        static if (asStatements)
            result = new CompoundStatement(s.loc, as.move());
    }

    override void visit(UnrolledLoopStatement s)
    {
        //printf("UnrolledLoopStatement.doInlineAs!%s() %d\n", Result.stringof.ptr, s.statements.length);
        static if (asStatements)
        {
            auto as = Statements();
            as.reserve(s.statements.length);
        }

        // a break or continue may leave an iteration ending with a return for what follows it
        const leaves = hasBreakOrContinue(s);
        foreach (sx; s.statements)
        {
            if (!sx)
                continue;
            auto r = doInlineAs!Result(sx, ids);
            static if (asStatements)
                as.push(r);
            else
                result = combineInlineSequence(result, r);

            if (ids.foundReturn)
            {
                if (!leaves)
                    break;
                ids.foundReturn = false;
            }
        }

        static if (asStatements)
            result = new UnrolledLoopStatement(s.loc, as.move());
    }

    override void visit(ScopeStatement s)
    {
        //printf("ScopeStatement.doInlineAs!%s() %d\n", Result.stringof.ptr, s.statement.length);
        auto r = doInlineAs!Result(s.statement, ids);
        static if (asStatements)
            result = new ScopeStatement(s.loc, r, s.endloc);
        else
            result = r;
    }

    override void visit(IfStatement s)
    {
        assert(!s.param);
        auto econd = doInlineAs!Expression(s.condition, ids);
        assert(econd);

        auto ifbody = doInlineAs!Result(s.ifbody, ids);
        bool bodyReturn = ids.foundReturn;

        ids.foundReturn = false;
        auto elsebody = doInlineAs!Result(s.elsebody, ids);

        static if (asStatements)
        {
            result = new IfStatement(s.loc, s.param, econd, ifbody, elsebody, s.endloc);
        }
        else
        {
            alias e1 = ifbody;
            alias e2 = elsebody;
            if (e1 && e2)
            {
                result = new CondExp(econd.loc, econd, e1, e2);
                result.type = e1.type;
                if (result.type.ty == Ttuple)
                {
                    e1.type = Type.tvoid;
                    e2.type = Type.tvoid;
                    result.type = Type.tvoid;
                }
            }
            else if (e1)
            {
                result = new LogicalExp(econd.loc, EXP.andAnd, econd, e1);
                result.type = Type.tvoid;
            }
            else if (e2)
            {
                result = new LogicalExp(econd.loc, EXP.orOr, econd, e2);
                result.type = Type.tvoid;
            }
            else
            {
                result = econd;
            }
        }
        ids.foundReturn = ids.foundReturn && bodyReturn;
    }

    override void visit(ReturnStatement s)
    {
        //printf("ReturnStatement.doInlineAs!%s() '%s'\n", Result.stringof.ptr, s.exp ? s.exp.toChars() : "");
        ids.foundReturn = true;

        auto exp = doInlineAs!Expression(s.exp, ids);
        static if (asStatements)
        {
            // a return before the end of the function goes to the end of what is inlined
            if (ids.retLabel)
            {
                auto a = Statements();
                if (exp)
                {
                    if (ids.eret)
                    {
                        auto ce = new ConstructExp(s.loc, ids.eret.copy(), exp);
                        ce.type = ids.eret.type;
                        exp = ce;
                    }
                    a.push(new ExpStatement(s.loc, exp));
                }
                a.push(gotoLabel(s.loc, ids.retLabel));
                result = new CompoundStatement(s.loc, a.move());
                return;
            }
        }
        if (!exp) // https://issues.dlang.org/show_bug.cgi?id=14560
                  // 'return' must not leave in the expand result
            return;
        static if (asStatements)
        {
            /* Any return statement should be the last statement in the function being
             * inlined, otherwise things shouldn't have gotten this far. The value is
             * assigned to the variable the call initializes or is assigned to, if
             * any, or else is ignored, so `exp` is evaluated only for side effects.
             * Already disallowed this if `exp` produces an object that needs destruction -
             * an enhancement would be to do the destruction here.
             */
            if (ids.eret)
            {
                auto ce = new ConstructExp(s.loc, ids.eret.copy(), exp);
                ce.type = ids.eret.type;
                exp = ce;
            }
            result = new ExpStatement(s.loc, exp);
        }
        else
        {
            if (!ids.fd || ids.fd.isNRVO)
            {
                result = exp;
                return;
            }

            if (ids.eret)
            {
                /* Perform RVO emplacement into eret.
                 * Generate:
                 *   ( eret ) = ( exp ), ( eret )
                 */
                auto ce = new ConstructExp(s.loc, ids.eret.copy(), exp);
                ce.type = exp.type;
                result = Expression.combine(ce, ids.eret.copy());
                return;
            }

            auto tf = ids.fd.type.isTypeFunction();

            if (exp.type.ty == Tstruct && !tf.isRef &&
                !ids.fd.isCtorDeclaration() && !canElideCopy(s.exp, tf.nextOf(), true))
            {
                /* If the inlined function returns a copy of a struct,
                 * and then the return value is used subsequently as an
                 * lvalue, as in a struct return that is then used as a 'this'.
                 * Taking the address of the return value will be taking the address
                 * of the original, not the copy. Fix this by assigning the return value to
                 * a temporary, then returning the temporary. If the temporary is used as an
                 * lvalue, it will work.
                 * This only happens with struct returns.
                 * See https://issues.dlang.org/show_bug.cgi?id=2127 for an example.
                 *
                 * On constructor call making __inlineretval is merely redundant, because
                 * the returned reference is exactly same as vthis, and the 'this' variable
                 * already exists at the caller side.
                 *
                 * Generate a new variable to hold the result and initialize it with the
                 * inlined body of the function:
                 *   tret __inlineretval = e;
                 */
                auto ei = new ExpInitializer(s.loc, exp);
                auto tmp = Identifier.generateId("__inlineretval");
                auto vd = new VarDeclaration(s.loc, tf.next, tmp, ei);
                vd.storage_class = STC.temp | (tf.isRef ? STC.ref_ : STC.rvalue);
                vd._linkage = tf.linkage;
                vd.parent = ids.parent;

                ei.exp = new ConstructExp(s.loc, vd, exp);
                ei.exp.type = vd.type;

                auto de = new DeclarationExp(s.loc, vd);
                de.type = Type.tvoid;

                // Chain the two together:
                //   ( typeof(return) __inlineretval = ( inlined body )) , __inlineretval
                exp = Expression.combine(de, new VarExp(s.loc, vd));
            }

            result = exp;
        }
    }

    override void visit(ImportStatement s)
    {
        //printf("ImportStatement.doInlineAs!%s()\n", Result.stringof.ptr);
    }

    override void visit(ForStatement s)
    {
        //printf("ForStatement.doInlineAs!%s()\n", Result.stringof.ptr);
        static if (asStatements)
        {
            auto sinit = doInlineAs!Statement(s._init, ids);
            auto scond = doInlineAs!Expression(s.condition, ids);
            auto sincr = doInlineAs!Expression(s.increment, ids);
            auto sbody = doInlineAs!Statement(s._body, ids);
            result = new ForStatement(s.loc, sinit, scond, sincr, sbody, s.endloc);
            // a return in the body, made a goto, leaves what follows the loop reachable
            ids.foundReturn = false;
        }
        else
            result = null;  // cannot be inlined as an Expression
    }

    // the labels made for returns, in a function inlined in turn
    override void visit(LabelStatement s)
    {
        static if (asStatements)
        {
            auto ld = copiedLabel(s);
            ld.statement.statement = doInlineAs!Statement(s.statement, ids);
            result = ld.statement;
        }
        else
            result = null;  // cannot be inlined as an Expression
    }

    override void visit(GotoStatement s)
    {
        static if (asStatements)
            result = gotoLabel(s.loc, copiedLabel(s.label.statement));
        else
            result = null;  // cannot be inlined as an Expression
    }

    // the label of the inlined code for label statement s of the function
    LabelDsymbol copiedLabel(LabelStatement s)
    {
        if (auto p = cast(void*)s in ids.labels)
            return *p;
        auto ld = returnLabel(s.loc, ids.parent.isFuncDeclaration());
        ids.labels[cast(void*)s] = ld;
        return ld;
    }

    override void visit(BreakStatement s)
    {
        static if (asStatements)
            result = new BreakStatement(s.loc, null);
        else
            result = null;  // cannot be inlined as an Expression
    }

    override void visit(ContinueStatement s)
    {
        static if (asStatements)
            result = new ContinueStatement(s.loc, null);
        else
            result = null;  // cannot be inlined as an Expression
    }

    override void visit(ThrowStatement s)
    {
        //printf("ThrowStatement.doInlineAs!%s() '%s'\n", Result.stringof.ptr, s.exp.toChars());
        static if (asStatements)
            result = new ThrowStatement(s.loc, doInlineAs!Expression(s.exp, ids));
        else
        {
            result = new ThrowExp(s.loc, doInlineAs!Expression(s.exp, ids));
            result.type = Type.tnoreturn;
        }
    }

    // Expression -> (Statement | Expression)

    static if (asStatements)
    {
        override void visit(Expression e)
        {
            result = new ExpStatement(e.loc, doInlineAs!Expression(e, ids));
        }
    }
    else
    {
        /******************************
         * Perform doInlineAs() on an array of Expressions.
         */
        Expressions* arrayExpressionDoInline(Expressions* a)
        {
            if (!a)
                return null;

            auto newa = new Expressions(a.length);

            foreach (i; 0 .. a.length)
            {
                (*newa)[i] = doInlineAs!Expression((*a)[i], ids);
            }
            return newa;
        }

        override void visit(Expression e)
        {
            //printf("Expression.doInlineAs!%s(%s): %s\n", Result.stringof.ptr, EXPtoString(e.op).ptr, e.toChars());
            result = e.copy();
        }

        override void visit(SymOffExp e)
        {
            //printf("SymOffExp.doInlineAs!%s(%s)\n", Result.stringof.ptr, e.toChars());
            if (ids.eret && ids.fd &&
                (ids.fd.isNRVO && e.var == ids.fd.nrvo_var || e.var.nrvo))
            {
                // Deoptimize here and turn SymOffExp back into (&( eret ) + offset),
                // because eret might have no symbol.
                result = new AddrExp(e.loc, ids.eret.copy());
                result.type = e.type;

                if (e.offset)
                {
                    auto ie = new IntegerExp(e.loc, e.offset, Type.tsize_t);
                    result = new AddExp(e.loc, result, ie);
                    result.type = e.type;
                }

                return;
            }
            // the latest copy of a variable, as an expression and its lowering
            // share subexpressions declaring variables, which are copied for each
            foreach_reverse (i; 0 .. ids.from.length)
            {
                if (e.var != ids.from[i])
                    continue;
                auto se = e.copy().isSymOffExp();
                se.var = ids.to[i].isDeclaration();
                result = se;
                return;
            }
            result = e;
        }

        override void visit(VarExp e)
        {
            //printf("VarExp.doInlineAs!%s(%s)\n", Result.stringof.ptr, e.toChars());
            if (ids.eret && ids.fd &&
                (ids.fd.isNRVO && e.var == ids.fd.nrvo_var || e.var.nrvo))
            {
                result = ids.eret.copy();
                return;
            }
            // the latest copy of a variable, as for SymOffExp
            foreach_reverse (i; 0 .. ids.from.length)
            {
                if (e.var != ids.from[i])
                    continue;
                auto ve = e.copy().isVarExp();
                ve.var = ids.to[i].isDeclaration();
                result = ve;
                return;
            }
            if (ids.fd && e.var == ids.fd.vthis)
            {
                result = new VarExp(e.loc, ids.vthis);
                if (ids.fd.hasDualContext)
                    result = new AddrExp(e.loc, result);
                result.type = e.type;
                return;
            }

            /* Inlining context pointer access for nested referenced variables.
             * For example:
             *      auto fun() {
             *        int i = 40;
             *        auto foo() {
             *          int g = 2;
             *          struct Result {
             *            auto bar() { return i + g; }
             *          }
             *          return Result();
             *        }
             *        return foo();
             *      }
             *      auto t = fun();
             * 'i' and 'g' are nested referenced variables in Result.bar(), so:
             *      auto x = t.bar();
             * should be inlined to:
             *      auto x = *(t.vthis.vthis + i.voffset) + *(t.vthis + g.voffset)
             */
            auto v = e.var.isVarDeclaration();
            if (v && v.nestedrefs.length && ids.vthis)
            {
                Dsymbol s = ids.fd;
                auto fdv = v.toParent().isFuncDeclaration();
                assert(fdv);
                result = new VarExp(e.loc, ids.vthis);
                result.type = ids.vthis.type;
                if (ids.fd.hasDualContext)
                {
                    // &__this
                    result = new AddrExp(e.loc, result);
                    result.type = ids.vthis.type.pointerTo();
                }
                while (s != fdv)
                {
                    auto f = s.isFuncDeclaration();
                    AggregateDeclaration ad;
                    if (f && f.hasDualContext)
                    {
                        if (f.hasNestedFrameRefs())
                        {
                            result = new DotVarExp(e.loc, result, f.vthis);
                            result.type = f.vthis.type;
                        }
                        // (*__this)[i]
                        uint i = f.followInstantiationContext(fdv);
                        if (i == 1 && f == ids.fd)
                        {
                            auto ve = e.copy().isVarExp();
                            ve.originalScope = ids.fd;
                            result = ve;
                            return;
                        }
                        result = new PtrExp(e.loc, result);
                        result.type = Type.tvoidptr.sarrayOf(2);
                        auto ie = new IndexExp(e.loc, result, new IntegerExp(i));
                        ie.indexIsInBounds = true; // no runtime bounds checking
                        result = ie;
                        result.type = Type.tvoidptr;
                        s = f.toParentP(fdv);
                        ad = s.isAggregateDeclaration();
                        if (ad)
                            goto Lad;
                        continue;
                    }
                    else if ((ad = s.isThis()) !is null)
                    {
                Lad:
                        while (ad)
                        {
                            assert(ad.vthis);
                            bool i = ad.followInstantiationContext(fdv);
                            auto vthis = i ? ad.vthis2 : ad.vthis;
                            result = new DotVarExp(e.loc, result, vthis);
                            result.type = vthis.type;
                            s = ad.toParentP(fdv);
                            ad = s.isAggregateDeclaration();
                        }
                    }
                    else if (f && f.isNested())
                    {
                        assert(f.vthis);
                        if (f.hasNestedFrameRefs())
                        {
                            result = new DotVarExp(e.loc, result, f.vthis);
                            result.type = f.vthis.type;
                        }
                        s = f.toParent2();
                    }
                    else
                        assert(0);
                    assert(s);
                }
                result = new DotVarExp(e.loc, result, v);
                result.type = v.type;
                //printf("\t==> result = %s, type = %s\n", result.toChars(), result.type.toChars());
                return;
            }
            else if (v && v.nestedrefs.length)
            {
                auto ve = e.copy().isVarExp();
                ve.originalScope = ids.fd;
                result = ve;
                return;
            }

            result = e;
        }

        override void visit(ThisExp e)
        {
            //if (!ids.vthis)
            //    e.error("no `this` when inlining `%s`", ids.parent.toErrMsg());
            if (!ids.vthis)
            {
                result = e;
                return;
            }
            result = new VarExp(e.loc, ids.vthis);
            if (ids.fd.hasDualContext)
            {
                // __this[0]
                result.type = ids.vthis.type;
                auto ie = new IndexExp(e.loc, result, IntegerExp.literal!0);
                ie.indexIsInBounds = true; // no runtime bounds checking
                result = ie;
                if (e.type.ty == Tstruct)
                {
                    result.type = e.type.pointerTo();
                    result = new PtrExp(e.loc, result);
                }
            }
            result.type = e.type;
        }

        override void visit(SuperExp e)
        {
            if (!ids.vthis)
            {
                result = e;
                return;
            }
            result = new VarExp(e.loc, ids.vthis);
            if (ids.fd.hasDualContext)
            {
                // __this[0]
                result.type = ids.vthis.type;
                auto ie = new IndexExp(e.loc, result, IntegerExp.literal!0);
                ie.indexIsInBounds = true; // no runtime bounds checking
                result = ie;
            }
            result.type = e.type;
        }

        override void visit(DeclarationExp e)
        {
            //printf("DeclarationExp.doInlineAs!%s(%s)\n", Result.stringof.ptr, e.toChars());
            if (auto vd = e.declaration.isVarDeclaration())
            {
                version (none)
                {
                    // Need to figure this out before inlining can work for tuples
                    if (auto tup = vd.toAlias().isTupleDeclaration())
                    {
                        tup.foreachVar((s) { s; });
                        result = st.objects.length;
                        return;
                    }
                }

                if (vd.isStatic() || (vd.storage_class & STC.manifest))
                    return;

                bool varIsNRVO = ids.fd && (ids.fd.isNRVO && vd == ids.fd.nrvo_var || vd.nrvo);

                if (ids.eret && varIsNRVO)
                {
                    if (vd._init && !vd._init.isVoidInitializer())
                    {
                        result = vd._init.initializerToExpression(null, null, global.errorSink);
                        assert(result);
                        result = doInlineAs!Expression(result, ids);
                    }
                    else
                        result = IntegerExp.literal!0;
                    return;
                }

                auto vto = new VarDeclaration(vd.loc, vd.type, vd.ident, vd._init);
                memcpy(cast(void*)vto, cast(void*)vd, __traits(classInstanceSize, VarDeclaration));
                vto.parent = ids.parent;
                vto.csym = null;
                vto.nrvo = ids.propagateNRVO && varIsNRVO;
                // what refers to vd is not inlined with it: the copy gets an empty list of its own,
                // set bit by bit as it shares vd's list, which assigning would free
                static immutable FuncDeclarations noRefs;
                memcpy(cast(void*) &vto.nestedrefs, cast(const void*) &noRefs, FuncDeclarations.sizeof);

                ids.from.push(vd);
                ids.to.push(vto);

                if (vd._init)
                {
                    if (vd._init.isVoidInitializer())
                    {
                        vto._init = new VoidInitializer(vd._init.loc);
                    }
                    else
                    {
                        auto ei = vd._init.initializerToExpression(null, null, global.errorSink);
                        assert(ei);
                        vto._init = new ExpInitializer(ei.loc, doInlineAs!Expression(ei, ids));
                    }
                }
                if (vd.edtor)
                {
                    vto.edtor = doInlineAs!Expression(vd.edtor, ids);
                }
                auto de = e.copy().isDeclarationExp();
                de.declaration = vto;
                result = de;
                return;
            }

            // Prevent the copy of the aggregates allowed in inlineable funcs
            if (isInlinableNestedAggregate(e))
                return;

            /* This needs work, like DeclarationExp.toElem(), if we are
             * to handle TemplateMixin's. For now, we just don't inline them.
             */
            visit(cast(Expression)e);
        }

        override void visit(TypeidExp e)
        {
            //printf("TypeidExp.doInlineAs!%s(): %s\n", Result.stringof.ptr, e.toChars());
            auto te = e.copy().isTypeidExp();
            if (auto ex = isExpression(te.obj))
            {
                te.obj = doInlineAs!Expression(ex, ids);
            }
            else
                assert(isType(te.obj));
            result = te;
        }

        override void visit(NewExp e)
        {
            //printf("NewExp.doInlineAs!%s(): %s\n", Result.stringof.ptr, e.toChars());
            auto ne = e.copy().isNewExp();
            auto lowering = ne.lowering;
            if (lowering)
                if (auto ce = lowering.isCallExp())
                    if (ce.f.ident == Id._d_newarrayT ||
                        ce.f.ident == Id._d_newarraymTX ||
                        ce.f.ident == Id._d_aaNew)
                        ne.lowering = doInlineAs!Expression(lowering, ids);

            // CTFE interprets the expression itself rather than its lowering
            ne.placement = doInlineAs!Expression(e.placement, ids);
            ne.thisexp = doInlineAs!Expression(e.thisexp, ids);
            ne.argprefix = doInlineAs!Expression(e.argprefix, ids);
            ne.arguments = arrayExpressionDoInline(e.arguments);

            result = ne;

            semanticTypeInfo(null, e.type);
        }

        override void visit(UnaExp e)
        {
            auto ue = cast(UnaExp)e.copy();
            ue.e1 = doInlineAs!Expression(e.e1, ids);
            result = ue;
        }

        override void visit(CastExp e)
        {
            auto ce = cast(CastExp)e.copy();
            ce.lowering = doInlineAs!Expression(ce.lowering, ids);
            ce.e1 = doInlineAs!Expression(e.e1, ids);
            result = ce;
        }

        override void visit(AssertExp e)
        {
            auto ae = e.copy().isAssertExp();
            ae.e1 = doInlineAs!Expression(e.e1, ids);
            ae.msg = doInlineAs!Expression(e.msg, ids);
            result = ae;
        }

        override void visit(CatExp e)
        {
            auto ce = e.copy().isCatExp();
            ce.lowering = doInlineAs!Expression(ce.lowering, ids);
            ce.e1 = doInlineAs!Expression(e.e1, ids);
            ce.e2 = doInlineAs!Expression(e.e2, ids);
            result = ce;
        }

        override void visit(CatAssignExp e)
        {
            auto cae = cast(CatAssignExp) e.copy();
            cae.lowering = doInlineAs!Expression(cae.lowering, ids);
            cae.e1 = doInlineAs!Expression(e.e1, ids);
            cae.e2 = doInlineAs!Expression(e.e2, ids);
            result = cae;
        }

        override void visit(BinExp e)
        {
            auto be = cast(BinExp)e.copy();
            be.e1 = doInlineAs!Expression(e.e1, ids);
            be.e2 = doInlineAs!Expression(e.e2, ids);
            result = be;
        }

        override void visit(CallExp e)
        {
            auto ce = e.copy().isCallExp();
            ce.e1 = doInlineAs!Expression(e.e1, ids);
            ce.arguments = arrayExpressionDoInline(e.arguments);
            result = ce;
        }

        override void visit(AssignExp e)
        {
            visit(cast(BinExp)e);
        }

        override void visit(ConstructExp e)
        {
            auto ce = cast(ConstructExp)e.copy();
            ce.lowering = doInlineAs!Expression(ce.lowering, ids);
            ce.e1 = doInlineAs!Expression(e.e1, ids);
            ce.e2 = doInlineAs!Expression(e.e2, ids);
            result = ce;
        }

        override void visit(LoweredAssignExp e)
        {
            // CTFE interprets the assignment itself rather than its lowering
            auto le = cast(LoweredAssignExp)e.copy();
            le.lowering = doInlineAs!Expression(e.lowering, ids);
            le.e1 = doInlineAs!Expression(e.e1, ids);
            le.e2 = doInlineAs!Expression(e.e2, ids);
            result = le;
        }

        override void visit(EqualExp e)
        {
            auto ee = cast(EqualExp)e.copy();
            ee.lowering = doInlineAs!Expression(ee.lowering, ids);
            ee.e1 = doInlineAs!Expression(e.e1, ids);
            ee.e2 = doInlineAs!Expression(e.e2, ids);

            result = ee;

            Type t1 = e.e1.type.toBasetype();
            if (t1.isStaticOrDynamicArray())
            {
                Type t = t1.nextOf().toBasetype();
                while (t.toBasetype().nextOf())
                    t = t.nextOf().toBasetype();
                if (t.ty == Tstruct)
                    semanticTypeInfo(null, t);
            }
            else if (t1.ty == Taarray)
            {
                semanticTypeInfo(null, t1);
            }
        }

        override void visit(IndexExp e)
        {
            auto are = e.copy().isIndexExp();
            are.e1 = doInlineAs!Expression(e.e1, ids);
            if (e.lengthVar)
            {
                //printf("lengthVar\n");
                auto vd = e.lengthVar;
                auto vto = new VarDeclaration(vd.loc, vd.type, vd.ident, vd._init);
                memcpy(cast(void*)vto, cast(void*)vd, __traits(classInstanceSize, VarDeclaration));
                vto.parent = ids.parent;
                vto.csym = null;

                ids.from.push(vd);
                ids.to.push(vto);

                if (vd._init && !vd._init.isVoidInitializer())
                {
                    auto ie = vd._init.isExpInitializer();
                    assert(ie);
                    vto._init = new ExpInitializer(ie.loc, doInlineAs!Expression(ie.exp, ids));
                }
                are.lengthVar = vto;
            }
            are.e2 = doInlineAs!Expression(e.e2, ids);
            result = are;
        }

        override void visit(SliceExp e)
        {
            auto are = e.copy().isSliceExp();
            are.e1 = doInlineAs!Expression(e.e1, ids);
            if (e.lengthVar)
            {
                //printf("lengthVar\n");
                auto vd = e.lengthVar;
                auto vto = new VarDeclaration(vd.loc, vd.type, vd.ident, vd._init);
                memcpy(cast(void*)vto, cast(void*)vd, __traits(classInstanceSize, VarDeclaration));
                vto.parent = ids.parent;
                vto.csym = null;

                ids.from.push(vd);
                ids.to.push(vto);

                if (vd._init && !vd._init.isVoidInitializer())
                {
                    auto ie = vd._init.isExpInitializer();
                    assert(ie);
                    vto._init = new ExpInitializer(ie.loc, doInlineAs!Expression(ie.exp, ids));
                }

                are.lengthVar = vto;
            }
            are.lwr = doInlineAs!Expression(e.lwr, ids);
            are.upr = doInlineAs!Expression(e.upr, ids);
            result = are;
        }

        override void visit(TupleExp e)
        {
            auto ce = e.copy().isTupleExp();
            ce.e0 = doInlineAs!Expression(e.e0, ids);
            ce.exps = arrayExpressionDoInline(e.exps);
            result = ce;
        }

        override void visit(ArrayLiteralExp e)
        {
            auto ce = e.copy().isArrayLiteralExp();
            ce.basis = doInlineAs!Expression(e.basis, ids);
            ce.elements = arrayExpressionDoInline(e.elements);
            result = ce;

            semanticTypeInfo(null, e.type);
        }

        override void visit(AssocArrayLiteralExp e)
        {
            auto ce = e.copy().isAssocArrayLiteralExp();
            ce.keys = arrayExpressionDoInline(e.keys);
            ce.values = arrayExpressionDoInline(e.values);
            ce.lowering = doInlineAs!Expression(e.lowering, ids);
            result = ce;

            semanticTypeInfo(null, e.type);
        }

        override void visit(StructLiteralExp e)
        {
            if (e.inlinecopy)
            {
                result = e.inlinecopy;
                return;
            }
            auto ce = e.copy().isStructLiteralExp();
            e.inlinecopy = ce;
            ce.elements = arrayExpressionDoInline(e.elements);
            e.inlinecopy = null;
            result = ce;
        }

        override void visit(ArrayExp e)
        {
            assert(0); // this should have been lowered to something else
        }

        override void visit(CondExp e)
        {
            auto ce = e.copy().isCondExp();
            ce.econd = doInlineAs!Expression(e.econd, ids);
            ce.e1 = doInlineAs!Expression(e.e1, ids);
            ce.e2 = doInlineAs!Expression(e.e2, ids);
            result = ce;
        }
    }
}

/// ditto
private Result doInlineAs(Result)(Statement s, InlineDoState ids)
{
    if (!s)
        return null;

    scope DoInlineAs!Result v = new DoInlineAs!Result(ids);
    s.accept(v);
    return v.result;
}

/// ditto
private Result doInlineAs(Result)(Expression e, InlineDoState ids)
{
    if (!e)
        return null;

    scope DoInlineAs!Result v = new DoInlineAs!Result(ids);
    e.accept(v);
    static if (is(Result == Expression))
        fixBoundsCheck(v.result, ids.fd);
    return v.result;
}

/***********************************************************
 * Keep the array bounds checks of a copy of an expression of `fd` as they are
 * in `fd`, wherever it is inlined: under `-release` the bounds of `@safe` code
 * are checked, while those of the code it may be inlined into are not.
 * Params:
 *      e = copy of an expression of fd
 *      fd = function inlined
 */
private void fixBoundsCheck(Expression e, FuncDeclaration fd)
{
    if (!e || e.boundsCheckFixed)
        return;
    switch (e.op)
    {
        // the expressions whose code checks bounds, each a fresh copy
        case EXP.index, EXP.slice, EXP.assign, EXP.construct, EXP.blit:
            break;
        default:
            return;
    }
    e.boundsCheckFixed = true;
    e.boundsCheck = !fd.isCsymbol() && arrayBoundsCheck(fd);
}

/// Whether `t` is the type of an expression that does not complete
private bool isNoReturn(Type t)
{
    return t && t.toBasetype().isTypeNoreturn() !is null;
}

/// Whether `e` does not complete: a throw, assert(0), halt or a call that never returns
private bool isNoReturnExp(Expression e)
{
    if (e.isThrowExp() || e.isHaltExp())
        return true;
    if (auto ae = e.isAssertExp())
        if (auto ie = ae.e1.isIntegerExp())
            return ie.getInteger() == 0;
    return isNoReturn(e.type);
}

/**
 * Whether the last statement of `s` does not complete, so that `s` completes only
 * by leaving it earlier, as by return, break or goto.
 * Conservative: false where it cannot tell.
 */
private bool endsInNoReturn(Statement s)
{
    if (!s)
        return false;
    if (s.isThrowStatement())
        return true;
    if (auto es = s.isExpStatement())
        return es.exp && isNoReturnExp(es.exp);
    if (auto cs = s.isCompoundStatement())
    {
        foreach_reverse (st; cs.statements)
            if (st)
                return endsInNoReturn(st);
        return false;
    }
    if (auto ss = s.isScopeStatement())
        return endsInNoReturn(ss.statement);
    if (auto ifs = s.isIfStatement())
        return endsInNoReturn(ifs.ifbody) && endsInNoReturn(ifs.elsebody);
    return false;
}

/// Whether functions, by address, never return normally (see `alwaysThrows`)
private __gshared bool[void*] neverReturns;

/**
 * Whether `fd` never returns normally: it has no return statement and its body
 * ends in a statement that does not complete, so a call of it is on an error path.
 */
private bool alwaysThrows(FuncDeclaration fd)
{
    if (auto p = cast(void*)fd in neverReturns)
        return *p;
    bool result;
    if (auto fb = fd.fbody)
    {
        if (endsInNoReturn(fb))
        {
            auto statements = new Statements(1);
            (*statements)[0] = fb;
            result = restHasNoReturn(*statements, 0);
        }
    }
    neverReturns[cast(void*)fd] = result;
    return result;
}

/***********************************************************
 * Walk the trees, looking for functions to inline.
 * Inline any that can be.
 */
/// The costs canInline() computed, by function
private __gshared int[void*] inlineCosts;

private int inlineCostOf(FuncDeclaration fd)
{
    if (auto p = cast(void*)fd in inlineCosts)
        return *p;
    return 0;
}

private extern (C++) final class InlineScanVisitor : Visitor
{
    alias visit = Visitor.visit;

public:
    FuncDeclaration parent;     // function being scanned
    PASS pass;
    ErrorSink eSink;
    int inlinedCost;            // cost of the functions inlined outside loops
    int loopInlinedCost;        // cost of the functions too costly outside loops inlined into loops
    int loopDepth;              // number of loops around what is being scanned
    int coldDepth;              // number of rarely run paths around what is being scanned

    // As the visit method cannot return a value, these variables
    // are used to pass the result from 'visit' back to 'inlineScan'
    Statement sresult;
    Expression eresult;
    bool again;

    extern (D) this(FuncDeclaration parent, PASS pass, ErrorSink eSink) scope @safe
    {
        this.parent = parent;
        this.pass = pass;
        this.eSink = eSink;
    }

    void reset()
    {
        sresult = null;
        eresult = null;
        again = false;
    }

    override void visit(Statement s)
    {
    }

    /// Whether the function being scanned is small enough for statements inlined into
    /// it not to crowd out its register variables
    bool smallCaller()
    {
        enum maxCallerLines = 150;
        return registersToSpare() ||
               parent.endloc.linnum >= parent.loc.linnum &&
               parent.endloc.linnum - parent.loc.linnum <= maxCallerLines;
    }

    /* Calls in `exp` of functions with loops, which are inlined only as statements,
     * are moved into temporaries declared before the statement, as
     * `T __liftval = call;` with `exp` reading the temporary, where the statement
     * inliner expands them. A call moves only from where it is always evaluated:
     * one evaluated before anything but constants and the calls moved before it
     * keeps its order with all else; any other only when what is evaluated before
     * it only reads values, its arguments only read values, and its function
     * changes nothing but its own locals, so nothing it moves ahead of can tell.
     * Returns the declarations of the temporaries, or null.
     */
    Statement liftCalls(ref Expression exp)
    {
        if (!exp || !smallCaller())
            return null;
        Statements lifted;
        Expression*[] slots;    // where each lifted call was
        CallExp[] calls;
        bool plain = true;      // whether all evaluated so far only reads values
        bool read;              // whether anything but constants and lifted calls is evaluated so far

        bool liftable(CallExp ce)
        {
            auto ve = ce.e1.isVarExp();
            auto fd = ve ? ve.var.isFuncDeclaration() : null;
            if (!fd || fd.isNested() || fd.needThis() || !ce.type)
                return false;
            auto t = ce.type.toBasetype();
            if (!(t.isTypeBasic() && t.ty != Tvoid) && !t.isTypePointer())
                return false;
            if (!canInline(fd, false, true, pass, eSink) || canInline(fd, false, false, pass, eSink))
                return false;
            if (!read)
                return true;
            if (ce.arguments)
                foreach (arg; *ce.arguments)
                    if (!isPlainRead(arg))
                        return false;
            return writesOnlyLocals(fd);
        }

        void lift(ref Expression e)
        {
            auto ce = e.isCallExp();
            auto vd = new VarDeclaration(ce.loc, ce.type, Identifier.generateId("__liftval"), null);
            vd.storage_class = STC.temp;
            vd._linkage = LINK.d;
            vd.parent = parent;
            auto ve = new VarExp(ce.loc, vd);
            ve.type = vd.type;
            auto cons = new ConstructExp(ce.loc, ve, ce);
            cons.type = vd.type;
            vd._init = new ExpInitializer(ce.loc, cons);
            auto de = new DeclarationExp(ce.loc, vd);
            de.type = Type.tvoid;
            lifted.push(new ExpStatement(ce.loc, de));
            slots ~= &e;
            calls ~= ce;
            auto ve2 = new VarExp(ce.loc, vd);
            ve2.type = vd.type;
            e = ve2;
        }

        static bool constant(Expression e)
        {
            return e.op == EXP.int64 || e.op == EXP.float64 || e.op == EXP.null_ ||
                   e.op == EXP.string_ || e.op == EXP.symbolOffset;
        }

        // walks e in the order it is evaluated, lifting calls while all before them is plain
        void walk(ref Expression e)
        {
            if (!e || !plain)
                return;
            if (isPlainRead(e))
            {
                read |= !constant(e);
                return;
            }
            if (auto ce = e.isCallExp())
            {
                if (liftable(ce))
                    lift(e);
                else
                    plain = false;
                return;
            }
            switch (e.op)
            {
                case EXP.assign, EXP.construct, EXP.blit:
                    /* what is assigned and where are evaluated in either order:
                     * a call is lifted from one side when the other only reads
                     */
                    auto ae = cast(AssignExp)e;
                    if (isPlainRead(ae.e2))
                    {
                        read |= !constant(ae.e2);
                        walk(ae.e1);
                    }
                    else if (isPlainRead(ae.e1, true))
                    {
                        // where a variable is is fixed, where an element is may change
                        read |= !ae.e1.isVarExp();
                        walk(ae.e2);
                    }
                    else
                        plain = false;
                    return;
                case EXP.addAssign, EXP.minAssign, EXP.mulAssign, EXP.andAssign, EXP.orAssign,
                     EXP.xorAssign, EXP.leftShiftAssign, EXP.rightShiftAssign,
                     EXP.unsignedRightShiftAssign:
                    auto be = e.isBinExp();
                    auto t = be.e1.type ? be.e1.type.toBasetype() : null;
                    if (t && (t.isTypeBasic() || t.isTypePointer()) && isPlainRead(be.e1))
                    {
                        read = true;    // the value changed is read first
                        walk(be.e2);
                    }
                    else
                        plain = false;
                    return;
                case EXP.index:
                    auto ie = e.isIndexExp();
                    walk(ie.e1);
                    walk(ie.e2);
                    if (!ie.indexIsInBounds)
                        plain = false;  // the bounds check may fail
                    return;
                case EXP.cast_:
                    auto c = e.isCastExp();
                    walk(c.e1);
                    if (!isPlainRead(c))
                    {
                        auto t = c.type ? c.type.toBasetype() : null;
                        auto f = c.e1.type ? c.e1.type.toBasetype() : null;
                        if ((!t || !f || !(t.isTypeBasic() || t.isTypePointer()) ||
                             !(f.isTypeBasic() || f.isTypePointer())) && !qualifierCast(c))
                            plain = false;
                    }
                    return;
                case EXP.negate, EXP.tilde, EXP.not:
                    walk(e.isUnaExp().e1);
                    return;
                case EXP.add, EXP.min, EXP.mul, EXP.and, EXP.or, EXP.xor,
                     EXP.leftShift, EXP.rightShift, EXP.unsignedRightShift,
                     EXP.lessThan, EXP.lessOrEqual, EXP.greaterThan, EXP.greaterOrEqual,
                     EXP.equal, EXP.notEqual, EXP.identity, EXP.notIdentity:
                    auto be = e.isBinExp();
                    auto t1 = be.e1.type ? be.e1.type.toBasetype() : null;
                    auto t2 = be.e2.type ? be.e2.type.toBasetype() : null;
                    if (!t1 || !t2 || !(t1.isTypeBasic() || t1.isTypePointer()) ||
                        !(t2.isTypeBasic() || t2.isTypePointer()))
                    {
                        plain = false;
                        return;
                    }
                    walk(be.e1);
                    walk(be.e2);
                    return;
                case EXP.andAnd, EXP.orOr:
                    // the right operand is evaluated only sometimes
                    auto be = e.isBinExp();
                    walk(be.e1);
                    plain = plain && isPlainRead(be.e2);
                    return;
                case EXP.question:
                    auto ce = e.isCondExp();
                    walk(ce.econd);
                    plain = plain && isPlainRead(ce.e1) && isPlainRead(ce.e2);
                    return;
                default:
                    plain = false;
                    return;
            }
        }

        walk(exp);
        if (!lifted.length)
            return null;
        // a call the statement inliner leaves is put back
        Statements kept;
        foreach (i, st; lifted[])
        {
            auto before = st;
            inlineScan(st);
            if (st is before)
                *slots[i] = calls[i];
            else
                kept.push(st);
        }
        if (!kept.length)
            return null;
        return new CompoundStatement(exp.loc, kept.move());
    }

    override void visit(ExpStatement s)
    {
        static if (LOG)
        {
            printf("ExpStatement.inlineScan(%s)\n", toChars(s));
        }
        if (!s.exp)
            return;

        Statement inlineScanExpAsStatement(ref Expression exp)
        {
            /* If there's a EXP.call at the top, then it may fail to inline
             * as an Expression. Try to inline as a Statement instead.
             */
            if (auto ce = exp.isCallExp())
            {
                visitCallExp(ce, null, true, false);
                if (eresult)
                    exp = eresult;
                auto s = sresult;
                sresult = null;
                eresult = null;
                return s;
            }

            /* `T v = call;` and `v = call;` of a scalar or POD struct local variable v: when the
             * call cannot be inlined as an expression, and the function being
             * scanned is small enough for the inlined statements not to crowd
             * out its register variables, or the call is given a function literal
             * to inline into the callee, the call is inlined as statements that
             * assign the returned value to v
             */
            VarDeclaration retVar(Expression e1, Expression e2)
            {
                auto ve = e1.isVarExp();
                if (!ve || !e2.isCallExp())
                    return null;
                auto vd = ve.var.isVarDeclaration();
                if (!vd || vd.isDataseg() || vd.isRef() || vd.storage_class & (STC.out_ | STC.lazy_) ||
                    vd.nestedrefs.length)
                    return null;
                auto t = vd.type.toBasetype();
                auto ts = t.isTypeStruct();
                if (!(t.isTypeBasic() && t.ty != Tvoid) && !t.isTypePointer() &&
                    !(ts && ts.sym.isPOD() && !ts.sym.hasCopyCtor))
                    return null;
                if (!e2.type || !equivalent(e2.type.toBasetype(), t))
                    return null;
                /* nor a v the call refers to, as by ref or as this: what it returns is built
                 * in v, so it would change v while it still reads it
                 */
                auto ce = e2.isCallExp();
                if (refersToVar(ce.e1, vd))
                    return null;
                if (ce.arguments)
                    foreach (arg; *ce.arguments)
                        if (refersToVar(arg, vd))
                            return null;
                return vd;
            }
            const small = smallCaller();
            if (auto de = exp.isDeclarationExp())
            {
                auto vd = de.declaration.isVarDeclaration();
                ExpInitializer ie;
                AssignExp ae;
                if (vd && vd._init && (ie = vd._init.isExpInitializer()) !is null &&
                    (ae = ie.exp.isConstructExp()) !is null && ae.e1.isVarExp() &&
                    ae.e1.isVarExp().var == vd && retVar(ae.e1, ae.e2) &&
                    (small || givenLiteral(ae.e2.isCallExp())))
                {
                    auto call = ae.e2.isCallExp();
                    inlineScan(exp);
                    if (ie.exp !is ae || ae.e2 !is call)
                        return null;            // inlined as an expression
                    visitCallExp(call, ae.e1, true, false);
                    auto s = sresult;
                    sresult = null;
                    eresult = null;
                    if (!s)
                        return null;
                    vd._init = new VoidInitializer(vd._init.loc);
                    auto a = Statements(new ExpStatement(exp.loc, de), s);
                    return new CompoundStatement(exp.loc, a.move());
                }
            }
            if (auto ae = exp.isAssignExp())
            {
                if ((ae.op == EXP.assign || ae.op == EXP.construct) && retVar(ae.e1, ae.e2) &&
                    (small || givenLiteral(ae.e2.isCallExp())))
                {
                    auto call = ae.e2.isCallExp();
                    inlineScan(exp);
                    if (exp !is ae || ae.e2 !is call)
                        return null;            // inlined as an expression
                    visitCallExp(call, ae.e1, true, false);
                    auto s = sresult;
                    sresult = null;
                    eresult = null;
                    return s;
                }

                /* `a[i] = call;` given a function literal, of a local a that no nested function
                 * refers to, so the call cannot change it, as
                 * `auto j = i; T tmp = void; tmp = call; a[j] = tmp;` with the call inlined
                 * as statements, the index evaluated before the call as it is otherwise
                 */
                auto call = ae.e2.isCallExp();
                auto ie = ae.e1.isIndexExp();
                auto ave = ie ? ie.e1.isVarExp() : null;
                auto av = ave ? ave.var.isVarDeclaration() : null;
                if (ae.op == EXP.assign && call && givenLiteral(call) && av &&
                    !av.isDataseg() && !av.isRef() && !(av.storage_class & (STC.out_ | STC.lazy_)) &&
                    !av.nestedrefs.length && !hasSideEffect(ie.e2) &&
                    call.type && equivalent(call.type.toBasetype(), ae.e1.type.toBasetype()))
                {
                    VarExp temp(Type t, const(char)[] name, Initializer init)
                    {
                        auto vd = new VarDeclaration(ae.loc, t, Identifier.generateId(name), init);
                        vd.storage_class = STC.temp;
                        vd._linkage = LINK.d;
                        vd.parent = parent;
                        auto ve = new VarExp(ae.loc, vd);
                        ve.type = t;
                        return ve;
                    }
                    auto val = temp(call.type, "__inlineval", new VoidInitializer(ae.loc));
                    if (!retVar(val, call))
                        return null;
                    inlineScan(exp);
                    if (exp !is ae || ae.e2 !is call)
                        return null;            // inlined as an expression
                    visitCallExp(call, val, true, false);
                    auto s = sresult;
                    sresult = null;
                    eresult = null;
                    if (!s)
                        return null;
                    Statement declare(VarExp ve)
                    {
                        auto de = new DeclarationExp(ae.loc, ve.var);
                        de.type = Type.tvoid;
                        return new ExpStatement(ae.loc, de);
                    }
                    auto a = Statements();
                    if (!ie.e2.isIntegerExp())
                    {
                        auto idx = temp(ie.e2.type, "__inlineidx", new ExpInitializer(ae.loc, ie.e2));
                        auto vd = idx.var.isVarDeclaration();
                        auto ce = new ConstructExp(ae.loc, vd, ie.e2);
                        ce.type = vd.type;
                        (cast(ExpInitializer)vd._init).exp = ce;
                        a.push(declare(idx));
                        auto idx2 = new VarExp(ae.loc, vd);
                        idx2.type = vd.type;
                        ie.e2 = idx2;
                    }
                    a.push(declare(val));
                    a.push(s);
                    auto val2 = new VarExp(ae.loc, val.var);
                    val2.type = val.type;
                    ae.e2 = val2;
                    a.push(new ExpStatement(ae.loc, ae));
                    return new CompoundStatement(ae.loc, a.move());
                }
            }

            /* If there's a CondExp or CommaExp at the top, then its
             * sub-expressions may be inlined as statements.
             */
            if (auto e = exp.isCondExp())
            {
                inlineScan(e.econd);
                auto s1 = inlineScanExpAsStatement(e.e1);
                auto s2 = inlineScanExpAsStatement(e.e2);
                if (!s1 && !s2)
                    return null;
                auto ifbody   = !s1 ? new ExpStatement(e.e1.loc, e.e1) : s1;
                auto elsebody = !s2 ? new ExpStatement(e.e2.loc, e.e2) : s2;
                return new IfStatement(exp.loc, null, e.econd, ifbody, elsebody, exp.loc);
            }
            if (auto e = exp.isCommaExp())
            {
                /* If expression declares temporaries which have to be destructed
                 * at the end of the scope then it is better handled as an expression.
                 */
                if (expNeedsDtor(e.e1))
                {
                    inlineScan(exp);
                    return null;
                }

                auto s1 = inlineScanExpAsStatement(e.e1);
                auto s2 = inlineScanExpAsStatement(e.e2);
                if (!s1 && !s2)
                    return null;
                auto a = Statements(!s1 ? new ExpStatement(e.e1.loc, e.e1) : s1,
                                    !s2 ? new ExpStatement(e.e2.loc, e.e2) : s2);
                return new CompoundStatement(exp.loc, a.move());
            }

            // inline as an expression
            inlineScan(exp);
            return null;
        }

        Statement lifted;
        if (auto de = s.exp.isDeclarationExp())
        {
            auto vd = de.declaration.isVarDeclaration();
            auto ie = vd && vd._init ? vd._init.isExpInitializer() : null;
            auto ae = ie ? ie.exp.isConstructExp() : null;
            if (ae && !ae.e2.isCallExp())
                lifted = liftCalls(ae.e2);
        }
        else if (!s.exp.isCallExp())
        {
            auto ae = s.exp.op == EXP.assign || s.exp.op == EXP.construct ? cast(AssignExp)s.exp : null;
            if (!ae || !ae.e2.isCallExp() || !ae.e1.isVarExp())
                lifted = liftCalls(s.exp);
        }
        sresult = inlineScanExpAsStatement(s.exp);
        if (lifted)
            sresult = new CompoundStatement(s.loc, lifted, sresult ? sresult : s);
    }

    override void visit(CompoundStatement s)
    {
        foreach (i; 0 .. s.statements.length)
        {
            inlineScan(s.statements[i]);
        }
    }

    override void visit(UnrolledLoopStatement s)
    {
        foreach (i; 0 .. s.statements.length)
        {
            inlineScan(s.statements[i]);
        }
    }

    override void visit(ScopeStatement s)
    {
        inlineScan(s.statement);
    }

    override void visit(WhileStatement s)
    {
        ++loopDepth;
        inlineScan(s.condition);
        inlineScan(s._body);
        --loopDepth;
    }

    override void visit(DoStatement s)
    {
        ++loopDepth;
        inlineScan(s._body);
        inlineScan(s.condition);
        --loopDepth;
    }

    override void visit(ForStatement s)
    {
        inlineScan(s._init);
        ++loopDepth;
        inlineScan(s.condition);
        inlineScan(s.increment);
        inlineScan(s._body);
        --loopDepth;
    }

    override void visit(ForeachStatement s)
    {
        inlineScan(s.aggr);
        ++loopDepth;
        inlineScan(s._body);
        --loopDepth;
    }

    override void visit(ForeachRangeStatement s)
    {
        inlineScan(s.lwr);
        inlineScan(s.upr);
        ++loopDepth;
        inlineScan(s._body);
        --loopDepth;
    }

    override void visit(IfStatement s)
    {
        auto lifted = s.param ? null : liftCalls(s.condition);
        inlineScan(s.condition);
        // a branch that cannot complete, where the other can, is the error path
        const ifCold = endsInNoReturn(s.ifbody);
        const elseCold = endsInNoReturn(s.elsebody);
        scanCold(s.ifbody, ifCold && !elseCold);
        scanCold(s.elsebody, elseCold && !ifCold);
        if (lifted)
            sresult = new CompoundStatement(s.loc, lifted, s);
    }

    override void visit(SwitchStatement s)
    {
        //printf("SwitchStatement.inlineScan()\n");
        inlineScan(s.condition);
        inlineScan(s._body);
        Statement sdefault = s.sdefault;
        inlineScan(sdefault);
        s.sdefault = cast(DefaultStatement)sdefault;
        if (s.cases)
        {
            foreach (i; 0 .. s.cases.length)
            {
                Statement scase = (*s.cases)[i];
                inlineScan(scase);
                (*s.cases)[i] = cast(CaseStatement)scase;
            }
        }
    }

    override void visit(CaseStatement s)
    {
        //printf("CaseStatement.inlineScan()\n");
        inlineScan(s.exp);
        scanCold(s.statement, endsInNoReturn(s.statement));
    }

    override void visit(DefaultStatement s)
    {
        scanCold(s.statement, endsInNoReturn(s.statement));
    }

    override void visit(ReturnStatement s)
    {
        //printf("ReturnStatement.inlineScan()\n");

        if (!s.exp)
            return;

        auto lifted = liftCalls(s.exp);
        Expression e0;
        Expression elast = Expression.extractLast(s.exp, e0);
        inlineScan(e0);

        if (auto ce = elast.isCallExp())
        {
            visitCallExp(ce, null, false, true);

            if (eresult)
            {
                elast = eresult;
                eresult = null;
            }
        }
        else
        {
            inlineScan(elast);
        }

        s.exp = Expression.combine(e0, elast);
        if (lifted)
            sresult = new CompoundStatement(s.loc, lifted, s);
    }

    override void visit(SynchronizedStatement s)
    {
        inlineScan(s.exp);
        inlineScan(s._body);
    }

    override void visit(WithStatement s)
    {
        if (s.wthis && s.wthis._init)
        {
            if (auto ie = s.wthis._init.isExpInitializer())
            {
                inlineScan(ie.exp);
            }
        }
        inlineScan(s._body);
    }

    override void visit(TryCatchStatement s)
    {
        inlineScan(s._body);
        if (s.catches)
        {
            foreach (c; *s.catches)
            {
                scanCold(c.handler, true);
            }
        }
    }

    override void visit(TryFinallyStatement s)
    {
        inlineScan(s._body);
        inlineScan(s.finalbody);
    }

    override void visit(ThrowStatement s)
    {
        ++coldDepth;
        inlineScan(s.exp);
        --coldDepth;
    }

    override void visit(LabelStatement s)
    {
        inlineScan(s.statement);
    }

    /// Scan `s`, as a rarely run path if `cold`
    void scanCold(ref Statement s, bool cold)
    {
        coldDepth += cold;
        inlineScan(s);
        coldDepth -= cold;
    }

    /********************************
     * Scan Statement s for inlining opportunities,
     * and if found replace s with an inlined one.
     * Params:
     *  s = Statement to be scanned and updated
     */
    void inlineScan(ref Statement s)
    {
        if (!s)
            return;
        assert(sresult is null);
        s.accept(this);
        if (sresult)
        {
            s = sresult;
            sresult = null;
        }
    }

    /* -------------------------- */
    void arrayInlineScan(Expressions* arguments)
    {
        if (arguments)
        {
            foreach (i; 0 .. arguments.length)
            {
                inlineScan((*arguments)[i]);
            }
        }
    }

    override void visit(Expression e)
    {
    }

    override void visit(DeclarationExp e)
    {
        if (VarDeclaration vd = e.declaration.isVarDeclaration())
        {
            if (TupleDeclaration td = vd.toAlias().isTupleDeclaration())
            {
                foreach (o; *td.objects)
                {
                    if (auto te = o.isExpression())
                    {
                        inlineScan(te);
                    }
                }
            }
            else if (vd._init)
            {
                if (ExpInitializer ie = vd._init.isExpInitializer())
                {
                    inlineScan(ie.exp);
                }
            }
        }
    }

    override void visit(UnaExp e)
    {
        inlineScan(e.e1);
    }

    override void visit(CastExp e)
    {
        if (e.lowering)
        {
            inlineScan(e.lowering);
        }
        else
        {
            inlineScan(e.e1);
        }
    }

    override void visit(AssertExp e)
    {
        inlineScan(e.e1);
        // the message is evaluated only when the assertion fails
        ++coldDepth;
        inlineScan(e.msg);
        --coldDepth;
    }

    override void visit(ThrowExp e)
    {
        ++coldDepth;
        inlineScan(e.e1);
        --coldDepth;
    }

    override void visit(CatExp e)
    {
        if (e.lowering)
        {
            inlineScan(e.lowering);
            return;
        }

        inlineScan(e.e1);
        inlineScan(e.e2);
    }

    override void visit(CatAssignExp e)
    {
        if (e.lowering)
            inlineScan(e.lowering);
        else
            visit(cast(BinExp) e);
    }

    override void visit(BinExp e)
    {
        inlineScan(e.e1);
        inlineScan(e.e2);
    }

    override void visit(EqualExp e)
    {
        if (e.lowering)
        {
            inlineScan(e.lowering);
        }
        else
        {
            visit(cast(BinExp)e);
        }
    }

    override void visit(AssignExp e)
    {
        void inlineConstruction(AssignExp e)
        {
            Expression e0;
            Expression elast = Expression.extractLast(e.e2, e0);
            inlineScan(e0);   // Side effects

            auto ce = elast.isCallExp();
            if (ce && ce.f)
            {
                visitCallExp(ce, e.e1, false, false);

                if (eresult)
                {
                    eresult = Expression.combine(e0, eresult);
                    //printf("call with nrvo: %s ==> %s\n", e.toChars(), eresult.toChars());
                    return;
                }
            }

            inlineScan(elast);
            e.e2 = Expression.combine(e0, elast);
        }

        inlineScan(e.e1); // LHS

        // Look for NRVO and emplace the return value into LHS directly
        // when expanding the function call on RHS.
        if (e.op == EXP.construct &&
            (e.e2.type.ty == Tstruct || e.e2.type.ty == Tsarray))
        {
            bool refInit = false;

            /* Inlining:
             *   S s = ...;    // initializing by rvalue
             * No NRVO on:
             *   ref S s = ...;
             */
            if (auto ve = e.e1.isVarExp())
                refInit = (ve.var.storage_class & (STC.out_ | STC.ref_)) != 0;

            if (!refInit)
            {
                inlineConstruction(e);
                return;
            }
        }

        inlineScan(e.e2); // RHS if not construction
    }

    override void visit(ConstructExp e)
    {
        if (e.lowering)
            inlineScan(e.lowering);
        else
            visit(cast(AssignExp) e);
    }

    override void visit(LoweredAssignExp e)
    {
        inlineScan(e.lowering);
    }

    override void visit(CallExp e)
    {
        //printf("CallExp.inlineScan() %s\n", e.toChars());
        visitCallExp(e, null, false, false);
    }

    /**************************************
     * Check function call to see if can be inlined,
     * and then inline it if it can.
     * Params:
     *  e = the function call
     *  eret = if !null, then this is the lvalue of the nrvo function result
     *  asStatements = if inline as statements rather than as an Expression
     *  propagateNRVO = if the parent function returns the result immediately,
     *      so NRVO variables have to be preserved in the parent
     * Returns:
     *  this.eresult if asStatements == false
     *  this.sresult if asStatements == true
     */
    void visitCallExp(CallExp e, Expression eret, bool asStatements, bool propagateNRVO)
    {
        /* Inlining a call outside loops saves little time, while what is
         * inlined is optimized again in each caller: past a budget, only
         * functions about as cheap as the call are inlined there
         */
        bool withinBudget(FuncDeclaration fd)
        {
            enum cheapCost = 10;        // cost of a function about as cheap as the call
            enum budget = 500;          // cost a function may inline outside loops
            if (fd.inlining == PINLINE.always)
                return true;
            // a function literal, written for where it is called
            if (fd.isFuncLiteralDeclaration())
                return true;
            // a function given a function literal, as a delegate to call, so the literal
            // can be inlined into it
            if (givenLiteral(e))
                return true;
            const cost = inlineCostOf(fd);
            /* on a path that runs rarely, as one ending in a throw, or in a call of a
             * function that never returns, inlining saves next to nothing and only
             * grows the caller
             */
            if (coldDepth || isNoReturn(e.type) || (cost > cheapCost && alwaysThrows(fd)))
                return cost <= cheapCost;
            if (loopDepth)
            {
                /* what is too costly outside loops is inlined into loops up to a
                 * budget, as each inlined function is optimized again in the caller
                 */
                // more in deeper loops, which run more often
                const depth = loopDepth < 3 ? loopDepth : 3;
                const loopBudget = (registersToSpare() ? 1200 : 700) * depth;
                if (!tooCostlyOutsideLoops(cost))
                    return true;
                const c = expressionCost(cost);
                if (loopInlinedCost + c > loopBudget)
                    return false;
                loopInlinedCost += c;
                return true;
            }
            if (tooCostlyOutsideLoops(cost))
                return false;
            if (cost <= cheapCost)
                return true;
            if (inlinedCost + cost > budget)
                return false;
            inlinedCost += cost;
            return true;
        }

        inlineScan(e.e1);
        arrayInlineScan(e.arguments);

        void inlineFd(FuncDeclaration fd, Expression explicitThis)
        {
            /* If the arguments generate temporaries that need destruction, the destruction
             * must be done after the function body is executed.
             * The easiest way to accomplish that is to do the inlining as an Expression.
             * https://issues.dlang.org/show_bug.cgi?id=16652
             */
            bool asStates = asStatements;
            if (asStates)
            {
                if (fd.semanticRun == pass && fd.inlineStatusExp == ILS.yes)
                    asStates = false;           // inline as expressions
                                                // so no need to recompute argumentsNeedDtors()
                else if (argumentsNeedDtors(e.arguments))
                    asStates = false;
            }

            bool hasThis;
            if (explicitThis)
            {
                /* If ethis is explicitly given by a DotVarExp, fd can be inlined
                 * as long as it does not require another `this` pointer.
                 * Inlining the case where one pointer can be accessed from another
                 * is not implemented yet.
                 */
                hasThis = !fd.isNested();
            }
            else
            {
                /* Otherwise, `this` pointer is captured from parent. Only allow
                 * immediate nested functions to reference `this` pointer.
                 */
                hasThis = parent == fd.toParent2();
            }

            if (canInline(fd, hasThis, asStates, pass, eSink) && withinBudget(fd) && inlineAllowed(fd, parent, e.loc))
            {
                expandInline(e, fd, parent, eret, explicitThis, asStates, propagateNRVO,
                             eresult, sresult, again);
                if (asStatements && eresult)
                {
                    sresult = new ExpStatement(eresult.loc, eresult);
                    eresult = null;
                }
            }
        }

        FuncDeclaration resolveCallTarget(Expression e, out Expression explicitThis)
        {
            /* Peel exactly one layer of (*fptr)() or (*&f)().
             */
            if (auto pe = e.isPtrExp())
            {
                if (pe.e1.isVarExp() || pe.e1.isFuncExp())
                    e = pe.e1;
                else if (auto se = pe.e1.isSymOffExp())
                    return se.var.isFuncDeclaration();
                else
                    return null;
            }

            // a function called through a pointer to it cast to add attributes, as
            // (cast(F) &f)() calls f as if pure
            if (auto ce = e.isCastExp())
                return attributeCastTarget(ce);

            // a literal called directly, as where a delegate parameter was inlined
            if (auto fe = e.isFuncExp())
                return fe.fd;
            if (auto de = e.isDelegateExp())
                if (de.func && de.func.isFuncLiteralDeclaration())
                    return de.func;

            /* Pattern match various ASTs looking for indirect function calls, delegate calls,
             * function literal calls, delegate literal calls, and dot member calls.
             * If so, and that is only assigned its _init.
             * If so, do 'copy propagation' of the _init value and try to inline it.
             */
            if (auto ve = e.isVarExp())
            {
                if (FuncDeclaration fd = ve.var.isFuncDeclaration())
                    return fd;

                auto v = ve.var.isVarDeclaration();
                if (!v || !v._init || !onlyOneAssign(v, parent))
                    return null;

                //printf("init: %s\n", v._init.toChars());
                auto ei = v._init.isExpInitializer();
                if (!ei || (ei.exp.op != EXP.blit && ei.exp.op != EXP.construct))
                    return null;

                Expression e2 = (cast(AssignExp)ei.exp).e2;
                if (auto se = e2.isSymOffExp())
                {
                    // function pointer call
                    return se.var.isFuncDeclaration();
                }
                else if (auto fe = e2.isFuncExp())
                {
                    // function/delegate literal call
                    return fe.fd;
                }
                else if (auto de = e2.isDelegateExp())
                {
                    if (auto ve2 = de.e1.isVarExp())
                    {
                        return ve2.var.isFuncDeclaration();
                    }
                }
            }
            else if (auto dve = e.isDotVarExp())
            {
                if (dve.e1.op == EXP.call && dve.e1.type.toBasetype().ty == Tstruct)
                {
                    /* To create ethis, we'll need to take the address
                     * of dve.e1, but this won't work if dve.e1 is
                     * a function call.
                     */
                    return null;
                }

                explicitThis = dve.e1;
                return dve.var.isFuncDeclaration();
            }
            else if (auto fe = e.isFuncExp())
            {
                return fe.fd;
            }

            return null;
        }

        //printf("visitCallExp() %s\n", e.toChars());
        Expression explicitThis;
        FuncDeclaration fd = resolveCallTarget(e.e1, explicitThis);

        if (!fd || fd == parent)
            return;

        inlineFd(fd, explicitThis);

        if (global.params.v.verbose && (eresult || sresult))
        {
            auto eSink = global.errorSink;
            eSink.message(Loc.init, "inlined   %s =>\n          %s", fd.toPrettyChars(), parent.toPrettyChars());
        }

        if (eresult && e.type.ty != Tvoid)
        {
            Expression ex = eresult;
            while (ex.op == EXP.comma)
            {
                ex.type = e.type;
                ex = ex.isCommaExp().e2;
            }
            ex.type = e.type;
        }
    }

    override void visit(SliceExp e)
    {
        inlineScan(e.e1);
        inlineScan(e.lwr);
        inlineScan(e.upr);
    }

    override void visit(TupleExp e)
    {
        //printf("TupleExp.inlineScan()\n");
        inlineScan(e.e0);
        arrayInlineScan(e.exps);
    }

    override void visit(ArrayLiteralExp e)
    {
        //printf("ArrayLiteralExp.inlineScan()\n");
        inlineScan(e.basis);
        arrayInlineScan(e.elements);
    }

    override void visit(AssocArrayLiteralExp e)
    {
        //printf("AssocArrayLiteralExp.inlineScan()\n");
        arrayInlineScan(e.keys);
        arrayInlineScan(e.values);
    }

    override void visit(StructLiteralExp e)
    {
        //printf("StructLiteralExp.inlineScan()\n");
        if (e.stageflags & StructLiteralExp.StageFlags.inlineScan)
            return;
        const old = e.stageflags;
        e.stageflags |= StructLiteralExp.StageFlags.inlineScan;
        arrayInlineScan(e.elements);
        e.stageflags = old;
    }

    override void visit(ArrayExp e)
    {
        //printf("ArrayExp.inlineScan()\n");
        inlineScan(e.e1);
        arrayInlineScan(e.arguments);
    }

    override void visit(CondExp e)
    {
        inlineScan(e.econd);
        inlineScan(e.e1);
        inlineScan(e.e2);
    }

    /********************************
     * Scan Expression e for inlining opportunities,
     * and if found replace e with an inlined one.
     * Params:
     *  e = Expression to be scanned and updated
     */
    void inlineScan(ref Expression e)
    {
        if (!e)
            return;
        assert(eresult is null);
        e.accept(this);
        if (eresult)
        {
            e = eresult;
            eresult = null;
        }
    }
}

/***********************************************************
 * Walk the trees, looking for functions to inline.
 * Inline any that can be.
 */
private extern (C++) final class InlineScanVisitorDsymbol : Visitor
{
    alias visit = Visitor.visit;

public:
    PASS pass;
    ErrorSink eSink;

    extern (D) this(PASS pass, ErrorSink eSink) scope @safe
    {
        this.pass = pass;
        this.eSink = eSink;
    }

    /*************************************
     * Look for function inlining possibilities.
     */
    override void visit(Dsymbol d)
    {
        // Most Dsymbols aren't functions
    }

    override void visit(FuncDeclaration fd)
    {
        static if (LOG)
        {
            printf("FuncDeclaration.inlineScan('%s')\n", fd.toPrettyChars());
        }

        if (!fd.fbody || fd.isNaked || fd.skipCodegen)
            return;

        if (fd.semanticRun < PASS.semantic3done)
            return;

        if (fd.semanticRun == pass && fd.inlineScanned)
            return;

        if (fd.isUnitTestDeclaration() && !global.params.useUnitTests)
            return;

        if (!fd.hasAlwaysInlines && pass == PASS.inlinePragma)
            return;

        if (fd.semanticRun != pass)
        {
            fd.inlineStatusExp = ILS.uninitialized;
            fd.inlineStatusStmt = ILS.uninitialized;
        }

        fd.inlineScanned = true;
        fd.semanticRun = pass;

        import dmd.timetrace;
        timeTraceBeginEvent(TimeTraceEventType.inlineFunction);
        scope (exit) timeTraceEndEvent(TimeTraceEventType.inlineFunction, fd);

        scope InlineScanVisitor v = new InlineScanVisitor(fd, pass, eSink);

        do
        {
            fd.inlineNest++;
            v.reset();
            v.inlineScan(fd.fbody);
            fd.inlineNest--;
        } while (v.again);

        if (fd.localsymtab)
        {
            // Sort by name: table order follows Identifier addresses,
            // and inline decisions are order-dependent
            Dsymbols symbols;
            symbols.reserve(fd.localsymtab.length);
            foreach (keyValue; fd.localsymtab.tab.asRange)
                symbols.push(keyValue.value);

            static int compare(const Dsymbol* a, const Dsymbol* b)
            {
                return strcmp(a.ident.toChars(), b.ident.toChars());
            }
            symbols.sort!compare();

            foreach (s; symbols)
                s.accept(this);
        }
    }

    override void visit(AttribDeclaration d)
    {
        if (Dsymbols* decls = d.include(null))
        {
            foreach (i; 0 .. decls.length)
            {
                Dsymbol s = (*decls)[i];
                //printf("AttribDeclaration.inlineScan %s\n", s.toChars());
                s.accept(this);
            }
        }
    }

    override void visit(AggregateDeclaration ad)
    {
        //printf("AggregateDeclaration.inlineScan(%s)\n", toChars());
        if (ad.members)
        {
            foreach (i; 0 .. ad.members.length)
            {
                Dsymbol s = (*ad.members)[i];
                //printf("inline scan aggregate symbol '%s'\n", s.toChars());
                s.accept(this);
            }
        }
    }

    override void visit(TemplateInstance ti)
    {
        static if (LOG)
        {
            printf("TemplateInstance.inlineScan('%s')\n", ti.toChars());
        }
        // in the pragma(inline) pass, only the instances enclosing functions it inlines into
        if (pass == PASS.inlinePragma && !ti.hasAlwaysInlines)
            return;
        if (!ti.errors && ti.members)
        {
            foreach (i; 0 .. ti.members.length)
            {
                Dsymbol s = (*ti.members)[i];
                s.accept(this);
            }
        }
    }
}

/***********************************************************
 * Scan function implementations in Module m looking for functions that can be inlined,
 * and inline them in situ.
 *
 * Params:
 *    m = module to scan
 *    pass = the current pass (inline1 or inline2)
 *    eSink = where to report errors
 */
private void inlineScanModule(Module m, PASS pass, ErrorSink eSink)
{
    assert(pass == PASS.inlinePragma || pass == PASS.inlineAll);

    // Note that modules get their own scope, from scratch.
    // This is so regardless of where in the syntax a module
    // gets imported, it is unaffected by context.

    //printf("Module = %p\n", m.sc.scopesym);

    scope v = new InlineScanVisitorDsymbol(pass, eSink);

    foreach (i; 0 .. m.members.length)
    {
        Dsymbol s = (*m.members)[i];
        s.accept(v);
    }

    m.semanticRun = pass;
}

/***********************************************************
 * Whether the statements from index i on end with a return statement,
 * the last of them being one.
 */
/// Whether statements[i .. $] have no return statement in them
bool restHasNoReturn(ref Statements statements, size_t i)
{
    import dmd.visitor.postorder : walkPostorder;
    extern (C++) final class Finder : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        extern (D) this() scope {}
        override void visit(Statement s) {}
        override void visit(ReturnStatement s) { stop = true; }
    }
    foreach (st; statements[i .. $])
    {
        if (!st)
            continue;
        scope Finder f = new Finder();
        if (walkPostorder(st, f))
            return false;
    }
    return true;
}

bool restEndsWithReturn(ref Statements statements, size_t i)
{
    if (i >= statements.length)
        return false;
    foreach (st; statements[i .. $])
        if (!st)
            return false;
    return statements[$ - 1].endsWithReturnStatement() !is null;
}

/***********************************************************
 * A label of its own in function fd, for the returns of an inlined function to go to
 */
private LabelDsymbol returnLabel(Loc loc, FuncDeclaration fd)
{
    auto id = Identifier.generateId("__inlineret");
    auto ld = fd.searchLabel(id, loc);
    ld.statement = new LabelStatement(loc, id, null);
    return ld;
}

/// Whether id names a label returnLabel() makes
package(dmd) bool isReturnLabel(Identifier id)
{
    import core.stdc.string : strncmp;
    return id && strncmp(id.toChars(), "__inlineret", 11) == 0;
}

private Statement gotoLabel(Loc loc, LabelDsymbol ld)
{
    auto g = new GotoStatement(loc, ld.ident);
    g.label = ld;
    return g;
}

/***********************************************************
 * Whether fd returns from anywhere but its last statement, so inlined as
 * statements its returns go to the end
 */
private bool returnsBeforeEnd(FuncDeclaration fd)
{
    import dmd.visitor.statement_rewrite_walker : StatementRewriteWalker;
    // the function's own statements, not those of what it declares
    extern (C++) final class Returns : StatementRewriteWalker
    {
        alias visit = StatementRewriteWalker.visit;
        int count;
        ReturnStatement last;
        override void visit(ReturnStatement s) { ++count; last = s; }
    }
    if (!fd.fbody)
        return false;
    scope v = new Returns();
    fd.fbody.accept(v);
    if (v.count == 0)
        return false;
    return v.count > 1 || fd.fbody.endsWithReturnStatement() !is v.last;
}

/// Whether s has a break or continue anywhere in it
private bool hasBreakOrContinue(Statement s)
{
    import dmd.visitor.statement_rewrite_walker : StatementRewriteWalker;
    extern (C++) final class Leaves : StatementRewriteWalker
    {
        alias visit = StatementRewriteWalker.visit;
        bool found;
        override void visit(BreakStatement s) { found = true; }
        override void visit(ContinueStatement s) { found = true; }
    }
    scope v = new Leaves();
    s.accept(v);
    return v.found;
}

/***********************************************************
 * Whether e refers to the variable v anywhere in it
 */
private bool refersToVar(Expression e, VarDeclaration v)
{
    extern (C++) final class Finder : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        VarDeclaration v;
        extern (D) this(VarDeclaration v) @safe { this.v = v; }
        override void visit(Expression e) {}
        override void visit(VarExp e) { if (e.var is v) stop = true; }
        override void visit(SymOffExp e) { if (e.var is v) stop = true; }
    }
    if (!e)
        return false;
    scope f = new Finder(v);
    return walkPostorder(e, f);
}

/***********************************************************
 * Whether the next expansion may be done: all of them, or with DMD_INLINE_MAX=n
 * set, the first n, to find one that goes wrong by bisection; DMD_INLINE_LOG lists
 * them with their numbers
 */
private bool inlineAllowed(FuncDeclaration fd, FuncDeclaration parent, Loc loc)
{
    import core.stdc.stdlib : getenv, atoi;
    __gshared int max = -2;
    __gshared int count;
    __gshared bool log;
    if (max == -2)
    {
        auto m = getenv("DMD_INLINE_MAX");
        max = m ? atoi(m) : -1;
        log = getenv("DMD_INLINE_LOG") !is null;
    }
    if (max >= 0 && count >= max)
        return false;
    if (log)
        printf("inline %d: %s into %s at %s\n", count, fd.toPrettyChars(), parent.toPrettyChars(), loc.toChars());
    ++count;
    return true;
}

/***********************************************************
 * The function ce casts a pointer to, when the type cast to differs from the
 * function's only in attributes, as `(cast(F) &f)` that calls `f` as if it were
 * `pure` or `nothrow`; else null
 */
private FuncDeclaration attributeCastTarget(CastExp ce)
{
    FuncDeclaration f;
    if (auto se = ce.e1.isSymOffExp())
    {
        if (se.offset == 0)
            f = se.var.isFuncDeclaration();
    }
    else if (auto ae = ce.e1.isAddrExp())
    {
        if (auto ve = ae.e1.isVarExp())
            f = ve.var.isFuncDeclaration();
    }
    if (!f || f.needThis() || !f.type || !ce.to)
        return null;
    auto tp = ce.to.toBasetype().isTypePointer();
    if (!tp)
        return null;
    auto t2 = tp.next.isTypeFunction();
    auto t1 = f.type.isTypeFunction();
    if (!t1 || !t2 || t1.linkage != t2.linkage || t1.isRef != t2.isRef ||
        t1.parameterList.varargs != t2.parameterList.varargs ||
        t1.parameterList.length != t2.parameterList.length ||
        !t1.next || !t2.next || !t1.next.equals(t2.next))
        return null;
    foreach (i; 0 .. t1.parameterList.length)
    {
        auto p1 = t1.parameterList[i];
        auto p2 = t2.parameterList[i];
        if (!p1.type.equals(p2.type) ||
            (p1.storageClass & (STC.ref_ | STC.out_ | STC.lazy_)) != (p2.storageClass & (STC.ref_ | STC.out_ | STC.lazy_)))
            return null;
    }
    return f;
}

/***********************************************************
 * Whether fd refers to nested functions only because function literals of its
 * own refer to its variables, rather than for its contracts, what it overrides,
 * or functions given its variables as aliases: the literals, once inlined into
 * it, read its variables directly, not through its frame
 */
private bool onlyClosureVars(FuncDeclaration fd)
{
    if (!fd.closureVars.length || fd.fdrequire || fd.fdensure ||
        fd.foverrides.length && fd.isVirtualMethod())
        return false;
    foreach (v; fd.closureVars)
        foreach (f; v.nestedrefs)
        {
            if (!f.isFuncLiteralDeclaration() || f.hasDualContext || f.toParent2() !is fd)
                return false;
        }
    return true;
}

/***********************************************************
 * Whether the body of fd still has a function literal, a delegate or a nested
 * function in it, once the calls in it that can be have been inlined
 */
private bool refersToNested(FuncDeclaration fd)
{
    import dmd.visitor : SemanticTimeTransitiveVisitor;
    extern (C++) final class NestedFinder : SemanticTimeTransitiveVisitor
    {
        alias visit = SemanticTimeTransitiveVisitor.visit;
        bool found;

        override void visit(FuncExp e) { found = true; }
        override void visit(DelegateExp e) { found = true; }
        override void visit(TemplateDeclaration d) { found = true; }
        override void visit(ScopeExp e) { found = true; }
        override void visit(VarExp e)
        {
            if (auto f = e.var.isFuncDeclaration())
                found |= f.isNested();
        }
        override void visit(SymOffExp e)
        {
            if (auto f = e.var.isFuncDeclaration())
                found |= f.isNested();
        }
        // a member function with a second context, as from an alias of a local
        override void visit(DotVarExp e)
        {
            if (auto f = e.var.isFuncDeclaration())
                found |= f.isNested() || f.hasDualContext;
            super.visit(e);
        }
        override void visit(CallExp e)
        {
            if (e.f)
                found |= e.f.isNested() || e.f.hasDualContext;
            super.visit(e);
        }
        override void visit(DeclarationExp e)
        {
            // what is declared but variables, as functions, structs and templates, may refer to the frame
            auto d = e.declaration;
            if (d.isVarDeclaration())
                super.visit(e);
            else if (!d.isAliasDeclaration() && !d.isEnumDeclaration())
                found = true;
        }
    }
    if (!fd.fbody)
        return false;
    scope v = new NestedFinder();
    fd.fbody.accept(v);
    return v.found;
}

/***********************************************************
 * Whether e only reads values, without calls, side effects or any way to fault,
 * so it may be evaluated after a call it comes before that changes nothing
 */
private bool isPlainRead(Expression e, bool boundsChecked = false)
{
    if (!e)
        return true;
    bool basic(Type t)
    {
        auto tb = t ? t.toBasetype() : null;
        return tb && (tb.isTypeBasic() && tb.ty != Tvoid || tb.isTypePointer());
    }
    switch (e.op)
    {
        case EXP.int64, EXP.float64, EXP.null_, EXP.string_, EXP.symbolOffset:
            return true;
        case EXP.variable:
            auto vd = e.isVarExp().var.isVarDeclaration();
            return vd && !(vd.storage_class & STC.lazy_);
        case EXP.dotVariable:
            auto dve = e.isDotVarExp();
            return dve.var.isVarDeclaration() && dve.e1.type &&
                   dve.e1.type.toBasetype().isTypeStruct() && isPlainRead(dve.e1, boundsChecked);
        case EXP.slice:
            auto se = e.isSliceExp();
            return !se.lwr && !se.upr && isPlainRead(se.e1, boundsChecked);
        case EXP.arrayLength:
            return isPlainRead(e.isArrayLengthExp().e1, boundsChecked);
        case EXP.index:
            auto ie = e.isIndexExp();
            auto ta = ie.e1.type ? ie.e1.type.toBasetype() : null;
            if (!ta || !(ta.isTypeSArray() || boundsChecked && ta.isTypeDArray()))
                return false;
            return (ie.indexIsInBounds || boundsChecked) &&
                   isPlainRead(ie.e1, boundsChecked) && isPlainRead(ie.e2, boundsChecked);
        case EXP.cast_:
            auto ce = e.isCastExp();
            return (basic(ce.type) && basic(ce.e1.type) || qualifierCast(ce)) && isPlainRead(ce.e1, boundsChecked);
        case EXP.negate, EXP.tilde, EXP.not:
            return basic(e.type) && isPlainRead(e.isUnaExp().e1, boundsChecked);
        case EXP.add, EXP.min, EXP.mul, EXP.and, EXP.or, EXP.xor,
             EXP.leftShift, EXP.rightShift, EXP.unsignedRightShift,
             EXP.lessThan, EXP.lessOrEqual, EXP.greaterThan, EXP.greaterOrEqual,
             EXP.equal, EXP.notEqual, EXP.identity, EXP.notIdentity:
            auto be = e.isBinExp();
            return basic(be.e1.type) && basic(be.e2.type) && isPlainRead(be.e1, boundsChecked) && isPlainRead(be.e2, boundsChecked);
        default:
            return false;
    }
}

/// Whether ce converts an array or pointer to one of the same elements qualified differently
private bool qualifierCast(CastExp ce)
{
    auto t = ce.type ? ce.type.toBasetype() : null;
    auto f = ce.e1.type ? ce.e1.type.toBasetype() : null;
    if (!t || !f || t.ty != f.ty || !(t.isTypeDArray() || t.isTypePointer()))
        return false;
    return t.nextOf().mutableOf().unSharedOf().equals(f.nextOf().mutableOf().unSharedOf());
}

/***********************************************************
 * Whether fd changes nothing but its own local variables, calling nothing and
 * allocating nothing, so a call of it may be moved before what it does not read
 */
private bool writesOnlyLocals(FuncDeclaration fd)
{
    import dmd.visitor : SemanticTimeTransitiveVisitor;
    extern (C++) final class Writes : SemanticTimeTransitiveVisitor
    {
        alias visit = SemanticTimeTransitiveVisitor.visit;
        FuncDeclaration fd;
        bool found;
        extern (D) this(FuncDeclaration fd) scope { this.fd = fd; }

        // a variable of fd's own or a part of one, held in fd's frame
        bool local(Expression e, bool bind)
        {
            if (auto ve = e.isVarExp())
            {
                auto vd = ve.var.isVarDeclaration();
                return vd && !vd.isDataseg() && vd.toParent2() == fd &&
                       !(vd.storage_class & (STC.out_ | STC.lazy_)) && (bind || !vd.isRef());
            }
            if (auto ie = e.isIndexExp())
                return ie.e1.type && ie.e1.type.toBasetype().isTypeSArray() && local(ie.e1, false);
            if (auto dve = e.isDotVarExp())
                return dve.e1.type && dve.e1.type.toBasetype().isTypeStruct() && local(dve.e1, false);
            return false;
        }

        override void visit(AssignExp e)
        {
            found |= !local(e.e1, e.op == EXP.construct || e.op == EXP.blit);
            super.visit(e);
        }
        override void visit(BinAssignExp e) { found |= !local(e.e1, false); super.visit(e); }
        override void visit(PreExp e) { found |= !local(e.e1, false); super.visit(e); }
        override void visit(PostExp e) { found |= !local(e.e1, false); super.visit(e); }
        override void visit(CallExp e) { found = true; }
        override void visit(NewExp e) { found = true; }
        override void visit(NewAnonClassExp e) { found = true; }
        override void visit(FuncExp e) { found = true; }
        override void visit(DelegateExp e) { found = true; }
        override void visit(ArrayLiteralExp e) { found = true; }
        override void visit(AssocArrayLiteralExp e) { found = true; }
        override void visit(DeleteExp e) { found = true; }
        override void visit(AsmStatement s) { found = true; }
        // what a template or a symbol used as an expression does is not looked into
        override void visit(TemplateDeclaration d) { found = true; }
        override void visit(ScopeExp e) { found = true; }
        override void visit(ThrowStatement s) { found = true; }
        override void visit(DeclarationExp e)
        {
            auto vd = e.declaration.isVarDeclaration();
            if (!vd || vd.isDataseg())
                found = true;
            else
                super.visit(e);
        }
    }
    if (!fd.fbody)
        return false;
    scope v = new Writes(fd);
    fd.fbody.accept(v);
    return !v.found;
}

/***********************************************************
 * Test that `fd` can be inlined.
 *
 * Params:
 *  hasThis = `true` if the caller can access the callee's this pointer.
 *  statementsToo = `true` if the function call is placed on ExpStatement.
 *      It means more code-block dependent statements in fd body - ForStatement,
 *      ThrowStatement, etc. can be inlined.
 *  eSink = where to report errors
 *
 * Returns:
 *  true if the function body can be expanded.
 */
private bool canInline(FuncDeclaration fd, bool hasThis, bool statementsToo, PASS pass, ErrorSink eSink)
{
    int cost;

    static if (CANINLINE_LOG)
    {
        printf("FuncDeclaration.canInline(hasThis = %d, statementsToo = %d, '%s')\n",
            hasThis, statementsToo, fd.toPrettyChars());
    }

    if (fd.needThis() && !hasThis)
        return false;

    if (fd.inlineNest)
    {
        static if (CANINLINE_LOG)
        {
            printf("\t1: no, inlineNest = %d, semanticRun = %d\n", fd.inlineNest, fd.semanticRun);
        }
        return false;
    }

    if (fd.semanticRun < PASS.semantic3)
    {
        if (!fd.fbody)
            return false;
        /* Only functions marked by pragma(inline, true) are inlined in this pass,
         * so the body of one that cannot be marked is not analyzed
         */
        if (pass != PASS.inlineAll && fd.inlining == PINLINE.default_ && !mayHavePragmaInline(fd.fbody))
            return false;
        if (!functionSemantic3(fd))
            return false;
        runDeferredSemantic3();
        if (global.errors)
            return false;
        assert(fd.semanticRun >= PASS.semantic3done);
    }

    if (fd.skipCodegen)
        return false;

    // Reset ILS if the decision was made in another pass
    if (fd.semanticRun != pass)
    {
        fd.inlineScanned = false;
        fd.inlineStatusExp = ILS.uninitialized;
        fd.inlineStatusStmt = ILS.uninitialized;
        fd.semanticRun = pass;
    }

    final switch (statementsToo ? fd.inlineStatusStmt : fd.inlineStatusExp)
    {
    case ILS.yes:
        static if (CANINLINE_LOG)
        {
            printf("\t1: yes %s\n", fd.toChars());
        }
        return true;
    case ILS.no:
        static if (CANINLINE_LOG)
        {
            printf("\t1: no %s\n", fd.toChars());
        }
        return false;
    case ILS.uninitialized:
        break;
    }

    final switch (fd.inlining)
    {
    case PINLINE.default_:
        if (pass != PASS.inlineAll)
            return false;
        break;
    case PINLINE.always:
        break;
    case PINLINE.never:
        return false;
    }

    if (fd.type)
    {
        TypeFunction tf = fd.type.isTypeFunction();

        // no variadic parameter lists
        if (tf.parameterList.varargs == VarArg.variadic ||
            tf.parameterList.varargs == VarArg.KRvariadic)
            goto Lno;

        /* No lazy parameters when inlining by statement, as the inliner tries to
         * operate on the created delegate itself rather than the return value.
         * Discussion: https://github.com/dlang/dmd/pull/6815
         */
        if (statementsToo && fd.parameters)
        {
            foreach (param; *fd.parameters)
            {
                if (param.storage_class & STC.lazy_)
                    goto Lno;
            }
        }

        // whether copying or destroying a t takes more than its bits
        static bool hasDtor(Type t)
        {
            auto ts = t.baseElemOf().isTypeStruct();
            return ts && !ts.sym.isPOD();
        }

        /* Don't inline a function that returns non-void, but has
         * no or multiple return expression.
         * When inlining as a statement:
         * 1. don't inline array operations, because the order the arguments
         *    get evaluated gets reversed. This is the same issue that e2ir.callfunc()
         *    has with them
         * 2. don't inline when the return value has a destructor, as it doesn't
         *    get handled properly
         */
        if (auto tfnext = tf.next)
        {
            /* for the isTypeSArray() case see https://github.com/dlang/dmd/pull/16145#issuecomment-1932776873
             */
            if (tfnext.ty != Tvoid && tfnext.ty != Tnoreturn &&
                (!fd.hasReturnExp ||
                 hasDtor(tfnext) && (statementsToo || tfnext.isTypeSArray())))
            {
                static if (CANINLINE_LOG)
                {
                    printf("\t3: no %s\n", fd.toChars());
                }
                goto Lno;
            }
        }

        /* https://issues.dlang.org/show_bug.cgi?id=14560
         * If fd returns void, all explicit `return;`s
         * must not appear in the expanded result.
         * See also ReturnStatement.doInlineAs!Statement().
         */
    }

    // cannot inline constructor calls because we need to convert:
    //      return;
    // to:
    //      return this;
    // ensure() has magic properties the inliner loses
    // require() has magic properties too
    // see bug 7699
    // no nested references to this frame
    if (!fd.fbody ||
        fd.ident == Id.ensure ||
        (fd.ident == Id.require &&
         fd.toParent().isFuncDeclaration() &&
         fd.toParent().isFuncDeclaration().needThis()) ||
         (fd.isSynchronized() ||
          fd.isImportedSymbol() ||
          fd.hasNestedFrameRefs() && !onlyClosureVars(fd) ||
          (fd.isVirtual() && !fd.isFinalFunc())))
    {
        static if (CANINLINE_LOG)
        {
            printf("\t4: no %s\n", fd.toChars());
        }
        goto Lno;
    }

    {
        scope v = new InlineScanVisitorDsymbol(pass, eSink);
        fd.accept(v);
        cost = inlineCostFunction(fd, hasThis, statementsToo);
        inlineCosts[cast(void*)fd] = cost;
    }
    // its variables are referred to only by nested functions whose calls are inlined
    if (fd.closureVars.length && refersToNested(fd))
        goto Lno;
    static if (CANINLINE_LOG)
    {
        printf("\tcost = %d for %s\n", cost, fd.toChars());
    }

    if (tooCostly(cost))
        goto Lno;
    if (!statementsToo && cost > COST_MAX)
        goto Lno;

    if (statementsToo)
        fd.inlineStatusStmt = ILS.yes;
    else
        fd.inlineStatusExp = ILS.yes;

    static if (CANINLINE_LOG)
    {
        printf("\t2: yes %s\n", fd.toChars());
    }
    return true;

Lno:
    if (fd.inlining == PINLINE.always && pass == PASS.inlinePragma &&
        global.errorSink.useWarnings == DiagnosticReporting.inform)
    {
        eSink.warning(fd.loc, "cannot inline function `%s`", fd.toPrettyChars());
    }

    if (statementsToo)
        fd.inlineStatusStmt = ILS.no;
    else
        fd.inlineStatusExp = ILS.no;

    static if (CANINLINE_LOG)
    {
        printf("\t2: no %s\n", fd.toChars());
    }
    return false;
}

/// The functions a call was inlined into, and the functions enclosing them
private __gshared bool[void*] inlinedInto;

/***********************************************************
 * Find, without analyzing it, whether the body of a function may have a
 * pragma(inline) statement, which can mark the function to be inlined.
 * Params:
 *      s = the body, or a statement in it, not yet analyzed
 * Returns:
 *      false if `s` has no pragma(inline) statement; true if it has one, or
 *      something not yet expanded, such as a mixin, could add one
 */
private bool mayHavePragmaInline(Statement s)
{
    if (!s)
        return false;
    final switch (s.stmt)
    {
        case STMT.Pragma:
            auto ps = s.isPragmaStatement();
            return ps.ident == Id.Pinline || mayHavePragmaInline(ps._body);

        case STMT.Compound:
        case STMT.CompoundDeclaration:
        case STMT.CompoundAsm:
            foreach (sx; (cast(CompoundStatement)s).statements[])
                if (mayHavePragmaInline(sx))
                    return true;
            return false;

        case STMT.UnrolledLoop:
            foreach (sx; s.isUnrolledLoopStatement().statements[])
                if (mayHavePragmaInline(sx))
                    return true;
            return false;

        case STMT.Peel:         return mayHavePragmaInline(s.isPeelStatement().s);
        case STMT.Scope:        return mayHavePragmaInline(s.isScopeStatement().statement);
        case STMT.Forwarding:   return mayHavePragmaInline(s.isForwardingStatement().statement);
        case STMT.While:        return mayHavePragmaInline(s.isWhileStatement()._body);
        case STMT.Do:           return mayHavePragmaInline(s.isDoStatement()._body);
        case STMT.For:
            auto fs = s.isForStatement();
            return mayHavePragmaInline(fs._init) || mayHavePragmaInline(fs._body);
        case STMT.Foreach:      return mayHavePragmaInline(s.isForeachStatement()._body);
        case STMT.ForeachRange: return mayHavePragmaInline(s.isForeachRangeStatement()._body);
        case STMT.If:
            auto ifs = s.isIfStatement();
            return mayHavePragmaInline(ifs.ifbody) || mayHavePragmaInline(ifs.elsebody);
        case STMT.Conditional:
            auto cs = s.isConditionalStatement();
            return mayHavePragmaInline(cs.ifbody) || mayHavePragmaInline(cs.elsebody);
        case STMT.Switch:       return mayHavePragmaInline(s.isSwitchStatement()._body);
        case STMT.Case:         return mayHavePragmaInline(s.isCaseStatement().statement);
        case STMT.CaseRange:    return mayHavePragmaInline(s.isCaseRangeStatement().statement);
        case STMT.Default:      return mayHavePragmaInline(s.isDefaultStatement().statement);
        case STMT.Synchronized: return mayHavePragmaInline(s.isSynchronizedStatement()._body);
        case STMT.With:         return mayHavePragmaInline(s.isWithStatement()._body);
        case STMT.TryCatch:
            auto tcs = s.isTryCatchStatement();
            if (mayHavePragmaInline(tcs._body))
                return true;
            if (tcs.catches)
                foreach (c; *tcs.catches)
                    if (mayHavePragmaInline(c.handler))
                        return true;
            return false;
        case STMT.TryFinally:
            auto tfs = s.isTryFinallyStatement();
            return mayHavePragmaInline(tfs._body) || mayHavePragmaInline(tfs.finalbody);
        case STMT.ScopeGuard:   return mayHavePragmaInline(s.isScopeGuardStatement().statement);
        case STMT.Debug:        return mayHavePragmaInline(s.isDebugStatement().statement);
        case STMT.Label:        return mayHavePragmaInline(s.isLabelStatement().statement);

        case STMT.Mixin:
        case STMT.StaticForeach:
            return true;

        case STMT.Error:
        case STMT.Exp:
        case STMT.DtorExp:
        case STMT.StaticAssert:
        case STMT.GotoDefault:
        case STMT.GotoCase:
        case STMT.SwitchError:
        case STMT.Return:
        case STMT.Break:
        case STMT.Continue:
        case STMT.Throw:
        case STMT.Goto:
        case STMT.Asm:
        case STMT.InlineAsm:
        case STMT.GccAsm:
        case STMT.Import:
            return false;
    }
}

/***********************************************************
 * Returns:
 *      whether a call was inlined into `fd` or a function nested in it
 */
public bool hasInlinedCalls(FuncDeclaration fd)
{
    return (cast(void*)fd in inlinedInto) !is null;
}

/***********************************************************
 * Expand a function call inline,
 *      ethis.fd(arguments)
 *
 * Params:
 *      e = original CallExp
 *      fd = function to expand
 *      parent = function that the call to fd is being expanded into
 *      eret = if !null then the lvalue of where the nrvo return value goes
 *      asStatements = expand to Statements rather than Expressions
 *      propagateNRVO = preserve NRVO status of variables
 *      eresult = if expanding to an expression, this is where the expression is written to
 *      sresult = if expanding to a statement, this is where the statement is written to
 *      again = if true, then fd can be inline scanned again because there may be
 *           more opportunities for inlining
 */
private void expandInline(CallExp ecall, FuncDeclaration fd, FuncDeclaration parent,
        Expression eret, Expression ethis, bool asStatements, bool propagateNRVO,
        out Expression eresult, out Statement sresult, out bool again)
{
    Loc callLoc = ecall.loc;
    auto tf = fd.type.isTypeFunction();
    static if (LOG || CANINLINE_LOG || EXPANDINLINE_LOG)
        printf("FuncDeclaration.expandInline('%s', %d)\n", fd.toChars(), asStatements);
    static if (EXPANDINLINE_LOG)
    {
        if (eret) printf("\teret = %s\n", eret.toChars());
        if (ethis) printf("\tethis = %s\n", ethis.toChars());
    }
    scope ids = new InlineDoState(parent, fd);
    ids.propagateNRVO = propagateNRVO;

    for (Dsymbol p = parent; p; p = p.toParent2())
        if (auto f = p.isFuncDeclaration())
            inlinedInto[cast(void*)f] = true;

    /* A function literal outside any function can still be called from other
     * modules (through an enum holding it), so the caller records it to be
     * emitted even though its call here is gone.
     */
    if (fd.isNested() || fd.isFuncLiteralDeclaration())
    {
        if (!parent.inlinedNestedCallees)
            parent.inlinedNestedCallees = new FuncDeclarations();
        parent.inlinedNestedCallees.push(fd);
    }

    // Set up eret
    if (eret)
    {
        if (eret.isVarExp())
        {
            ids.eret = eret;
            eret = null;
        }
        else
        {
            // Use a pointer to the expression (field or static array) to be initialized.

            auto ei = new ExpInitializer(callLoc, null);
            auto tmp = Identifier.generateId("__retptr");
            auto vd = new VarDeclaration(fd.loc, eret.type.pointerTo(), tmp, ei);
            vd.storage_class |= STC.temp;
            vd._linkage = LINK.d;
            vd.parent = parent;

            ei.exp = new ConstructExp(fd.loc, vd, new AddrExp(fd.loc, eret, vd.type));
            ei.exp.type = vd.type;

            auto de = new DeclarationExp(fd.loc, vd);
            de.type = Type.tvoid;

            ids.eret = new PtrExp(fd.loc, new VarExp(fd.loc, vd));
            ids.eret.type = eret.type;
            eret = de;
        }
    }

    // Set up vthis
    VarDeclaration vthis;
    if (ethis)
    {
        Expression e0;
        ethis = Expression.extractLast(ethis, e0);

        if (VarDeclaration vthis2 = ecall.vthis2)
        {
            // void*[2] __this = [ethis, this]
            if (ethis.type.ty == Tstruct)
            {
                // &ethis
                Type t = ethis.type.pointerTo();
                ethis = new AddrExp(ethis.loc, ethis);
                ethis.type = t;
            }
            auto elements = new Expressions(2);
            (*elements)[0] = ethis;
            (*elements)[1] = new NullExp(Loc.initial, Type.tvoidptr);
            Expression ae = new ArrayLiteralExp(vthis2.loc, vthis2.type, elements);
            Expression ce = new ConstructExp(vthis2.loc, vthis2, ae);
            ce.type = vthis2.type;
            vthis2._init = new ExpInitializer(vthis2.loc, ce);
            vthis = vthis2;
        }
        else if (auto ve = ethis.isVarExp())
        {
            vthis = ve.var.isVarDeclaration();
        }
        else
        {
            if (ethis.type.ty == Tpointer)
            {
                Type t = ethis.type.nextOf();
                ethis = new PtrExp(ethis.loc, ethis);
                ethis.type = t;
            }

            auto ei = new ExpInitializer(fd.loc, null);
            vthis = new VarDeclaration(fd.loc, ethis.type, Id.This, ei);
            vthis._linkage = LINK.d;
            vthis.parent = parent;

            if (ethis.isStructLiteralExp())
            {
                vthis.storage_class = STC.rvalue;

                if (fd.isCtorDeclaration() && propagateNRVO)
                    vthis.nrvo = true;
            }
            else if (ethis.type.ty != Tclass)
            {
                vthis.storage_class = STC.ref_;
            }

            ei.exp = new ConstructExp(fd.loc, vthis, ethis);
            ei.exp.type = vthis.type;

            auto de = new DeclarationExp(fd.loc, vthis);
            de.type = Type.tvoid;
            e0 = Expression.combine(e0, de);
        }
        ethis = e0;

        ids.vthis = vthis;
    }

    // Set up parameters
    Expression eparams;
    if (ecall.arguments && ecall.arguments.length)
    {
        assert(fd.parameters.length == ecall.arguments.length);
        foreach (i; 0 .. ecall.arguments.length)
        {
            auto vfrom = (*fd.parameters)[i];
            auto arg = (*ecall.arguments)[i];

            auto ei = new ExpInitializer(vfrom.loc, arg);
            auto vto = new VarDeclaration(vfrom.loc, vfrom.type, vfrom.ident, ei);
            vto.storage_class |= vfrom.storage_class & (STC.temp | STC.IOR | STC.lazy_ | STC.nodtor);
            vto._linkage = vfrom._linkage;
            vto.parent = parent;
            //printf("vto = '%s', vto.storage_class = x%x\n", vto.toChars(), vto.storage_class);
            //printf("vto.parent = '%s'\n", parent.toChars());

            if (VarExp ve = arg.isVarExp())
            {
                VarDeclaration va = ve.var.isVarDeclaration();
                if (va && va.isArgDtorVar)
                {
                    assert(vto.storage_class & STC.nodtor);
                    // The destructor is called on va so take it by ref
                    vto.storage_class |= STC.ref_;
                }
            }

            if (arg.rvalue)
                vto.storage_class |= STC.ref_;

            // Even if vto is STC.lazy_, `vto = arg` is handled correctly in glue layer.
            ei.exp = new BlitExp(vto.loc, vto, arg);
            ei.exp.type = vto.type;

            ids.from.push(vfrom);
            ids.to.push(vto);

            auto de = new DeclarationExp(Loc.initial, vto);
            de.type = Type.tvoid;
            eparams = Expression.combine(eparams, de);

            /* If function pointer or delegate parameters are present,
             * inline scan again because if they are initialized to a symbol,
             * any calls to the fp or dg can be inlined.
             */
            if (vfrom.type.ty == Tdelegate ||
                vfrom.type.isPtrToFunction())
            {
                // the copy keeps its initializer if the function only calls the parameter
                if (onlyCalled(vfrom, fd))
                    unchangedCopies[cast(void*) vto] = true;
                if (auto ve = arg.isVarExp())
                {
                    if (ve.var.isFuncDeclaration())
                        again = true;
                }
                else if (auto se = arg.isSymOffExp())
                {
                    if (se.var.isFuncDeclaration())
                        again = true;
                }
                else if (arg.op == EXP.function_ || arg.op == EXP.delegate_)
                    again = true;
            }
        }
    }

    if (asStatements)
    {
        /* Construct:
         *  { eret; ethis; eparams; fd.fbody; }
         * or:
         *  { eret; ethis; try { eparams; fd.fbody; } finally { vthis.edtor; } }
         */

        auto as = Statements();
        auto asDtor = Statements();
        if (eret)
            as.push(new ExpStatement(callLoc, eret));
        if (ethis)
            as.push(new ExpStatement(callLoc, ethis));

        auto as2 = &as;
        if (vthis && !vthis.isDataseg())
        {
            if (vthis.needsScopeDtor())
            {
                // same with ExpStatement.scopeCode()
                as2 = &asDtor;
                vthis.storage_class |= STC.nodtor;
            }
        }

        if (eparams)
            as2.push(new ExpStatement(callLoc, eparams));

        if (returnsBeforeEnd(fd))
            ids.retLabel = returnLabel(callLoc, parent);
        fd.inlineNest++;
        Statement s = doInlineAs!Statement(fd.fbody, ids);
        fd.inlineNest--;
        as2.push(s);
        if (ids.retLabel)
            as2.push(ids.retLabel.statement);

        if (as2 != &as)
        {
            as.push(new TryFinallyStatement(callLoc,
                        new CompoundStatement(callLoc, as2.move()),
                        new DtorExpStatement(callLoc, vthis.edtor, vthis)));
        }

        sresult = new ScopeStatement(callLoc, new CompoundStatement(callLoc, as.move()), callLoc);

        static if (EXPANDINLINE_LOG)
            printf("\n[%s] %s expandInline sresult =\n%s\n",
                callLoc.toChars(), fd.toPrettyChars(), toChars(sresult));
    }
    else
    {
        /* Construct:
         *  (eret, ethis, eparams, fd.fbody)
         */

        fd.inlineNest++;
        auto e = doInlineAs!Expression(fd.fbody, ids);
        fd.inlineNest--;

        import dmd.expressionsem : toLvalue;
        // https://issues.dlang.org/show_bug.cgi?id=11322
        if (tf.isRef)
            e = e.toLvalue(null, "`ref` return");

        // https://issues.dlang.org/show_bug.cgi?id=15210
        if (tf.next.ty == Tvoid && e && e.type.ty != Tvoid && e.type.ty != Tnoreturn)
        {
            e = new CastExp(callLoc, e, Type.tvoid);
            e.type = Type.tvoid;
        }

        eresult = combineInlineSequence(eresult, eret);
        eresult = combineInlineSequence(eresult, ethis);
        eresult = combineInlineSequence(eresult, eparams);
        eresult = combineInlineSequence(eresult, e);

        if (ecall.rvalue || tf.isRvalue)
            eresult.rvalue = true;

        static if (EXPANDINLINE_LOG)
            printf("\n[%s] %s expandInline eresult = %s\n",
                callLoc.toChars(), fd.toPrettyChars(), eresult.toChars());
    }

    // Need to reevaluate whether parent can now be inlined
    // in expressions, as we might have inlined statements
    parent.inlineStatusExp = ILS.uninitialized;
}

/***********************************************************
 * Determine if v is 'head const', meaning
 * that once it is initialized it is not changed
 * again.
 *
 * This is done using a primitive flow analysis.
 *
 * v is head const if v is const or immutable.
 * Otherwise, v is assumed to be head const unless one of the
 * following is true:
 *      1. v is a `ref` or `out` variable
 *      2. v is a parameter and fd is a variadic function
 *      3. v is assigned to again
 *      4. the address of v is taken
 *      5. v is referred to by a function nested within fd
 *      6. v is ever assigned to a `ref` or `out` variable
 *      7. v is ever passed to another function as `ref` or `out`
 *
 * Params:
 *      v       variable to check
 *      fd      function that v is local to
 * Returns:
 *      true if v's initializer is the only value assigned to v
 */
private bool onlyOneAssign(VarDeclaration v, FuncDeclaration fd) @trusted
{
    if (!v.type.isMutable())
        return true;            // currently the only case handled atm
    return (cast(void*) v in unchangedCopies) !is null;
}

/// Whether the code generator keeps enough variables in registers for the functions
/// inlined into a caller of any size, and for more of them into loops
private bool registersToSpare()
{
    import dmd.backend.arm.lir : newCodegenEnabled;
    import dmd.target : target;
    return target.isAArch64 && newCodegenEnabled();
}

/// Whether call `e` is given a function literal as an argument
private bool givenLiteral(CallExp e)
{
    if (e && e.arguments)
        foreach (arg; *e.arguments)
            if (arg && (arg.isFuncExp() ||
                        arg.isDelegateExp() && arg.isDelegateExp().func.isFuncLiteralDeclaration()))
                return true;
    return false;
}

/// The copies of parameters made by inlining that are never changed
private __gshared bool[void*] unchangedCopies;      // by identity, as frontend classes are extern(C++)

/**
 * Whether parameter v of fd is only ever called, so it holds its argument throughout
 */
private bool onlyCalled(VarDeclaration v, FuncDeclaration fd)
{
    import dmd.visitor.foreachvar : foreachExpAndVar;
    import dmd.visitor.postorder : walkPostorder;
    if (!fd.fbody || v.storage_class & (STC.ref_ | STC.out_ | STC.lazy_))
        return false;
    extern (C++) final class Uses : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        VarDeclaration v;
        int called, all;
        extern (D) this(VarDeclaration v) scope { this.v = v; }
        override void visit(Expression e) {}
        override void visit(VarExp e) { if (e.var == v) ++all; }
        override void visit(SymOffExp e) { if (e.var == v) all += 2; }     // the address taken
        override void visit(CallExp e)
        {
            if (auto ve = e.e1.isVarExp())
                if (ve.var == v)
                    ++called;
        }
    }
    scope Uses u = new Uses(v);
    bool complex;
    foreachExpAndVar(fd.fbody, (Expression e) { walkPostorder(e, u); },
        (VarDeclaration d) {
            if (d._init)
                if (auto ie = d._init.isExpInitializer())
                    walkPostorder(ie.exp, u);
        });
    return u.all == u.called;
}

/************************************************************
 * See if arguments to a function are creating temporaries that
 * will need destruction after the function is executed.
 * Params:
 *      arguments = arguments to function
 * Returns:
 *      true if temporaries need destruction
 */

private bool argumentsNeedDtors(Expressions* arguments)
{
    if (arguments)
    {
        foreach (arg; *arguments)
        {
            if (expNeedsDtor(arg))
                return true;
        }
    }
    return false;
}

/************************************************************
 * See if expression is creating temporaries that
 * will need destruction at the end of the scope.
 * Params:
 *      exp = expression
 * Returns:
 *      true if temporaries need destruction
 */

private bool expNeedsDtor(Expression exp)
{
    extern (C++) final class NeedsDtor : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        Expression exp;

    public:
        extern (D) this(Expression exp) scope @safe
        {
            this.exp = exp;
        }

        override void visit(Expression)
        {
        }

        override void visit(DeclarationExp de)
        {
            Dsymbol_needsDtor(de.declaration);
        }

        void Dsymbol_needsDtor(Dsymbol s)
        {
            /* This mirrors logic of Dsymbol_toElem() in e2ir.d
             * perhaps they can be combined.
             */

            void symbolDg(Dsymbol s)
            {
                Dsymbol_needsDtor(s);
            }

            if (auto vd = s.isVarDeclaration())
            {
                s = s.toAlias();
                if (s != vd)
                    return Dsymbol_needsDtor(s);
                if (vd.isStatic() || vd.storage_class & (STC.extern_ | STC.gshared | STC.manifest))
                    return;
                if (vd.needsScopeDtor())
                {
                    stop = true;
                }
            }
            else if (auto tm = s.isTemplateMixin())
            {
                tm.members.foreachDsymbol(&symbolDg);
            }
            else if (auto ad = s.isAttribDeclaration())
            {
                ad.include(null).foreachDsymbol(&symbolDg);
            }
            else if (auto td = s.isTupleDeclaration())
            {
                td.foreachVar(&symbolDg);
            }


        }
    }

    scope NeedsDtor ct = new NeedsDtor(exp);
    return walkPostorder(exp, ct);
}
