/**
 * Generate the object file for function declarations and critical sections.
 *
 * generateCodeAndWrite() is the only function seen by the front end.
 *
 * Copyright:   Copyright (C) 1999-2026 by The D Language Foundation, All Rights Reserved
 * Authors:     $(LINK2 https://www.digitalmars.com, Walter Bright)
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Source:      $(LINK2 https://github.com/dlang/dmd/blob/master/compiler/src/dmd/glue/glue.d, _glue.d)
 * Documentation: $(LINK https://dlang.org/phobos/dmd_glue_package.html)
 * Coverage:    $(LINK https://codecov.io/gh/dlang/dmd/src/master/compiler/src/dmd/glue/package.d)
 */

module dmd.glue;

import core.stdc.stdio;
import core.stdc.string;
import core.stdc.stdlib;

import dmd.root.array;
import dmd.root.file;
import dmd.root.filename;
import dmd.common.outbuffer;
import dmd.root.rmem;
import dmd.root.string;

// `ObjcGlue_initialize` and `generateCodeAndWrite` (declared below)
// are the only public functions of this package
public import dmd.glue.objc;

import dmd.glue.e2ir;
import dmd.glue.tocsym;
import dmd.glue.toctype;
import dmd.glue.toir;
import dmd.glue.toobj;

import dmd.backend.cdef;
import dmd.backend.cc;
import dmd.backend.code;
import dmd.backend.dt;
import dmd.backend.el;
import dmd.backend.blockopt;
import dmd.backend.cg : localgot;
import dmd.backend.dout : dataSymbolsWritten, out_readonly, out_reset, outdata, writefunc;
import dmd.backend.x86.cg87 : cg87_reset;
import dmd.backend.obj;
import dmd.backend.oper;
import dmd.backend.rtlsym;
import dmd.backend.symbol;
import dmd.backend.ty;
import dmd.backend.type;
import dmd.glue.s2ir;
import dmd.aggregate;
import dmd.arraytypes;
import dmd.astenums;
import dmd.blockexit;
import dmd.dclass;
import dmd.declaration;
import dmd.dmdparams;
import dmd.dmodule;
import dmd.dstruct;
import dmd.dsymbol;
import dmd.dsymbolsem : getLocalClasses, getType, findGetMembers;
import dmd.expressionsem : toInteger;
import dmd.dtemplate;
import dmd.errors : fatal;
import dmd.errorsink;
import dmd.expression;
import dmd.func;
import dmd.funcsem : onlyOneMain, isVirtual;
import dmd.globals;
import dmd.hdrgen : toErrMsg;
import dmd.identifier;
import dmd.id;
import dmd.lib;
import dmd.location;
import dmd.mtype;
import dmd.statement;
import dmd.target;
import dmd.tokens;
import dmd.typesem;
import dmd.funcsem : genCfunc;
import dmd.utils;

/**
 * Generate code for `modules` and write objects/libraries
 *
 * Params:
 *  modules = array of `Module`s to generate code for
 *  libmodules = array of objects/libraries already generated (passed on command line)
 *  libname = {.lib,.a} file output name
 *  objdir = directory to write object files to
 *  writeLibrary = write library file instead of object file(s)
 *  obj = generate object files
 *  oneobj = write one object file instead of multiple ones
 *  multiobj = break one object file into multiple ones
 *  verbose = print progress message when generatig code
 */
public void generateCodeAndWrite(Module[] modules, const(char)*[] libmodules,
                          const(char)[] libname, const(char)[] objdir,
                          bool writeLibrary, bool obj, bool oneobj, bool multiobj,
                          bool verbose)
{
    auto eSink = global.errorSink;

    Library library = null;
    if (writeLibrary)
    {
        library = Library.factory(target.objectFormat(), target.lib_ext, eSink);

        const arg = libraryFileName(libname, objdir);
        library.setFilename(outputPartSuffix.length ? arg ~ outputPartSuffix : arg);

        // Add input object and input library files to output library
        foreach (p; libmodules)
            library.addObject(p.toDString(), null);
    }

    /* In a worker of a split compilation, the functions it has put off generating are
     * settled with the other workers once its modules' code is generated: with
     * multiobj, after their deferred functions are written, and otherwise with its last
     * module
     */
    if (outputPartSuffix.length && !multiobj)
    {
        foreach (m; modules)
            if (m.filetype != FileType.dhdr)
                settleWith = m;
    }

    if (!obj)
    {
    }
    else if (oneobj)
    {
        OutBuffer objbuf;
        Module firstm;    // first module we generate code for
        foreach (m; modules)
        {
            if (m.filetype == FileType.dhdr)
                continue;
            if (!firstm)
            {
                firstm = m;
                obj_start(objbuf, m.srcfile.toChars());
            }
            if (verbose)
                eSink.message(Loc.initial, "code      %s", m.toChars());
            genObjFile(m, false, false);
        }
        if (!global.errors && firstm)
        {
            const objname = firstm.objfile.toString();
            obj_end(objbuf, library, !library && outputPartSuffix.length ? objname ~ outputPartSuffix : objname);
        }
    }
    else
    {
        OutBuffer objbuf;
        foreach (m; modules)
        {
            if (m.filetype == FileType.dhdr)
                continue;
            if (verbose)
                eSink.message(Loc.initial, "code      %s", m.toChars());
            obj_start(objbuf, m.srcfile.toChars());
            genObjFile(m, multiobj, false);
            obj_end(objbuf, library, m.objfile.toString());
            obj_write_deferred(objbuf, library, glue.obj_symbols_towrite);
            if (global.errors && !writeLibrary)
                m.deleteObjFile();
        }
        if (multiobj && outputPartSuffix.length)
        {
            import dmd.parallel : settleRound;
            generatePlannedInstances(multiobj);
            obj_write_deferred(objbuf, library, glue.obj_symbols_towrite);
            Dsymbol[] generate;
            while (settleRound(functionsGenerated, generate))
            {
                foreach (sym; generate)
                    toObjFile(sym, multiobj);
                obj_write_deferred(objbuf, library, glue.obj_symbols_towrite);
            }
        }
    }
    if (writeLibrary && !global.errors)
    {
        if (verbose)
            eSink.message(Loc.initial, "library   %.*s", library.filename.fTuple.expand);

        if (!ensurePathToNameExists(Loc.initial, library.filename))
            fatal();

        /* Write library to temporary file. If that is successful,
         * then and only then replace the existing file with the temporary file
         */
        auto tmpname = library.filename ~ ".tmp\0";

        auto libbuf = OutBuffer(tmpname.ptr);
        library.writeLibToBuffer(libbuf);

        if (!libbuf.moveToFile(library.filename))
        {
            eSink.error(Loc.initial, "error writing file '%.*s'", library.filename.fTuple.expand);
            destroy(tmpname);
            fatal();
        }
        destroy(tmpname);
    }
}

/// Suffix added to the name of the object file or library written by
/// generateCodeAndWrite(), when the compilation is split across workers
public __gshared const(char)[] outputPartSuffix;

/// In a worker of a split compilation without multiobj: its last module, whose code
/// generation ends with settling with the other workers who generates the functions
/// any of them could
private __gshared Module settleWith;

/**************************************
 * Combine the library parts written by split workers into one library.
 * Params:
 *      libfile = the library to write
 *      libmodules = object and library files given on the command line to add to it
 *      parts = the library parts
 * Returns:
 *      true on success
 */
public bool mergeLibraries(const(char)[] libfile, const(char)*[] libmodules, const(char)[][] parts)
{
    auto library = Library.factory(target.objectFormat(), target.lib_ext, global.errorSink);
    library.setFilename(libfile);
    foreach (p; libmodules)
        library.addObject(p.toDString(), null);
    foreach (p; parts)
        library.addObject(p, null);
    if (global.errors)
        return false;
    import dmd.parallel : mergeTemporary;
    auto tmpname = mergeTemporary(libfile) ~ "\0";
    auto libbuf = OutBuffer(tmpname.ptr);
    library.writeLibToBuffer(libbuf);
    return libbuf.moveToFile(libfile);
}

/**
 * Get the name of the library to write, by combining objdir, libname,
 * the first object file name, and the library extension.
 */
public const(char)[] libraryFileName(const(char)[] libname, const(char)[] objdir)
{
    const(char)[] arg;
    if (!libname.length)
    {
        // get name of the first object file
        const(char)[] n = global.params.objfiles[0].toDString;
        n = FileName.name(n);                // remove its path
        arg = FileName.forceExt(n, target.lib_ext); // force library name extension
    }
    else
        arg = FileName.defaultExt(libname, target.lib_ext);
    if (!FileName.absolute(arg))
        arg = FileName.combine(objdir, arg);
    return arg;
}

/**
 * Get the name of the one object file written for `modules`.
 */
public const(char)[] oneObjectFileName(Module[] modules)
{
    foreach (m; modules)
        if (m.filetype != FileType.dhdr)
            return m.objfile.toString();
    return null;
}

// FIXME: does not work on old bootstrap compilers
//package(dmd.glue):


alias toSymbol = dmd.glue.tocsym.toSymbol;

//extern
__gshared Symbol* bzeroSymbol;        /// common location for immutable zeros

/*******************************************
 * Generate readonly symbol that consists of a bunch of zeros.
 * Immutable Symbol instances can be mapped over it.
 * Only one is generated per object file.
 * Returns:
 *    bzero symbol
 */
Symbol* getBzeroSymbol()
{
    Symbol* s = bzeroSymbol;
    if (s)
        return s;

    s = symbol_calloc("__bzeroBytes");
    s.Stype = type_static_array(128, type_fake(TYuchar));
    s.Stype.Tmangle = Mangle.c;
    s.Stype.Tcount++;
    s.Sclass = SC.global;
    s.Sfl = FL.data;
    s.Sflags |= SFLnodebug;
    s.Salignment = 16;

    auto dtb = DtBuilder(0);
    dtb.nzeros(128);
    s.Sdt = dtb.finish();
    dt2common(&s.Sdt);

    outdata(s);

    bzeroSymbol = s;
    return s;
}

/*****************************
 * Return back end type corresponding to D front end type.
 */
tym_t totym(Type tx)
{
    // OSX AArch64 long doubles are 64 bits
    bool RealIsDouble = target.os == Target.os.OSX && target.isAArch64;

    tym_t t;
    switch (tx.ty)
    {
        case Tvoid:     t = TYvoid;     break;
        case Tint8:     t = TYschar;    break;
        case Tuns8:     t = TYuchar;    break;
        case Tint16:    t = TYshort;    break;
        case Tuns16:    t = TYushort;   break;
        case Tint32:    t = TYint;      break;
        case Tuns32:    t = TYuint;     break;
        case Tint64:    t = TYllong;    break;
        case Tuns64:    t = TYullong;   break;
        case Tfloat32:  t = TYfloat;    break;
        case Tfloat64:  t = TYdouble;   break;
        case Tfloat80:  t = RealIsDouble ? TYdouble : TYreal;  break;
        case Timaginary32: t = TYifloat; break;
        case Timaginary64: t = TYidouble; break;
        case Timaginary80: t = RealIsDouble ? TYidouble : TYireal; break;
        case Tcomplex32: t = TYcfloat;  break;
        case Tcomplex64: t = TYcdouble; break;
        case Tcomplex80: t = RealIsDouble ? TYcdouble : TYcreal; break;
        case Tbool:     t = TYbool;     break;
        case Tchar:     t = TYchar;     break;
        case Twchar:    t = TYwchar_t;  break;
        case Tdchar:
            t = (driverParams.symdebug == 1 || target.os & Target.OS.Posix) ? TYdchar : TYulong;
            break;

        case Taarray:   t = TYaarray;   break;
        case Tclass:
        case Treference:
        case Tpointer:  t = TYnptr;     break;
        case Tdelegate: t = TYdelegate; break;
        case Tarray:    t = TYdarray;   break;
        case Tsarray:   t = TYstruct;   break;
        case Tnoreturn: t = TYnoreturn; break;

        case Tstruct:
            t = TYstruct;
            break;

        case Tenum:
        {
            Type tb = tx.toBasetype();
            const id = tx.toDsymbol(null).ident;
            if (id == Id.__c_long)
                t = tb.ty == Tint32 ? TYlong : TYllong;
            else if (id == Id.__c_ulong)
                t = tb.ty == Tuns32 ? TYulong : TYullong;
            else if (id == Id.__c_long_double)
                t = tb.size() == 8 ? TYdouble : TYreal;
            else if (id == Id.__c_complex_float)
                t = TYcfloat;
            else if (id == Id.__c_complex_double)
                t = TYcdouble;
            else if (id == Id.__c_complex_real)
                t = tb.size() == 16 ? TYcdouble : TYcreal;
            else
                t = totym(tb);
            break;
        }

        case Tident:
        case Ttypeof:
        case Tmixin:
            //printf("ty = %d, '%s'\n", tx.ty, tx.toChars());
            auto eSink = global.errorSink;
            eSink.error(Loc.initial, "forward reference of `%s`", tx.toErrMsg());
            t = TYint;
            break;

        case Tnull:
            t = TYnptr;
            break;

        case Tvector:
        {
            auto tv = cast(TypeVector)tx;
            const tb = tv.elementType();
            const s32 = tv.alignsize() == 32;   // if 32 byte, 256 bit vector
            switch (tb.ty)
            {
                case Tvoid:
                case Tint8:     t = s32 ? TYschar32  : TYschar16;  break;
                case Tuns8:     t = s32 ? TYuchar32  : TYuchar16;  break;
                case Tint16:    t = s32 ? TYshort16  : TYshort8;   break;
                case Tuns16:    t = s32 ? TYushort16 : TYushort8;  break;
                case Tint32:    t = s32 ? TYlong8    : TYlong4;    break;
                case Tuns32:    t = s32 ? TYulong8   : TYulong4;   break;
                case Tint64:    t = s32 ? TYllong4   : TYllong2;   break;
                case Tuns64:    t = s32 ? TYullong4  : TYullong2;  break;
                case Tfloat32:  t = s32 ? TYfloat8   : TYfloat4;   break;
                case Tfloat64:  t = s32 ? TYdouble4  : TYdouble2;  break;
                default:
                    assert(0);
            }
            break;
        }

        case Tfunction:
        {
            auto tf = cast(TypeFunction)tx;
            final switch (tf.linkage)
            {
                case LINK.windows:
                    if (target.isX86_64)
                        goto case LINK.c;
                    t = (tf.parameterList.varargs == VarArg.variadic ||
                         tf.parameterList.varargs == VarArg.KRvariadic) ? TYnfunc : TYnsfunc;
                    break;

                case LINK.c:
                case LINK.cpp:
                case LINK.objc:
                    t = TYnfunc;
                    if (target.os == Target.OS.Windows)
                    {
                    }
                    else if (target.isX86 && retStyle(tf, false) == RET.stack)
                        t = TYhfunc;
                    break;

                case LINK.d:
                    t = (tf.parameterList.varargs == VarArg.variadic) ? TYnfunc : TYjfunc;
                    break;

                case LINK.default_:
                case LINK.system:
                    printf("linkage = %d\n", tf.linkage);
                    assert(0);
            }
            if (tf.isNothrow)
                t |= mTYnothrow;
            return t;
        }
        default:
            //printf("ty = %d, '%s'\n", tx.ty, tx.toChars());
            assert(0);
    }

    t |= modToTym(tx.mod);    // Add modifiers

    return t;
}

/**************************************
 * Append s to list of object files to generate later.
 * Only happens with multiobj.
 */
void obj_append(Dsymbol s)
{
    //printf("deferred: %s\n", s.toChars());
    glue.obj_symbols_towrite.push(s);
}

extern (D) bool obj_includelib(scope const char[] name) nothrow
{
    return objmod.includelib(name);
}

void obj_startaddress(Symbol* s)
{
    return objmod.startaddress(s);
}

bool obj_linkerdirective(scope const(char)* directive)
{
    return objmod.linkerdirective(directive);
}

/* Counts of the functions whose code is generated, and of the template instance
 * functions whose code is left to other workers of a split compilation
 */
private __gshared size_t functionsGenerated;
private __gshared size_t functionsLeftToOtherWorkers;

/// Returns: true if `fd`, or a function it is nested in, belongs to a non-root module
private bool inNonRootFunction(FuncDeclaration fd)
{
    for (FuncDeclaration fd2 = fd; fd2; )
    {
        if (fd2.inNonRoot())
            return true;
        if (fd2.isNested())
            fd2 = fd2.toParent2().isFuncDeclaration();
        else
            break;
    }
    return false;
}

/* Returns: the outermost function enclosing `fd` at run time, through the functions
 * and aggregates it is nested in, or `fd` if there is none. A function reaches the
 * frames enclosing it at the offsets the code generation of their functions assigns,
 * so in a split compilation the worker generating the outermost function generates
 * all the functions it encloses.
 */
private FuncDeclaration frameRoot(FuncDeclaration fd)
{
    FuncDeclaration root = fd;
    for (Dsymbol p = fd.toParent2(); p; p = p.toParent2())
    {
        if (auto f = p.isFuncDeclaration())
            root = f;
        else if (!p.isAggregateDeclaration())
            break;
    }
    return root;
}

/// Returns: true if generating `fd` adds it to what the module being generated runs
/// at startup, at exit or as a unit test
private bool registersWithModule(FuncDeclaration fd)
{
    return fd.isStaticCtorDeclaration() || fd.isStaticDtorDeclaration() ||
        fd.isUnitTestDeclaration() && global.params.useUnitTests || fd.isCrtCtor || fd.isCrtDtor;
}

/// Returns: true if a member of template instance `ti` adds itself to what the module
/// generating it runs at startup, at exit or as a unit test
private bool instanceRegisters(TemplateInstance ti)
{
    import dmd.dsymbolsem : include;

    static bool scan(Dsymbols* members)
    {
        if (!members)
            return false;
        foreach (s; *members)
        {
            if (auto fd = s.isFuncDeclaration())
            {
                if (registersWithModule(fd))
                    return true;
            }
            else if (s.isAttribDeclaration())
            {
                if (scan(include(s, null)))
                    return true;
            }
            else if (auto sds = s.isScopeDsymbol())
            {
                if (!s.isTemplateInstance() && !s.isTemplateDeclaration() && scan(sds.members))
                    return true;
            }
        }
        return false;
    }
    return scan(ti.members);
}

/* How a function or template instance is generated in a worker of a split
 * compilation: what is generated as a whole with it, a group, and whether the group
 * is generated by a given worker regardless of which needs it, or is settled with
 * the other workers (see `dmd.parallel.settleRound`)
 */
private struct SplitGroup
{
    int pinned = -1;        // the worker generating the group, -1 if it is settled
    Dsymbol head;           // what is generated first of the group
    const(char)[] name;     // the name of the group
}

/* Returns: the group of function `fd`. A function is generated with the functions
 * enclosing it (see `frameRoot`). A template instance function is generated with its
 * template instance. Any other function is generated with the module of its
 * outermost enclosing function, if that is a root module, unless it is a function
 * literal outside any function, which is generated where it is needed.
 */
private SplitGroup functionGroup(FuncDeclaration fd)
{
    import dmd.parallel : moduleWorker;
    import dmd.mangle : mangleExact;

    auto root = frameRoot(fd);
    if (auto ti = root.isInstantiated())
        return instanceGroup(ti);
    SplitGroup g;
    g.head = root;
    g.name = mangleExact(root).toDString();
    if (!root.isFuncLiteralDeclaration())
        g.pinned = moduleWorker(root.getModule());
    return g;
}

/* Returns: the group of template instance `ti`. An instance nested in a function, or
 * of a template declared in one, is generated with the group of that function.
 * Another instance is generated by the worker the plan of the split assigns it to
 * (see `planSplit`). One first needed during code generation is settled with the other
 * workers; without multiobj, if it has a static constructor, static destructor or unit
 * test, it is generated by the worker generating the module it is a member of, which
 * runs them, and if that is not this worker the split is given up, as only an unsplit
 * compilation runs them where it would.
 */
private SplitGroup instanceGroup(TemplateInstance ti)
{
    import dmd.parallel : abandonSplit, instanceWorker, moduleWorker, thisWorker;

    if (auto f = enclosingFunction(ti))
        return functionGroup(f);
    SplitGroup g;
    g.head = ti;
    g.name = instanceName(ti);
    g.pinned = instanceWorker(ti);
    if (g.pinned < 0 && !global.params.multiobj && instanceRegisters(ti))
    {
        g.pinned = ti.memberOf ? moduleWorker(ti.memberOf) : -1;
        if (g.pinned != thisWorker())
            abandonSplit("runs with a module another worker generates", g.name);
    }
    return g;
}

/// Returns: the function template instance `ti` is nested in, or the function its
/// template is declared in, if any
private FuncDeclaration enclosingFunction(TemplateInstance ti)
{
    for (Dsymbol p = ti.enclosing ? ti.enclosing : ti.parent; p; p = p.toParent2())
    {
        if (auto f = p.isFuncDeclaration())
            return f;
    }
    return null;
}

/// Returns: how much code generating the functions among `members` is, in lines
private size_t codeSize(Dsymbols* members)
{
    import dmd.dsymbolsem : include;

    size_t size = 0;
    if (!members)
        return 0;
    foreach (s; *members)
    {
        if (auto fd = s.isFuncDeclaration())
        {
            if (fd.fbody)
                size += fd.endloc.linnum >= fd.loc.linnum ? fd.endloc.linnum - fd.loc.linnum + 1 : 1;
        }
        else if (s.isAttribDeclaration())
            size += codeSize(include(s, null));
        else if (auto sds = s.isScopeDsymbol())
        {
            if (!s.isTemplateInstance() && !s.isTemplateDeclaration())
                size += codeSize(sds.members);
        }
    }
    return size;
}

/**************************************
 * Plan which worker of a split compilation generates what: each root module is
 * generated by one worker, as is each template instance needing code generated, with
 * the functions it encloses. An instance whose static constructors the module it is a
 * member of runs, or nested in a function of a root module, is generated with that
 * module. The modules are dealt out first, then the instances, the largest first, each
 * to the worker with the least code so far, measured in lines of functions: the plan
 * is a function of the sources and the number of workers only.
 * Params:
 *      modules = the root modules
 *      n = the number of workers
 * Returns:
 *      the worker of each module; the worker of each instance is recorded with
 *      `dmd.parallel.setInstanceWorker`
 */
uint[] planSplit(Module[] modules, uint n)
{
    import dmd.parallel : setInstanceWorker;
    import dmd.templatesem : needsCodegen;

    static struct Unit { size_t cost; size_t order; TemplateInstance ti; size_t moduleIndex; }

    size_t[void*] moduleIndex;
    foreach (j, m; modules)
        moduleIndex[cast(void*)m] = j;

    /* The unit an instance is generated with: a module (by its index + 1), another
     * instance, or none (0, null) when it is settled during code generation
     */
    static struct Owner { size_t moduleIndex; TemplateInstance ti; }
    Owner unitOf(TemplateInstance ti)
    {
        if (auto f = enclosingFunction(ti))
        {
            auto root = frameRoot(f);
            if (auto outer = root.isInstantiated())
                return unitOf(outer);
            if (root.isFuncLiteralDeclaration())
                return Owner.init;
            if (auto p = cast(void*)root.getModule() in moduleIndex)
                return Owner(*p + 1, null);
            return Owner.init;
        }
        if (!global.params.multiobj && instanceRegisters(ti) && ti.memberOf)
        {
            if (auto p = cast(void*)ti.memberOf in moduleIndex)
                return Owner(*p + 1, null);
            return Owner.init;
        }
        return Owner(0, ti);
    }

    auto moduleCost = new size_t[modules.length];
    size_t[void*] instanceCost;
    TemplateInstance[] instances;           // the units that are instances, in order
    TemplateInstance[] withModule;          // instances generated with a module
    size_t[] withModuleIndex;
    foreach (j, m; modules)
    {
        if (!m.members)
            continue;
        moduleCost[j] += codeSize(m.members);
        foreach (s; *m.members)
        {
            auto ti = s.isTemplateInstance();
            if (!ti || isError(ti) || !ti.members || !ti.needsCodegen())
                continue;
            const cost = codeSize(ti.members);
            auto u = unitOf(ti);
            if (u.moduleIndex)
            {
                moduleCost[u.moduleIndex - 1] += cost;
                withModule ~= ti;
                withModuleIndex ~= u.moduleIndex - 1;
            }
            else if (u.ti)
            {
                if (auto c = cast(void*)u.ti in instanceCost)
                    *c += cost;
                else
                {
                    instanceCost[cast(void*)u.ti] = cost;
                    instances ~= u.ti;
                }
            }
        }
    }

    auto load = new size_t[n];
    uint leastLoaded()
    {
        uint least = 0;
        foreach (k; 1 .. n)
            if (load[k] < load[least])
                least = cast(uint)k;
        return least;
    }
    __gshared Unit[] sorting;
    extern (C) static int largestFirst(const void* a, const void* b)
    {
        auto x = cast(const Unit*)a, y = cast(const Unit*)b;
        if (x.cost != y.cost)
            return x.cost < y.cost ? 1 : -1;
        return (x.order > y.order) - (x.order < y.order);
    }

    auto units = new Unit[modules.length];
    foreach (j; 0 .. modules.length)
        units[j] = Unit(moduleCost[j] + 1, j, null, j);
    qsort(units.ptr, units.length, Unit.sizeof, &largestFirst);
    auto assign = new uint[modules.length];
    foreach (ref u; units)
    {
        const k = leastLoaded();
        assign[u.moduleIndex] = k;
        load[k] += u.cost;
    }

    units = new Unit[instances.length];
    foreach (i, ti; instances)
        units[i] = Unit(instanceCost[cast(void*)ti] + 1, i, ti, 0);
    qsort(units.ptr, units.length, Unit.sizeof, &largestFirst);
    foreach (ref u; units)
    {
        const k = leastLoaded();
        setInstanceWorker(u.ti, k);
        load[k] += u.cost;
    }
    foreach (i, ti; withModule)
        setInstanceWorker(ti, assign[withModuleIndex[i]]);
    return assign;
}

/* Returns: the name of template instance `ti` among the functions and instances a
 * split compilation settles who generates. The mangled name of an instance tells
 * neither overloaded templates apart, nor the instances of a function template with
 * `auto ref` parameters, which that of its function does.
 */
private const(char)[] instanceName(TemplateInstance ti)
{
    import dmd.mangle : mangleExact, mangleToBuffer;
    OutBuffer buf;
    buf.writeByte('\x02');
    auto fd = ti.aliasdecl ? ti.aliasdecl.isFuncDeclaration() : null;
    if (fd && fd.parent is ti)  // not a function the instance is an alias of
        buf.writestring(mangleExact(fd).toDString());
    else
    {
        mangleToBuffer(cast(Dsymbol)ti, buf);   // qualified by the template's parents
        const loc = ti.tempdecl ? ti.tempdecl.loc : ti.loc;
        buf.printf("@%s:%u:%u", loc.filename, loc.linnum, loc.charnum);
    }
    return buf.extractSlice();
}

/* In a worker of a split compilation: whether it generates `s`, a function or
 * template instance of group `g`, now; if not, it is generated by another worker,
 * or put off until the workers settle who generates it
 */
private bool generatesHere(Dsymbol s, const(char)[] name, ref SplitGroup g, bool canGenerateHead)
{
    import dmd.parallel : generateSettled, noteLeftPinned, thisWorker;

    if (g.pinned == thisWorker())
        return true;
    if (g.pinned >= 0)
    {
        noteLeftPinned(name, g.name, g.pinned);
        return false;
    }
    return generateSettled(s, name, g.head, g.name, canGenerateHead);
}

/// Returns: true if this worker can generate `head`, the head of a group
private bool canGenerate(Dsymbol head)
{
    import dmd.templatesem : needsCodegen;
    if (auto ti = head.isTemplateInstance())
        return !isError(ti) && ti.members && ti.needsCodegen();
    auto fd = head.isFuncDeclaration();
    return fd.fbody && !fd.hasSemantic3Errors && !fd.skipCodegen && fd.semanticRun >= PASS.semantic3done &&
        !inNonRootFunction(fd);
}

/**************************************
 * In a worker of a split compilation: whether it generates template instance `ti`,
 * which needs code generated.
 */
bool instanceGeneratedHere(TemplateInstance ti)
{
    import dmd.parallel : inSplitWorker, noteGenerated, thisWorker;

    if (!inSplitWorker())
        return true;
    auto g = instanceGroup(ti);
    if (g.pinned >= 0 && g.pinned != thisWorker())
        return false;   // the worker generating it walks the modules' instances too
    const name = g.head is ti ? g.name : instanceName(ti);
    if (!generatesHere(ti, name, g, g.head is ti || canGenerate(g.head)))
        return false;
    noteGenerated(name);
    return true;
}

/**************************************
 * In a worker of a split compilation, generate the template instances of the root
 * modules other workers generate that the plan of the split (see `planSplit`) has
 * this worker generate.
 */
private void generatePlannedInstances(bool multiobj)
{
    import dmd.parallel : instanceWorker, otherModules, thisWorker;
    import dmd.templatesem : needsCodegen;

    foreach (o; otherModules())
    {
        foreach (s; (*o.m.members)[0 .. o.membersAtSplit])
        {
            auto ti = s.isTemplateInstance();
            if (ti && instanceGroup(ti).pinned == thisWorker())
                toObjFile(ti, multiobj);
        }
    }
}

/* The backend inline expands a function call only into a function compiled after the
 * function called, whose optimized code it copies. So that what is inlined does not
 * depend on the order the functions are compiled in, which in a split compilation
 * depends on how they are split, a function `f` may only have inlined the functions
 * `inlineCallees(f)` gives: those it calls directly that rank before it, a function's
 * rank being the position of its outermost enclosing function among the members of
 * the root modules (see `rankFunctions`), then its mangled name. They are compiled
 * before `f` is, in any process compiling `f`: in a worker of a split compilation, a
 * weak definition of a function another worker generates is so generated here too.
 */

/// The position of each function among the members of the root modules
private __gshared uint[void*] functionPositions;

/**************************************
 * Rank the functions of the root modules for the backend inliner (see
 * `inlineCallees`), by their position among the members of `modules`, the members of
 * a template instance being where the instance is.
 */
public void rankFunctions(Module[] modules)
{
    import dmd.dsymbolsem : include;

    uint position;
    void walk(Dsymbols* members)
    {
        if (!members)
            return;
        foreach (s; *members)
        {
            if (auto fd = s.isFuncDeclaration())
                functionPositions[cast(void*)fd] = ++position;
            else if (auto ti = s.isTemplateInstance())
            {
                if (!isError(ti))
                    walk(ti.members);
            }
            else if (s.isAttribDeclaration())
                walk(include(s, null));
            else if (auto sds = s.isScopeDsymbol())
            {
                if (!s.isTemplateDeclaration())
                    walk(sds.members);
            }
        }
    }
    foreach (m; modules)
        walk(m.members);
}

/// Returns: true if function `g` ranks before function `f` (see `inlineCallees`)
private bool ranksBefore(FuncDeclaration g, FuncDeclaration f)
{
    import dmd.mangle : mangleExact;

    static uint position(FuncDeclaration fd)
    {
        if (auto p = cast(void*)frameRoot(fd) in functionPositions)
            return *p;
        return uint.max;
    }
    const pg = position(g), pf = position(f);
    if (pg != pf)
        return pg < pf;
    return strcmp(mangleExact(g), mangleExact(f)) < 0;
}

/* Returns: true if the code of `fd` may be a single basic block once optimized, which
 * the backend inlines, and is small enough to compile again for that
 */
private bool backendInlineShape(FuncDeclaration fd)
{
    import dmd.visitor : StoppableVisitor;
    import dmd.visitor.postorder : walkPostorder;

    enum maxStatements = 100;
    extern (C++) final class Finder : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        uint statements;
        extern (D) this() scope {}
        override void visit(Statement s)
        {
            if (++statements > maxStatements)
                stop = true;
        }
        override void visit(TryCatchStatement s) { stop = true; }
        override void visit(TryFinallyStatement s) { stop = true; }
        override void visit(ScopeGuardStatement s) { stop = true; }
        override void visit(SynchronizedStatement s) { stop = true; }
        override void visit(AsmStatement s) { stop = true; }
    }
    scope Finder v = new Finder();
    if (walkPostorder(fd.fbody, v))
        return false;

    /* A function compiled for inlining where it would not otherwise be duplicates its
     * code, which must then not define what it declares: data, whose address tells it
     * apart, nor functions or aggregates
     */
    extern (C++) final class Declarations : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        extern (D) this() scope {}
        override void visit(Expression e) {}
        override void visit(FuncExp e) { stop = true; }
        override void visit(DeclarationExp e)
        {
            auto d = e.declaration;
            if (auto vd = d.isVarDeclaration())
            {
                if (vd.isDataseg())
                    stop = true;
            }
            else if (d.isFuncDeclaration() || d.isAggregateDeclaration() || d.isAttribDeclaration())
                stop = true;
        }
    }
    import dmd.visitor.foreachvar : foreachExpAndVar;
    scope Declarations d = new Declarations();
    bool declares;
    foreachExpAndVar(fd.fbody, (Expression e) {
        if (!declares && walkPostorder(e, d))
            declares = true;
    }, (VarDeclaration vd) {
        if (vd.isDataseg())
            declares = true;
    });
    return !declares;
}

/// Returns: true if the backend may inline function `g` into function `f`, which
/// calls it (see `inlineCallees`)
private bool backendInlinable(FuncDeclaration g, FuncDeclaration f)
{
    import dmd.templatesem : needsCodegen;

    if (g is f || !g.fbody || g.hasSemantic3Errors || g.skipCodegen || g.isNaked ||
        g.semanticRun < PASS.semantic3done || g.semanticRun == PASS.semanticdone ||
        g.isNested() || g.inlinedNestedCallees || inNonRootFunction(g) || registersWithModule(g) ||
        g.isUnitTestDeclaration())
        return false;
    if (auto ti = g.isInstantiated())
    {
        if (isError(ti) || !ti.needsCodegen())
            return false;
    }
    else if (target.os != Target.OS.OSX && g.getModule() !is f.getModule())
        return false;   // only on Mach-O is every function a weak definition
    if (!(toSymbol(g).Sfunc.Fflags & Finline) || !ranksBefore(g, f))
        return false;
    return backendInlineShape(g);
}

/// Returns: the functions the backend may inline into `f`, which are compiled before it
private FuncDeclaration[] inlineCallees(FuncDeclaration f)
{
    import dmd.visitor : StoppableVisitor;
    import dmd.visitor.foreachvar : foreachExpAndVar;
    import dmd.visitor.postorder : walkPostorder;
    import dmd.init : ExpInitializer;

    if (!f.fbody)
        return null;
    FuncDeclaration[] callees;
    bool[void*] seen;

    extern (C++) final class Collector : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        extern (D) void delegate(Expression) walk;
        extern (D) void delegate(VarDeclaration) var;
        extern (D) void delegate(FuncDeclaration) call;
        extern (D) this() scope {}
        override void visit(Expression e) {}
        override void visit(CallExp e)
        {
            if (e.f && (!e.f.isVirtual() || e.directcall))
                call(e.f);
        }
        override void visit(NewExp e)
        {
            if (e.member)
                call(e.member);     // the constructor
            walk(e.lowering);
        }
        override void visit(ArrayLiteralExp e) { walk(e.lowering); }
        override void visit(AssocArrayLiteralExp e) { walk(e.lowering); }
        override void visit(CastExp e) { walk(e.lowering); }
        override void visit(LoweredAssignExp e) { walk(e.lowering); }
        override void visit(ConstructExp e) { walk(e.lowering); }
        override void visit(DeclarationExp e)
        {
            if (auto vd = e.declaration.isVarDeclaration())
                var(vd);
        }
    }
    scope Collector c = new Collector();
    void walkExp(Expression e)
    {
        if (e)
            walkPostorder(e, c);
    }
    void walkVar(VarDeclaration vd)
    {
        if (vd._init)
            if (auto ei = vd._init.isExpInitializer())
                walkExp(ei.exp);
        walkExp(vd.edtor);
    }
    void call(FuncDeclaration g)
    {
        if (cast(void*)g in seen)
            return;
        seen[cast(void*)g] = true;
        if (backendInlinable(g, f))
            callees ~= g;
    }
    c.walk = &walkExp;
    c.var = &walkVar;
    c.call = &call;
    foreachExpAndVar(f.fbody, &walkExp, &walkVar);
    return callees;
}

/* In a worker of a split compilation: the function generated here whatever worker the
 * split has generate it, as the function being generated may have it inlined
 */
private __gshared FuncDeclaration generatedForInlining;

/* Generate the code of `fp` now, as the code of the function being generated depends
 * on the layout of its frame. In a worker of a split compilation, if another worker
 * generates `fp`, the split is given up.
 */
private void toObjFileFramesFirst(FuncDeclaration fp, bool multiobj)
{
    import dmd.parallel : abandonSplit, inSplitWorker;
    import dmd.mangle : mangleExact;

    const left = functionsLeftToOtherWorkers;
    toObjFile(fp, multiobj);
    if (inSplitWorker() && fp.semanticRun < PASS.obj && functionsLeftToOtherWorkers != left)
        abandonSplit("its frame is needed by a function generated by another worker", mangleExact(fp).toDString());
}

/// Returns: true if `fd` is marked to have no code generated, which toSymbol() may do
private bool skipsCodegen(FuncDeclaration fd)
{
    toSymbol(fd);
    return fd.skipCodegen;
}

void FuncDeclaration_toObjFile(FuncDeclaration fd, bool multiobj)
{
    ClassDeclaration cd = fd.parent.isClassDeclaration();
    //printf("FuncDeclaration_toObjFile(%p, %s.%s)\n", fd, fd.parent.toChars(), fd.toChars());
    //printf("storage_class: %llx\n", fd.storage_class);

    //if (type) printf("type = %s\n", type.toChars());
    version (none)
    {
        //printf("line = %d\n", getWhere() / LINEINC);
        EEcontext* ee = env.getEEcontext();
        if (ee.EEcompile == 2)
        {
            if (ee.EElinnum < (getWhere() / LINEINC) ||
                ee.EElinnum > (endwhere / LINEINC)
               )
                return;             // don't compile this function
            ee.EEfunc = toSymbol(this);
        }
    }

    if (fd.semanticRun >= PASS.obj) // if toObjFile() already run
        return;

    if (fd.type && fd.type.ty == Tfunction && (cast(TypeFunction)fd.type).next is null)
        return;

    // If errors occurred compiling it, such as https://issues.dlang.org/show_bug.cgi?id=6118
    if (fd.type && fd.type.ty == Tfunction && (cast(TypeFunction)fd.type).next.ty == Terror)
        return;

    if (fd.hasSemantic3Errors)
        return;

    if (global.errors)
        return;

    if (!fd.fbody)
        return;

    if (fd.skipCodegen)
        return;

    UnitTestDeclaration ud = fd.isUnitTestDeclaration();
    if (ud && !global.params.useUnitTests)
        return;

    import dmd.timetrace;
    timeTraceBeginEvent(TimeTraceEventType.codegenFunction);
    scope (exit) timeTraceEndEvent(TimeTraceEventType.codegenFunction, fd);

    /* In a compilation split across worker processes, which worker generates a
     * function is decided by its group (see `functionGroup`). With multiobj, that is
     * decided before it is deferred to an object file of its own, unless it is not to
     * be generated, so that the other workers don't write such object files for it.
     */
    import dmd.parallel : inSplitWorker, noteGenerated, noteLeftPinned, thisWorker;
    import dmd.mangle : mangleExact;

    SplitGroup group;
    const(char)[] splitName;
    const split = inSplitWorker() && fd !is generatedForInlining;
    if (split)
    {
        group = functionGroup(fd);
        splitName = mangleExact(fd).toDString();
        if (group.pinned >= 0 && group.pinned != thisWorker())
        {
            if (fd.semanticRun != PASS.semanticdone && !inNonRootFunction(fd) && !skipsCodegen(fd))
                noteLeftPinned(splitName, group.name, group.pinned);
            ++functionsLeftToOtherWorkers;
            return;
        }
        if (multiobj && fd.semanticRun != PASS.semanticdone && !inNonRootFunction(fd) && !skipsCodegen(fd) &&
            !generatesHere(fd, splitName, group, canGenerate(group.head)))
        {
            ++functionsLeftToOtherWorkers;
            return;
        }
    }

    if (multiobj && !fd.isStaticDtorDeclaration() && !fd.isStaticCtorDeclaration()
        && !(fd.isCrtCtor || fd.isCrtDtor) && !(fd.storage_class & STC.static_ && fd.isCsymbol()))
    {
        obj_append(fd);
        return;
    }

    if (fd.semanticRun == PASS.semanticdone)
    {
        /* What happened is this function failed semantic3() with errors,
         * but the errors were gagged.
         * Try to reproduce those errors, and then fail.
         */
        auto eSink = global.errorSink;
        eSink.error(fd.loc, "%s `%s` errors compiling the function", fd.kind, fd.toPrettyChars);
        return;
    }
    assert(fd.semanticRun >= PASS.semantic3done && fd.semanticRun <= PASS.inlineAll);
    assert(fd.ident != Id.empty);

    if (inNonRootFunction(fd))
        return;

    if (UnitTestDeclaration udp = needsDeferredNested(fd))
    {
        /* Can't do unittest's out of order, they are order dependent in that their
         * execution is done in lexical order.
         */
        udp.deferredNested.push(fd);
        //printf("%s @[%s]\n\t-. pushed to unittest @[%s]\n",
        //    fd.toPrettyChars(), fd.loc.toChars(), udp.loc.toChars());
        return;
    }

    Symbol* s = toSymbol(fd); // may set skipCodegen
    func_t* f = s.Sfunc;
    if (fd.skipCodegen) // test it again, as toSymbol() might have set it
        return;
    if (split && !generatesHere(fd, splitName, group, canGenerate(group.head)))
    {
        ++functionsLeftToOtherWorkers;
        return;
    }
    if (split)
        noteGenerated(splitName);
    ++functionsGenerated;

    // start code generation
    fd.semanticRun = PASS.obj;
    findUnusedNested(fd);

    if (global.params.v.verbose)
    {
        auto eSink = global.errorSink;
        eSink.message(Loc.init, "function  %s", fd.toPrettyChars());
    }

    // tunnel type of "this" to debug info generation
    if (AggregateDeclaration ad = fd.parent.isAggregateDeclaration())
    {
        .type* t = Type_toCtype(getType(ad));
        if (cd)
            t = t.Tnext; // skip reference
        f.Fclass = cast(Classsym *)t;
    }

    /* This is done so that the 'this' pointer on the stack is the same
     * distance away from the function parameters, so that an overriding
     * function can call the nested fdensure or fdrequire of its overridden function
     * and the stack offsets are the same.
     */
    if (fd.isVirtual() && (fd.fensure || fd.frequire))
        f.Fflags |= Ffakeeh;

    if (fd.hasNoEH)
        // Same as config.ehmethod==EH_NONE, but only for this function
        f.Fflags |= Feh_none;

    s.Sclass = target.os == Target.OS.OSX ? SC.comdat : SC.global;

    /* Make C static functions SCstatic
     */
    if (fd.storage_class & STC.static_ && fd.isCsymbol())
        s.Sclass = SC.static_;

    for (Dsymbol p = fd.parent; p; p = p.parent)
    {
        if (p.isTemplateInstance())
        {
            // functions without D or C++ name mangling mixed in at global scope
            // shouldn't have multiple definitions
            const linkage = fd.resolvedLinkage();
            if (p.isTemplateMixin() && (linkage == LINK.c || linkage == LINK.windows ||
                linkage == LINK.objc))
            {
                const q = p.toParent();
                if (q && q.isModule())
                {
                    s.Sclass = SC.global;
                    break;
                }
            }
            s.Sclass = SC.comdat;
            break;
        }
    }

    if (fd.inlinedNestedCallees)
    {
        /* https://issues.dlang.org/show_bug.cgi?id=15333
         * If fd contains inlined expressions that come from
         * nested function bodies, the enclosing of the functions must be
         * generated first, in order to calculate correct frame pointer offset.
         */
        foreach (fdc; *fd.inlinedNestedCallees)
        {
            FuncDeclaration fp = fdc.toParent2().isFuncDeclaration();
            if (fp && fp.semanticRun < PASS.obj)
            {
                toObjFileFramesFirst(fp, multiobj);
            }
        }
    }

    if (fd.isNested())
    {
        //if (!(config.flags3 & CFG3pic))
        //    s.Sclass = SCstatic;
        f.Fflags |= Fnested;

        /* The enclosing function must have its code generated first,
         * in order to calculate correct frame pointer offset.
         */
        FuncDeclaration fdp = fd.toParent2().isFuncDeclaration();
        if (fdp && fdp.semanticRun < PASS.obj)
        {
            toObjFileFramesFirst(fdp, multiobj);
        }
    }
    else
    {
        if (entryPointFunctions(objmod, fd))
            s.Sclass = SC.global;
    }

    // the functions the backend may inline into this one are compiled first
    FuncDeclaration[] inlined = driverParams.optimize ? inlineCallees(fd) : null;
    foreach (g; inlined)
    {
        if (g.semanticRun >= PASS.obj)
            continue;
        auto saved = generatedForInlining;
        generatedForInlining = g;
        toObjFile(g, false);
        generatedForInlining = saved;
    }

    symtab_t* symtabsave = cstate.CSpsymtab;
    cstate.CSpsymtab = &f.Flocsym;

    // Find module m for this function
    Module m = null;
    for (Dsymbol p = fd.parent; p; p = p.parent)
    {
        m = p.isModule();
        if (m)
            break;
    }

    Dsymbols deferToObj;                   // write these to OBJ file later
    Array!(elem*) varsInScope;
    Label*[void*] labels = null;
    IRState irs = IRState(m, fd, &varsInScope, &deferToObj, &labels, &global.params, &target, global.errorSink);

    // function literals inlined into fd are emitted as if it still called them
    if (fd.inlinedNestedCallees)
    {
        foreach (fdc; *fd.inlinedNestedCallees)
        {
            auto fld = fdc.isFuncLiteralDeclaration();
            if (!fld || fld.isNested() || fld.deferToObj)
                continue;
            if (fld.tok == TOK.reserved)
            {
                fld.tok = TOK.function_;
                fld.vthis = null;
            }
            fld.deferToObj = true;
            deferToObj.push(fld);
        }
    }

    Symbol* shidden = null;
    Symbol* sthis = null;
    tym_t tyf = tybasic(s.Stype.Tty);
    //printf("linkage = %d, tyf = x%x\n", linkage, tyf);
    int reverse = tyrevfunc(s.Stype.Tty);

    assert(fd.type.ty == Tfunction);
    auto tf = cast(TypeFunction)fd.type;
    const retmethod = retStyle(tf, fd.needThis());
    if (retmethod == RET.stack)
    {
        // If function returns a struct, put a pointer to that
        // as the first argument
        .type* thidden = Type_toCtype(tf.next.pointerTo());
        const hiddenparamLen = 5 + 10 + 1;
        char[hiddenparamLen] hiddenparam = void;
        __gshared uint hiddenparami;    // how many we've generated so far

        const(char)[] name;
        if (fd.isNRVO && fd.nrvo_var)
            name = fd.nrvo_var.ident.toString();
        else
        {
            int length = snprintf(hiddenparam.ptr, hiddenparamLen, "__HID%u", ++hiddenparami);
            assert(length != -1 &&     // for bad old snprintf()
                   length < hiddenparamLen);
            name = hiddenparam[0 .. length];
        }
        shidden = symbol_name(name, SC.parameter, thidden);
        shidden.Sflags |= SFLtrue | SFLfree | SFLhidden;
        if (fd.isNRVO && fd.nrvo_var && referencedFromNested(fd.nrvo_var))
            type_setcv(&shidden.Stype, shidden.Stype.Tty | mTYvolatile);
        irs.shidden = shidden;
        fd.shidden = shidden;
    }
    else
    {
        // Register return style cannot make nrvo.
        // Auto functions keep the NRVO flag up to here,
        // so we should eliminate it before entering backend.
        fd.isNRVO = false;
    }

    if (fd.vthis)
    {
        assert(!fd.vthis.csym);
        sthis = toSymbol(fd.vthis);
        sthis.Stype = getParentClosureType(sthis, fd);
        irs.sthis = sthis;
        if (!(f.Fflags & Fnested))
            f.Fflags |= Fmember;
    }

    // Estimate number of parameters, pi
    size_t pi = (fd.v_arguments !is null);
    if (fd.parameters)
        pi += fd.parameters.length;
    if (fd.objc.selector)
        pi++; // Extra argument for Objective-C selector
    // Create a temporary buffer, params[], to hold function parameters
    Symbol*[10] paramsbuf = void;
    Symbol **params = paramsbuf.ptr;    // allocate on stack if possible
    if (pi + 2 > paramsbuf.length)      // allow extra 2 for sthis and shidden
    {
        params = cast(Symbol**)Mem.check(malloc((pi + 2) * (Symbol*).sizeof));
    }

    // Get the actual number of parameters, pi, and fill in the params[]
    pi = 0;
    if (fd.v_arguments)
    {
        params[pi] = toSymbol(fd.v_arguments);
        pi += 1;
    }
    Symbol* lastParam;
    if (fd.parameters)
    {
        foreach (i, v; *fd.parameters)
        {
            //printf("param[%d] = %p, %s\n", cast(int)i, v, v.toChars());
            assert(!v.csym);
            lastParam = toSymbol(v);
            params[pi + i] = lastParam;
        }
        pi += fd.parameters.length;
    }

    if (reverse)
    {
        // Reverse params[] entries
        foreach (i, sptmp; params[0 .. pi/2])
        {
            params[i] = params[pi - 1 - i];
            params[pi - 1 - i] = sptmp;
        }
    }

    if (shidden)
    {
        // shidden becomes last parameter
        //params[pi] = shidden;

        // shidden becomes first parameter
        memmove(params + 1, params, pi * (params[0]).sizeof);
        params[0] = shidden;

        pi++;
    }

    pi = objc.addSelectorParameterSymbol(fd, params, pi);

    if (sthis)
    {
        // sthis becomes last parameter
        //params[pi] = sthis;

        // sthis becomes first parameter
        memmove(params + 1, params, pi * (params[0]).sizeof);
        params[0] = sthis;

        pi++;
    }

    if (target.isPOSIX && fd._linkage != LINK.d && shidden && sthis)
    {
        /* swap shidden and sthis
         */
        Symbol* sp = params[0];
        params[0] = params[1];
        params[1] = sp;
    }

    foreach (sp; params[0 .. pi])
    {
        sp.Sclass = SC.parameter;
        sp.Sflags &= ~SFLspill;
        sp.Sfl = FL.para;
        symbol_add(sp);
    }

    // Determine register assignments
    if (pi)
    {
        FuncParamRegs fpr = FuncParamRegs.create(tyf);

        foreach (sp; params[0 .. pi])
        {
            if (target.isAArch64 && sp == shidden)
            {
                // AAPCS64 indirect result location register
                sp.Spreg = 8;
                sp.Spreg2 = NOREG;
                sp.Sclass = SC.fastpar;
                sp.Sfl = FL.fast;
                continue;
            }
            if (fpr.alloc(sp.Stype, sp.Stype.Tty, sp.Spreg, sp.Spreg2))
            {
                // successful allocation
                //printf("ident %s reg %d reg2 %d\n", sp.Sident.ptr, sp.Spreg, sp.Spreg2);
                sp.Sclass = (target.os == Target.OS.Windows && target.isX86_64) ? SC.shadowreg : SC.fastpar;
                sp.Sfl = (sp.Sclass == SC.shadowreg) ? FL.para : FL.fast;
            }
        }
    }

    // Done with params
    if (params != paramsbuf.ptr)
        free(params);
    params = null;

    localgot = null;

    Statement sbody = fd.fbody;

    BlockState bx;
    bx.startblock = block_calloc(bo);
    bx.curblock = bx.startblock;
    bx.funcsym = s;
    bx.scope_index = -1;
    bx.classdec = cast(void*)cd;
    bx.member = cast(void*)fd;
    bx._module = cast(void*)fd.getModule();
    irs.blx = &bx;

    // Initialize argptr
    if (fd.v_argptr)   // created for variadic functions
    {
        if (target.isAArch64 && target.os == Target.os.OSX)
        {
            type* t = type_fake(TYnptr); /// pointer to void
            // The backend will pick this up by name and set it to the last named parameter
            Symbol* sv = symbol_name("__va_argsave", SC.auto_, t);
            sv.Stype.Tty |= mTYvolatile;
            symbol_add(sv);
        }
        else if ((target.isX86_64 || target.isAArch64) &&
            target.os & Target.OS.Posix)
        {
            type* t = target.isX86_64
                ? type_struct_class("__va_argsave_t", 16, 8 * 6 + 8 * 16 + 8 * 3 + 8, null, null, false, false, true, false)
                : type_struct_class("__va_argsave_t", 16, 8 * 8 + 8 * 16 + 8 * 4 + 8, null, null, false, false, true, false);
            // The backend will pick this up by name
            Symbol* sv = symbol_name("__va_argsave", SC.auto_, t);
            sv.Stype.Tty |= mTYvolatile;
            symbol_add(sv);
        }

        // Declare _argptr, but only for D files
        if (!irs.Cfile)
        {
            Symbol* sa = toSymbol(fd.v_argptr);
            symbol_add(sa);
            // (&v_argptr OPva_start &lastParam)
            elem* e = el_bin(OPva_start, TYnptr, el_ptr(sa), lastParam ? el_ptr(lastParam) : el_long(TYnptr, 0));
            block_appendexp(irs.blx.curblock, e);
        }
    }

    /* Doing this in semantic3() caused all kinds of problems:
     * 1. couldn't reliably get the final mangling of the function name due to fwd refs
     * 2. impact on function inlining
     * 3. what to do when writing out .di files, or other pretty printing
     */
    if (global.params.trace && !fd.isCMain() && !fd.isNaked && !fd.hasInlineAsm)
    {
        /* The profiler requires TLS, and TLS may not be set up yet when C main()
         * gets control (i.e. OSX), leading to a crash.
         */
        /* Wrap the entire function body in:
         *   trace_pro("funcname");
         *   try
         *     body;
         *   finally
         *     _c_trace_epi();
         */
        StringExp se = StringExp.create(Loc.initial, s.Sident.ptr);
        se.type = Type.tstring;
        se.type = se.type.typeSemantic(Loc.initial, null);
        Expressions* exps = new Expressions(se);
        FuncDeclaration fdpro = genCfunc(null, Type.tvoid, "trace_pro");
        Expression ec = VarExp.create(Loc.initial, fdpro);
        Expression e = CallExp.create(Loc.initial, ec, exps);
        e.type = Type.tvoid;
        Statement sp = ExpStatement.create(fd.loc, e);

        FuncDeclaration fdepi = genCfunc(null, Type.tvoid, "_c_trace_epi");
        ec = VarExp.create(Loc.initial, fdepi);
        e = CallExp.create(Loc.initial, ec);
        e.type = Type.tvoid;
        Statement sf = ExpStatement.create(fd.loc, e);

        Statement stf;
        if (sbody.blockExit(fd, null) == BE.fallthru)
            stf = CompoundStatement.create(Loc.initial, sbody, sf);
        else
            stf = TryFinallyStatement.create(Loc.initial, sbody, sf);
        sbody = CompoundStatement.create(Loc.initial, sp, stf);
    }

    if (fd.interfaceVirtual)
    {
        // Adjust the 'this' pointer instead of using a thunk
        assert(irs.sthis);
        elem* ethis = el_var(irs.sthis);
        ethis = fixEthis2(ethis, fd);
        elem* e = el_bin(OPminass, TYnptr, ethis, el_long(TYsize_t, fd.interfaceVirtual.offset));
        block_appendexp(irs.blx.curblock, e);
    }

    buildClosure(fd, irs);
    buildAlignSection(fd, irs); // must be after buildClosure

    if (config.ehmethod == EHmethod.EH_WIN32 && fd.isSynchronized() && cd &&
        !fd.isStatic() && !sbody.usesEH() && !global.params.trace)
    {
        /* The "jmonitor" hack uses an optimized exception handling frame
         * which is a little shorter than the more general EH frame.
         */
        s.Sfunc.Fflags |= Fjmonitor;
    }

    Statement_toIR(sbody, irs);

    if (global.errors)
    {
        // Restore symbol table
        cstate.CSpsymtab = symtabsave;
        return;
    }

    bx.curblock.bc = BC.ret;

    /* The flag el_ctor_dtor() makes for a temporary destroyed if an exception
     * leaves its construction is read by the landing pad also where a ?: or &&
     * did not construct it, so it starts out clear
     */
    if (config.ehmethod == EHmethod.EH_DWARF)
        foreach (sf; f.Flocsym[])
            if (sf.Sclass == SC.auto_ && strcmp(sf.Sident.ptr, "__flag") == 0 &&
                tybasic(sf.Stype.Tty) == TYbool && sf.Stype.Tty & mTYvolatile)
            {
                elem* e0 = el_bin(OPeq, TYvoid, el_var(sf), el_long(TYbool, 0));
                bx.startblock.Belem = el_combine(e0, bx.startblock.Belem);
            }

    f.Fstartblock = bx.startblock;
//  einit = el_combine(einit,bx.init);

    if (fd.isCtorDeclaration())
    {
        assert(sthis);
        foreach (b; BlockRange(f.Fstartblock))
        {
            if (b.bc == BC.ret)
            {
                elem* ethis = el_var(sthis);
                ethis = fixEthis2(ethis, fd);
                b.bc = BC.retexp;
                b.Belem = el_combine(b.Belem, ethis);
            }
        }
    }
    if (config.ehmethod == EHmethod.EH_NONE || f.Fflags & Feh_none)
        insertFinallyBlockGotos(f.Fstartblock);
    else if (config.ehmethod == EHmethod.EH_DWARF)
        insertFinallyBlockCalls(f.Fstartblock);

    // If static constructor
    if (auto sctor = fd.isSharedStaticCtorDeclaration())        // must come first because it derives from StaticCtorDeclaration
    {
        if (sctor.standalone)
            glue.sisharedctors.push(s);
        else
            glue.ssharedctors.push(s);
    }
    else if (fd.isStaticCtorDeclaration())
    {
        glue.sctors.push(s);
    }

    // If static destructor
    if (fd.isSharedStaticDtorDeclaration())        // must come first because it derives from StaticDtorDeclaration
    {
        SharedStaticDtorDeclaration fs = fd.isSharedStaticDtorDeclaration();
        assert(fs);
        if (fs.vgate)
        {
            /* Increment destructor's vgate at construction time
             */
            glue.esharedctorgates.push(fs);
        }

        glue.sshareddtors.shift(s);
    }
    else if (fd.isStaticDtorDeclaration())
    {
        StaticDtorDeclaration fs = fd.isStaticDtorDeclaration();
        assert(fs);
        if (fs.vgate)
        {
            /* Increment destructor's vgate at construction time
             */
            glue.ectorgates.push(fs);
        }

        glue.sdtors.shift(s);
    }

    // If unit test
    if (ud)
    {
        glue.stests.push(s);
        glue.testNames.push(ud.ident);
    }

    if (global.errors)
    {
        // Restore symbol table
        cstate.CSpsymtab = symtabsave;
        return;
    }

    foreach (g; inlined)
        toSymbol(g).Sfunc.Fflags |= Finlinecallee;
    writefunc(s); // hand off to backend
    foreach (g; inlined)
        toSymbol(g).Sfunc.Fflags &= ~Finlinecallee;

    buildCapture(fd);

    // Restore symbol table
    cstate.CSpsymtab = symtabsave;

    if (fd.isExport() || driverParams.exportVisibility == ExpVis.public_)
        objmod.export_symbol(s, cast(uint)cgstate.Para.offset);

    if (fd.isCrtCtor)
        objmod.setModuleCtorDtor(s, true);

    if (fd.isCrtDtor)
    {
        //See TargetC.initialize
        if(target.c.crtDestructorsSupported)
        {
            objmod.setModuleCtorDtor(s, false);
        } else
        {
             /*
                https://issues.dlang.org/show_bug.cgi?id=22520

                Apple radar: https://openradar.appspot.com/FB9733712

                Apple deprecated the mechanism used to implement `crt_destructor`
                on MacOS Monterey. This works around that by generating a new function
                (crt_destructor_thunk_NNN, run as a constructor) which registers
                the destructor-to-be using __cxa_atexit()

                This workaround may need a further look at when it comes to
                shared library support, however there is no bridge for
                that spilt milk to flow under yet.

                This relies on the Itanium ABI so is portable to any
                platform it, if needed.
            */
            __gshared uint nthDestructor = 0;
            char* buf = cast(char*) Mem.check(calloc(50, 1));
            const ret = snprintf(buf, 100, "_dmd_crt_destructor_thunk.%u", nthDestructor++);
            assert(ret >= 0 && ret < 100, "snprintf either failed or overran buffer");
            //Function symbol
            auto newConstructor = symbol_calloc(buf[0 .. strlen(buf)]);
            //Build type
            newConstructor.Stype = type_function(TYnfunc, [], false, type_alloc(TYvoid));
            //Tell it it's supposed to be a C function. Does it do anything? Not sure.
            type_setmangle(&newConstructor.Stype, Mangle.c);
            symbol_func(*newConstructor);
            //Global SC for now.
            newConstructor.Sclass = SC.static_;
            func_t* funcState = newConstructor.Sfunc;
            //Init start block
            funcState.Fstartblock = block_calloc(bo);
            block* startBlk = funcState.Fstartblock;
            //Make that block run __cxa_atexit(&func);
            auto atexitSym = getRtlsym(RTLSYM.CXA_ATEXIT);
            Symbol* dso_handle = symbol_calloc("__dso_handle");
            dso_handle.Stype = type_fake(TYint);
            //Try to get MacOS _ prefix-ism right.
            type_setmangle(&dso_handle.Stype, Mangle.c);
            dso_handle.Sfl = FL.extern_;
            dso_handle.Sclass = SC.extern_;
            dso_handle.Stype.Tcount++;
            auto handlePtr = el_ptr(dso_handle);
            //Build parameter pack - __cxa_atexit(&func, null, null)
            auto paramPack = el_params(handlePtr, el_long(TYnptr, 0), el_ptr(s), null);
            auto exec = el_bin(OPcall, TYvoid, el_var(atexitSym), paramPack);
            block_appendexp(startBlk, exec); //payload
            startBlk.bc = BC.goto_;
            auto next = block_calloc(bo);
            startBlk.Bsucc.push(next);
            startBlk.Bnext = next;
            next.bc = BC.ret;
            //Emit in binary
            writefunc(newConstructor);
            //Mark as a CONSTRUCTOR because our thunk implements the destructor
            objmod.setModuleCtorDtor(newConstructor, true);
        }
    }

    foreach (sd; *irs.deferToObj)
    {
        toObjFile(sd, false);
    }

    if (ud)
    {
        foreach (fdn; ud.deferredNested)
        {
            toObjFile(fdn, false);
        }
    }

    if (irs.startaddress)
    {
        //printf("Setting start address\n");
        objmod.startaddress(irs.startaddress);
    }
}

private:

alias symbols = Array!(Symbol*);

struct Glue
{
    elem* eictor;
    Symbol* ictorlocalgot;

    symbols sctors; // static constructorss
    StaticDtorDeclarations ectorgates;
    symbols sdtors;
    symbols stests;
    Array!Identifier testNames;

    symbols ssharedctors; // shared static constructors
    symbols sisharedctors; // standalone shared static constructors
    SharedStaticDtorDeclarations esharedctorgates;
    symbols sshareddtors;

    const(char)* lastmname;
    Dsymbols obj_symbols_towrite;
}

private __gshared Glue glue;

/*******************************
 * Generating multiple object files, one per Dsymbol
 * in symbols_towrite[].
 * Params:
 *      library = library to write object files to
 *      symbols_towrite = array of Dsymbols
 */
extern (D)
private void obj_write_deferred(ref OutBuffer objbuf, Library library, ref Dsymbols symbols_towrite)
{
    // this array can grow during the loop; do not replace with foreach
    for (size_t i = 0; i < symbols_towrite.length; ++i)
    {
        Dsymbol s = symbols_towrite[i];
        Module m = s.getModule();

        const(char)* mname;
        if (m)
        {
            mname = m.srcfile.toChars();
            glue.lastmname = mname;
        }
        else
        {
            //mname = s.ident.toChars();
            mname = glue.lastmname;
            assert(mname);
        }
        auto mnames = mname.toDString();

        obj_start(objbuf, mname);
        const generated = functionsGenerated;
        const dataWritten = dataSymbolsWritten;

        /* A sequence for generating names; in a worker of a split compilation, of the
         * numbers the other workers do not use, so that the doppelganger modules of
         * different workers have different names
         */
        __gshared int count;
        __gshared bool counting;
        import dmd.parallel : thisWorker, workerStride;
        if (!counting)
        {
            counting = true;
            count = thisWorker();
        }
        count += workerStride();

        /* Create a module that's a doppelganger of m, with just
         * enough to be able to create the moduleinfo.
         */
        OutBuffer idbuf;
        idbuf.printf("%s.%d", m ? m.ident.toChars() : mname, count);

        if (!m)
        {
            // it doesn't make sense to make up a module if we don't know where to put the symbol
            //  so output it into its own object file without ModuleInfo
            objmod.initfile(idbuf.peekChars(), null, mname);
            toObjFile(s, false);
            objmod.termfile();
        }
        else
        {
            Identifier id = Identifier.create(idbuf.extractChars());

            Module md = new Module(m.loc, mnames, id, 0, 0);
            md.members = new Dsymbols(s);   // its only 'member' is s
            md.md = m.md;
            md.aimports.push(m);       // it only 'imports' m

            genObjFile(md, false, true);
        }

        /* Set object file name to be source name with sequence number,
         * as mangled symbol names get way too long.
         */
        const length = FileName.ext(mnames).length;
        const fname = mnames[0 .. mnames.length - (length ? length + 1 : 0)];  // +1 to remove .
        OutBuffer namebuf;
        uint hash = 0;
        for (const(char)* p = s.toChars(); *p; p++)
            hash += *p;
        namebuf.printf("%.*s_%x_%x.%.*s", cast(int)fname.length, fname.ptr, count, hash,
                       cast(int)target.obj_ext.length, target.obj_ext.ptr);

        /* In a worker of a split compilation, an object file with nothing in it, as
         * other workers generate what it was for or this one already has, is left out
         */
        import dmd.parallel : inSplitWorker;
        if (inSplitWorker() && functionsGenerated == generated && dataSymbolsWritten == dataWritten)
        {
            objmod.term(namebuf[]);
            objmod = null;
            objbuf.setsize(0);
            continue;
        }

        //printf("writing '%s'\n", fname);
        obj_end(objbuf, library, namebuf.extractSlice());
    }
    glue.obj_symbols_towrite.length = 0;
}


/***********************************************
 * Generate function that calls array of functions and gates.
 * Params:
 *      m = module symbol (for name mangling purposes)
 *      sctors = array of functions
 *      ectorgates = array of gates
 *      id = identifier string for generator function
 * Returns:
 *      function Symbol generated
 */

extern (D)
private Symbol* callFuncsAndGates(Module m, Symbol*[] sctors, StaticDtorDeclaration[] ectorgates,
        const(char)* id)
{
    if (!sctors.length && !ectorgates.length)
        return null;

    Symbol* sctor = null;

    __gshared type* t;
    if (!t)
    {
        /* t will be the type of the functions generated:
         *      extern (C) void func();
         */
        t = type_function(TYnfunc, null, false, tstypes[TYvoid]);
        t.Tmangle = Mangle.c;
    }

    localgot = null;
    sctor = toSymbolX(m, id, SC.global, t, "FZv");
    cstate.CSpsymtab = &sctor.Sfunc.Flocsym;
    elem* ector = null;

    foreach (f; ectorgates)
    {
        Symbol* s = toSymbol(f.vgate);
        elem* e = el_var(s);
        e = el_bin(OPaddass, TYint, e, el_long(TYint, 1));
        ector = el_combine(ector, e);
    }

    foreach (s; sctors)
    {
        elem* e = el_una(OPucall, TYvoid, el_var(s));
        ector = el_combine(ector, e);
    }

    block* b = block_calloc(bo);
    b.bc = BC.ret;
    b.Belem = ector;
    sctor.Sfunc.Fstartline.Sfilename = m.arg.xarraydup.ptr;
    sctor.Sfunc.Fstartblock = b;
    writefunc(sctor); // hand off to backend

    return sctor;
}

/**************************************
 * Prepare for generating obj file.
 * Params:
 *      objbuf = write object file contents to this
 *      srcfile = name of the source file
 */

private void obj_start(ref OutBuffer objbuf, const(char)* srcfile)
{
    //printf("obj_start()\n");

    bzeroSymbol = null;
    resetCtfeSymbolCache();
    rtlsym_reset();
    clearStringTab();
    objmod = Obj.initialize(&objbuf, srcfile, null);

    OutBuffer buf;
    buf.write("DMD ");
    buf.write(global.versionString());
    Obj.compiler(buf.peekChars());

    el_reset();
    cg87_reset();
    out_reset();
    objc.reset();
}


/****************************************
 * Finish creating the object module and writing it to objbuf[].
 * Then either write the object module to an actual file,
 * or add it to a library.
 * Params:
 *      objbuf = contains the generated contents of the object file
 *      objfilename = what to call the object module
 *      library = if non-null, add object module to this library
 */
private void obj_end(ref OutBuffer objbuf, Library library, const(char)[] objfilename)
{
    objmod.term(objfilename);
    //delete objmod;
    objmod = null;

    if (library)
    {
        // Transfer ownership of image buffer to library
        library.addObject(objfilename, cast(ubyte[]) objbuf.extractSlice[]);
    }
    else
    {
        //printf("write obj %s\n", objfilename);
        if (!writeFile(Loc.initial, objfilename, objbuf[]))
            return fatal();

        // For non-libraries, the object buffer should be cleared to
        // avoid repetitions.
        objbuf.destroy();
    }
}

/**************************************
 * Generate .obj file for Module.
 */

private void genObjFile(Module m, bool multiobj, bool doppelganger)
{
    //EEcontext* ee = env.getEEcontext();

    //printf("Module.genobjfile(multiobj = %d) %s\n", multiobj, m.toChars());

    import dmd.timetrace;
    timeTraceBeginEvent(TimeTraceEventType.codegenModule);
    scope(exit) timeTraceEndEvent(TimeTraceEventType.codegenModule, m);

    glue.lastmname = m.srcfile.toChars();

    objmod.initfile(glue.lastmname, null, m.toPrettyChars());

    glue.eictor = null;
    glue.ictorlocalgot = null;
    glue.sctors.setDim(0);
    glue.ectorgates.setDim(0);
    glue.sdtors.setDim(0);
    glue.ssharedctors.setDim(0);
    glue.sisharedctors.setDim(0);
    glue.esharedctorgates.setDim(0);
    glue.sshareddtors.setDim(0);
    glue.stests.setDim(0);
    glue.testNames.setDim(0);

    if (doppelganger)
    {
        /* Generate a reference to the moduleinfo, so the module constructors
         * and destructors get linked in.
         */
        Module mod = m.aimports[0];
        assert(mod);
        if (mod.hasCDtor)
        {
            Symbol* s = toSymbol(mod);
            //objextern(s);
            //if (!s.Sxtrnnum) objextdef(s.Sident);
            if (!s.Sxtrnnum)
            {
                //printf("%s\n", s.Sident);
//#if 0 /* This should work, but causes optlink to fail in common/newlib.asm */
//                objextdef(s.Sident);
//#else
                Symbol* sref = symbol_generate(SC.static_, type_fake(TYnptr));
                sref.Sfl = FL.data;
                auto dtb = DtBuilder(0);
                dtb.xoff(s, 0, TYnptr);
                sref.Sdt = dtb.finish();
                outdata(sref);
//#endif
            }
        }
    }

    Symbol* mcov;
    if (global.params.cov)
    {
        /* Create coverage identifier:
         *  uint[numlines] __coverage;
         */
        mcov = toSymbolX(m, "__coverage", SC.static_, type_fake(TYint), "Z");
        m.cov = mcov;
        mcov.Sflags |= SFLhidden;
        mcov.Stype.Tmangle = Mangle.d;
        mcov.Sfl = FL.data;

        auto dtb = DtBuilder(0);

        if (m.ctfe_cov)
        {
            // initalize the uint[] __coverage symbol with data from ctfe.
            static extern (C) int comp_uints (const scope void* a, const scope void* b)
                { return (*cast(uint*) a) - (*cast(uint*) b); }

            uint[] sorted_lines = m.ctfe_cov.keys;
            qsort(sorted_lines.ptr, sorted_lines.length, sorted_lines[0].sizeof,
                &comp_uints);

            uint lastLine = 0;
            foreach (line;sorted_lines)
            {
                // zero fill from last line to line.
                if (line)
                {
                    assert(line > lastLine);
                    dtb.nzeros((line - lastLine - 1) * 4);
                }
                dtb.dword(m.ctfe_cov[line]);
                lastLine = line;
            }
            // zero fill from last line to end
            if (m.numlines > lastLine)
                dtb.nzeros((m.numlines - lastLine) * 4);
        }
        else
        {
            dtb.nzeros(4 * m.numlines);
        }
        mcov.Sdt = dtb.finish();

        outdata(mcov);

        size_t sz = m.covb[0].sizeof;
        size_t n = (m.numlines + sz * 8) / (sz * 8);
        uint* p =  cast(uint*)Mem.check(calloc(n, sz));
        m.covb = p[0 .. n];
    }

    for (int i = 0; i < m.members.length; i++)
    {
        auto member = (*m.members)[i];
        //printf("toObjFile %s %s\n", member.kind(), member.toChars());
        toObjFile(member, multiobj);
    }

    /* Generating code can instantiate templates, adding the instances to modules
     * other workers of a split compilation compile; this worker generates them
     */
    import dmd.parallel : adoptLateInstances, settleRound;
    void generateLateInstances()
    {
        for (auto late = adoptLateInstances(); late.length; late = adoptLateInstances())
        {
            foreach (ti; late)
                toObjFile(ti, multiobj);
        }
    }
    generateLateInstances();

    /* The functions a worker has put off generating are settled with the other
     * workers once its last module's code is generated, and those it is to generate
     * are generated with that module
     */
    if (m is settleWith)
    {
        generatePlannedInstances(multiobj);
        generateLateInstances();
        Dsymbol[] generate;
        while (settleRound(functionsGenerated, generate))
        {
            foreach (sym; generate)
                toObjFile(sym, multiobj);
            generateLateInstances();
        }
    }

    Symbol* msictor;
    if (global.params.cov)
    {
        /* Generate
         *  private bit[numlines] __bcoverage;
         */
        Symbol* bcov = symbol_calloc("__bcoverage");
        bcov.Stype = type_fake(TYuint);
        bcov.Stype.Tcount++;
        bcov.Sclass = SC.static_;
        bcov.Sfl = FL.data;

        auto dtb = DtBuilder(0);
        dtb.nbytes(cast(const(ubyte)[]) m.covb);
        bcov.Sdt = dtb.finish();

        outdata(bcov);

        free(m.covb.ptr);
        m.covb = null;

        /* Generate:
         *  _d_cover_register(uint[] __coverage, BitArray __bcoverage, string filename);
         * and prepend it to the static constructor.
         */

        /* t will be the type of the functions generated:
         *      extern (C) void func();
         */
        type* t = type_function(TYnfunc, null, false, tstypes[TYvoid]);
        t.Tmangle = Mangle.c;

        msictor = toSymbolX(m, "__modictor", SC.global, t, "FZv");
        m.hasCDtor = true;
        cstate.CSpsymtab = &msictor.Sfunc.Flocsym;
        localgot = glue.ictorlocalgot;

        elem* ecov  = el_pair(TYdarray, el_long(TYsize_t, m.numlines), el_ptr(mcov));
        elem* ebcov = el_pair(TYdarray, el_long(TYsize_t, m.numlines), el_ptr(bcov));

        if (target.os == Target.OS.Windows && target.isX86_64)
        {
            ecov  = addressElem(ecov,  Type.tvoid.arrayOf(), false);
            ebcov = addressElem(ebcov, Type.tvoid.arrayOf(), false);
        }

        elem* efilename = toEfilename(m);
        if (target.os == Target.OS.Windows && target.isX86_64)
            efilename = addressElem(efilename, Type.tstring, true);

        elem* e = el_params(
                      el_long(TYuchar, global.params.covPercent),
                      ecov,
                      ebcov,
                      efilename,
                      null);
        e = el_bin(OPcall, TYvoid, el_var(getRtlsym(RTLSYM.DCOVER2)), e);
        glue.eictor = el_combine(e, glue.eictor);
        glue.ictorlocalgot = localgot;
    }

    Symbol* msctor, msdtor, mssharedctor, msshareddtor, mstest;
    // If coverage / static constructor / destructor / unittest calls
    if (glue.eictor || glue.sctors.length || glue.ectorgates.length || glue.sdtors.length ||
        glue.ssharedctors.length || glue.esharedctorgates.length || glue.sshareddtors.length || glue.stests.length || glue.sisharedctors.length)
    {
        if (glue.eictor)
        {
            localgot = glue.ictorlocalgot;

            block* b = block_calloc(bo);
            b.bc = BC.ret;
            b.Belem = glue.eictor;
            msictor.Sfunc.Fstartline.Sfilename = m.arg.xarraydup.ptr;
            msictor.Sfunc.Fstartblock = b;
            writefunc(msictor);
        }

        msctor = callFuncsAndGates(m, glue.sctors[], glue.ectorgates[], "__modctor");
        msdtor = callFuncsAndGates(m, glue.sdtors[], null, "__moddtor");
        m.hasCDtor = true;

        if (glue.sisharedctors.length > 0)
        {
            if (msictor)
                glue.sisharedctors.shift(msictor);
            msictor = callFuncsAndGates(m, glue.sisharedctors[], null, "__modsharedictor");
        }

        mssharedctor = callFuncsAndGates(m, glue.ssharedctors[], cast(StaticDtorDeclaration[])glue.esharedctorgates[], "__modsharedctor");
        msshareddtor = callFuncsAndGates(m, glue.sshareddtors[], null, "__modshareddtor");
        mstest = callFuncsAndGates(m, glue.stests[], null, "__modtest");

        if (doppelganger)
            genModuleInfo(m, msictor, msctor, msdtor, mssharedctor, msshareddtor, mstest);
    }

    if (doppelganger)
    {
        objc.generateModuleInfo(m);
        objmod.termfile();
        return;
    }

     /* Generate module info for templates and -cov.
     *  Don't generate ModuleInfo if `object.ModuleInfo` is not declared or
     *  explicitly disabled through compiler switches such as `-betterC`.
     *  Don't generate ModuleInfo for C files unless coverage testing,
     *  although a D main needs to be present in order to pull in the druntime
     *  code to actually generate the coverage report.
     */
    if (global.params.useModuleInfo && Module.moduleinfo &&
        (global.params.cov || m.filetype != FileType.c) /*|| needModuleInfo()*/)
        genModuleInfo(m, msictor, msctor, msdtor, mssharedctor, msshareddtor, mstest);

    objmod.termfile();
}


// Put out instance of ModuleInfo for this Module

private void genModuleInfo(Module m, Symbol* msictor,
                           Symbol* msctor, Symbol* msdtor,
                           Symbol* mssharedctor, Symbol* msshareddtor,
                           Symbol* mstest)
{
    //printf("Module.genmoduleinfo() %s\n", m.toChars());

    if (!Module.moduleinfo)
    {
        ObjectNotFound(m.loc, Id.ModuleInfo);
    }

    Symbol* msym = toSymbol(m);

    //////////////////////////////////////////////

    auto csym = cast(Symbol*)m.csym;
    csym.Sclass = SC.global;
    csym.Sfl = FL.data;

    auto dtb = DtBuilder(0);

    ClassDeclarations aclasses;
    getLocalClasses(m, aclasses);

    // importedModules[]
    size_t aimports_dim = m.aimports.length;
    for (size_t i = 0; i < m.aimports.length; i++)
    {
        Module mod = m.aimports[i];
        if (!mod.needmoduleinfo)
            aimports_dim--;
    }

    FuncDeclaration sgetmembers = m.findGetMembers();

    // These must match the values in druntime/src/object_.d
    enum
    {
        MIstandalone      = 0x4,
        MItlsctor         = 0x8,
        MItlsdtor         = 0x10,
        MIctor            = 0x20,
        MIdtor            = 0x40,
        MIxgetMembers     = 0x80,
        MIictor           = 0x100,
        MIunitTest        = 0x200,
        MIimportedModules = 0x400,
        MIlocalClasses    = 0x800,
        MIname            = 0x1000,
        MIunitTests       = 0x2000,
    }

    uint flags = 0;
    if (!m.needmoduleinfo)
        flags |= MIstandalone;
    if (msctor)
        flags |= MItlsctor;
    if (msdtor)
        flags |= MItlsdtor;
    if (mssharedctor)
        flags |= MIctor;
    if (msshareddtor)
        flags |= MIdtor;
    if (sgetmembers)
        flags |= MIxgetMembers;
    if (msictor)
        flags |= MIictor;
    if (mstest)
        flags |= MIunitTest | MIunitTests;
    if (aimports_dim)
        flags |= MIimportedModules;
    if (aclasses.length)
        flags |= MIlocalClasses;
    flags |= MIname;

    dtb.dword(flags);        // _flags
    dtb.dword(0);            // _index

    if (flags & MItlsctor)
        dtb.xoff(msctor, 0, TYnptr);
    if (flags & MItlsdtor)
        dtb.xoff(msdtor, 0, TYnptr);
    if (flags & MIctor)
        dtb.xoff(mssharedctor, 0, TYnptr);
    if (flags & MIdtor)
        dtb.xoff(msshareddtor, 0, TYnptr);
    if (flags & MIxgetMembers)
        dtb.xoff(toSymbol(sgetmembers), 0, TYnptr);
    if (flags & MIictor)
        dtb.xoff(msictor, 0, TYnptr);
    if (flags & MIunitTest)
        dtb.xoff(mstest, 0, TYnptr);
    if (flags & MIimportedModules)
    {
        dtb.size(aimports_dim);
        foreach (i; 0 .. m.aimports.length)
        {
            Module mod = m.aimports[i];

            if (!mod.needmoduleinfo)
                continue;

            Symbol* s = toSymbol(mod);

            /* Weak references don't pull objects in from the library,
             * they resolve to 0 if not pulled in by something else.
             * Don't pull in a module just because it was imported.
             */
            s.Sflags |= SFLweak;
            dtb.xoff(s, 0, TYnptr);
        }
    }
    if (flags & MIlocalClasses)
    {
        dtb.size(aclasses.length);
        foreach (i; 0 .. aclasses.length)
        {
            ClassDeclaration cd = aclasses[i];
            dtb.xoff(toSymbol(cd), 0, TYnptr);
        }
    }
    if (flags & MIname)
    {
        // Put out module name as a 0-terminated string, to save bytes
        m.nameoffset = dtb.length();
        const(char) *name = m.toPrettyChars();
        m.namelen = strlen(name);
        dtb.nbytes(name[0 .. m.namelen + 1]);
        //printf("nameoffset = x%x\n", nameoffset);
    }

    if (flags & MIunitTests)
    {
        // Preserve all existing offsets, including the NUL-terminated name.
        const pointerSize = target.ptrsize;
        dtb.nzeros((pointerSize - dtb.length() % pointerSize) % pointerSize);
        const count = glue.stests.length;
        const arrayOffset = dtb.length() + 2 * pointerSize;
        const recordsOffset = arrayOffset + count * pointerSize;
        // object.UnitTestInfo: size, func, name.length, name.ptr.
        const recordSize = 4 * pointerSize;
        auto nameOffset = recordsOffset + count * recordSize;
        dtb.size(count);
        dtb.xoff(csym, arrayOffset, TYnptr);
        foreach (i; 0 .. count)
            dtb.xoff(csym, recordsOffset + i * recordSize, TYnptr);
        foreach (i, test; glue.stests[])
        {
            const name = glue.testNames[i].toString();
            dtb.size(recordSize);
            dtb.xoff(test, 0, TYnptr);
            dtb.size(name.length);
            dtb.xoff(csym, nameOffset, TYnptr);
            nameOffset += name.length;
        }
        foreach (name; glue.testNames[])
            dtb.nbytes(name.toString());
    }

    objc.generateModuleInfo(m);
    csym.Sdt = dtb.finish();
    out_readonly(csym);
    outdata(csym);

    //////////////////////////////////////////////

    objmod.moduleinfo(msym);
    if (driverParams.exportVisibility == ExpVis.public_)
        objmod.export_symbol(msym, 0);
}


/* ================================================================== */

private UnitTestDeclaration needsDeferredNested(FuncDeclaration fd)
{
    while (fd && fd.isNested())
    {
        FuncDeclaration fdp = fd.toParent2().isFuncDeclaration();
        if (!fdp)
            break;
        if (UnitTestDeclaration udp = fdp.isUnitTestDeclaration())
            return udp.semanticRun < PASS.obj ? udp : null;
        fd = fdp;
    }
    return null;
}

/*******************************************
 * Detect entry points like `main()`.
 * Entry points trigger special handling like referencing the
 * default library, setting up sections, etc.
 *
 * Params:
 *      objmod = object module to write hooks to
 *      fd = function symbol
 * Returns:
 *      true if entry point
 */
private bool entryPointFunctions(Obj objmod, FuncDeclaration fd)
{
    // D main()
    if (fd.isDMain() && onlyOneMain(fd))
    {
        /* Reference the C main() to pull it in to the executable
         */
        static if (0) // superceded by object's import of core.internal.entrypoint : _d_cmain
        final switch (target.objectFormat())
        {
            case Target.ObjectFormat.elf:
            case Target.ObjectFormat.macho:
                objmod.external_def("_main");
                break;
            case Target.ObjectFormat.coff:
                objmod.external_def("main");
                break;
        }
        if (const libname = finalDefaultlibname())
            obj_includelib(libname);
        return true;
    }

    // D runtime library
    if (fd.isRtInit())
    {
        objmod.ehsections();   // initialize exception handling sections
        return true;
    }

    // C main()
    if (fd.isCMain())
    {
        switch (target.objectFormat())
        {
            case Target.ObjectFormat.coff:
                if (driverParams.mscrtlib.length && driverParams.mscrtlib[0])
                    obj_includelib(driverParams.mscrtlib);
                objmod.includelib("OLDNAMES");
                break;

            default:
                break;
        }
        return true;
    }

    // Windows WinMain() or DllMain()
    if (target.os == Target.OS.Windows &&
        (fd.isWinMain() || fd.isDllMain()) &&
        onlyOneMain(fd))
    {
        objmod.includelib("uuid");
        if (driverParams.mscrtlib.length && driverParams.mscrtlib[0])
            obj_includelib(driverParams.mscrtlib);
        objmod.includelib("OLDNAMES");
        if (const libname = finalDefaultlibname())
            obj_includelib(libname);
        return true;
    }

    return false;
}

/* ================================================================== */

/**************************************
 * Generate elem that is a dynamic array slice of the module file name.
 */

private elem* toEfilename(Module m)
{
    //printf("toEfilename(%s)\n", m.toChars());
    const(char)* id = m.srcfile.toChars();
    size_t len = strlen(id);

    Symbol* msfilename;
    if (!m.sfilename)
    {
        // Put out as a static array
        msfilename = toStringSymbol(id, len, 1);
        m.sfilename = msfilename;
    }

    // Turn static array into dynamic array
    return el_pair(TYdarray, el_long(TYsize_t, len), el_ptr(msfilename));
}

/**
 * Find the functions nested in fd that nothing refers to, as every call of them was
 * inlined, and add them to unusedNestedFuncs. Only for a body declaring nothing but
 * variables and functions, so no code outside it can refer to them.
 */
private void findUnusedNested(FuncDeclaration fd)
{
    import dmd.visitor.foreachvar : foreachExpAndVar;
    import dmd.visitor.postorder : walkPostorder;
    import dmd.visitor : StoppableVisitor;
    import dmd.dsymbolsem : toAlias;
    import dmd.inline : hasInlinedCalls;

    // needsClosure() is not asked, as buildClosure() diagnoses what it changes
    if (!fd.fbody || fd.hasInlineAsm)
        return;
    /* Only inlining leaves a nested function nothing refers to that is worth
     * leaving out; without it the scan would cost more than it saves
     */
    if (!hasInlinedCalls(fd))
        return;
    bool simple = true;
    FuncDeclarations declared;
    FuncDeclarations work;
    bool[void*] referred;
    void refer(FuncDeclaration f)
    {
        // each function once, as the template arguments can refer back to it
        if (!f || cast(void*)f in referred)
            return;
        referred[cast(void*)f] = true;
        work.push(f);
        // the functions given to a template instance it is in, which its code refers to
        for (auto ti = f.isInstantiated(); ti; ti = ti.tinst)
        {
            if (!ti.tiargs)
                continue;
            foreach (o; *ti.tiargs)
            {
                auto sym = isDsymbol(o);
                if (!sym)
                    continue;
                if (auto af = sym.toAlias().isFuncDeclaration())
                    refer(af);
                else if (sym.toParent2() == fd)
                    simple = false;
            }
        }
    }

    extern (C++) final class Refs : StoppableVisitor
    {
        alias visit = typeof(super).visit;
        extern (D) void delegate(FuncDeclaration) dgRefer;
        extern (D) void delegate(FuncDeclaration) dgDeclare;
        extern (D) void delegate(Expression) dgInit;
        extern (D) void delegate() dgComplex;
        extern (D) void delegate(Declaration) dgRead;
        extern (D) void delegate(VarDeclaration, FuncDeclaration) dgLiteralVar;
        extern (D) void delegate(VarDeclaration) dgUseVar;
        extern (D) this() scope {}
        override void visit(Expression e) {}
        override void visit(VarExp e)
        {
            dgRefer(e.var.isFuncDeclaration());
            dgRead(e.var);
            if (auto v = e.var.isVarDeclaration())
                dgUseVar(v);
        }
        override void visit(SymOffExp e) { dgRefer(e.var.isFuncDeclaration()); dgRead(e.var); }
        override void visit(ThisExp e) { dgRead(e.var); }
        override void visit(DotVarExp e) { dgRefer(e.var.isFuncDeclaration()); }
        override void visit(DelegateExp e) { dgRefer(e.func); }
        override void visit(FuncExp e) { dgRefer(e.fd); }
        override void visit(CallExp e) { dgRefer(e.f); }
        override void visit(DeclarationExp e)
        {
            if (auto v = e.declaration.isVarDeclaration())
            {
                if (v.toAlias() != v)
                    dgComplex();
                else if (v._init)
                    if (auto ie = v._init.isExpInitializer())
                    {
                        // a variable a function literal is put in, as by inlining a call given
                        // one, refers to it only if the variable is used
                        if (auto f = literalOf(ie.exp))
                            dgLiteralVar(v, f);
                        else
                            dgInit(ie.exp);
                    }
            }
            else if (auto f = e.declaration.isFuncDeclaration())
            {
                // only one using the frame of the function makes variables live in memory
                if (!f.isFuncLiteralDeclaration() && f.isNested())
                    dgDeclare(f);
            }
            else if (!e.declaration.isAliasDeclaration() && !e.declaration.isEnumDeclaration())
                dgComplex();        // aliases and enums have no code that could refer to anything
        }
    }
    scope Refs refs = new Refs();
    bool[void*] usedVars;
    FuncDeclaration[void*] literalVars;
    refs.dgLiteralVar = (VarDeclaration v, FuncDeclaration f) {
        literalVars[cast(void*)v] = f;
        if (cast(void*)v in usedVars)
            refer(f);
    };
    refs.dgUseVar = (VarDeclaration v) {
        usedVars[cast(void*)v] = true;
        if (auto f = cast(void*)v in literalVars)
            refer(*f);
    };
    void walk(Expression e)
    {
        if (e)
            walkPostorder(e, refs);
    }
    refs.dgRefer = &refer;
    refs.dgDeclare = (FuncDeclaration f) { declared.push(f); };
    refs.dgInit = &walk;
    refs.dgComplex = () { simple = false; };
    // the variables the nested functions being scanned use
    FuncDeclaration scanning;   // the nested function being scanned
    bool[void*] reads;
    refs.dgRead = (Declaration d) {
        if (!scanning || !d)
            return;
        if (auto v = d.isVarDeclaration())
            if (v.toParent2() != scanning)
                reads[cast(void*)v] = true;
    };
    void scan(Statement s)
    {
        foreachExpAndVar(s, &walk, (VarDeclaration v) {
            if (v._init)
                if (auto ie = v._init.isExpInitializer())
                    walk(ie.exp);
        });
    }

    scan(fd.fbody);
    // the nested functions given to templates, which their code may call
    foreach (f; declared)
        if (cast(void*)f in templateArgFuncs())
            refer(f);
    // what the functions nested in fd that are referred to refer to
    void drain()
    {
    while (work.length)
    {
        auto f = work.pop();
        bool inside;
        for (Dsymbol p = f.toParent2(); p; p = p.toParent2())
            if (p == fd)
            {
                inside = true;
                break;
            }
        if (f.fbody && inside)
        {
            if (f.hasInlineAsm)
            {
                simple = false;
                return;
            }
            scanning = f;
            scan(f.fbody);
        }
    }
    }
    drain();
    /* a literal put in a variable that is not used is generated all the same, though
     * never called: what it calls is generated too, while what it reads is not read
     */
    foreach (v, f; literalVars)
        if (!(v in usedVars) && f.fbody && !(cast(void*)f in referred))
        {
            if (f.hasInlineAsm)
                return;
            scanning = null;
            scan(f.fbody);
        }
    drain();
    if (!simple)
        return;
    foreach (f; declared)
        if (!(cast(void*)f in referred) && f.toParent2() == fd)
            unusedNestedFuncs[cast(void*)f] = true;
    nestedAnalyzed[cast(void*)fd] = true;
    foreach (v, _; reads)
        nestedReadVars[v] = true;
}

/* The function literal that the initialization init puts in a variable, or null
 */
private FuncDeclaration literalOf(Expression init)
{
    auto ae = init.isConstructExp() ? cast(AssignExp)init : init.isBlitExp() ? cast(AssignExp)init : null;
    if (!ae)
        return null;
    Expression e = ae.e2;
    while (auto ce = e.isCastExp())
        e = ce.e1;
    if (auto fe = e.isFuncExp())
        return fe.fd;
    if (auto de = e.isDelegateExp())
        if (de.func && de.func.isFuncLiteralDeclaration() && de.e1.isVarExp() is null)
            return de.func;
    return null;
}

/* The functions given as arguments to the template instances of the root modules,
 * which the code of the instances may refer to
 */
private bool[void*] templateArgFuncs()
{
    import dmd.dsymbolsem : toAlias;
    __gshared bool[void*] funcs;
    __gshared bool found;
    if (found)
        return funcs;
    found = true;
    void add(Dsymbol s)
    {
        auto ti = s.isTemplateInstance();
        if (!ti)
            return;
        if (ti.tiargs)
            foreach (o; *ti.tiargs)
                if (auto sym = isDsymbol(o))
                    if (auto f = sym.toAlias().isFuncDeclaration())
                        funcs[cast(void*)f] = true;
        if (ti.members)
            foreach (m; *ti.members)
                add(m);
    }
    foreach (m; Module.amodules)
        if (m.isRoot() && m.members)
            foreach (s; *m.members)
                add(s);
    return funcs;
}
