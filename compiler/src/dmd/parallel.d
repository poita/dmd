/**
 * Split the semantic3, inlining and code generation of the root modules across
 * forked worker processes.
 *
 * After semantic2 the original process forks worker processes, which take the
 * modules one at a time, largest first, and carry on compiling the modules they take.
 * Each worker writes its output (an object file or a library) with a part suffix, and
 * the original process waits for the workers and combines the parts into the requested
 * output. Declarations are fully analyzed before the split, so every worker sees the
 * same symbols; a template instance can end up generated in more than one part, which
 * is harmless as template instances are weak definitions. What a worker finds cannot be
 * inlined is shared with the others, so that a function other workers consider inlining
 * is not analyzed by each of them.
 *
 * Copyright:   Copyright (C) 1999-2026 by The D Language Foundation, All Rights Reserved
 * License:     $(LINK2 https://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 */
module dmd.parallel;

import core.stdc.stdio;
import core.stdc.stdlib;
import core.stdc.string;

import dmd.arraytypes;
import dmd.dmodule;
import dmd.dtemplate : TemplateInstance;
import dmd.globals;
import dmd.root.filename;

version (Posix)
{
    import core.sys.posix.sys.mman : mmap, MAP_ANON, MAP_FAILED, MAP_SHARED, PROT_READ, PROT_WRITE;
    import core.sys.posix.sys.types : pid_t;
    import core.sys.posix.sys.wait : waitpid, WIFEXITED, WEXITSTATUS;
    import core.sys.posix.unistd : dup2, fork, _exit, getpid, sysconf, execvp, _SC_NPROCESSORS_ONLN;
}

/**************************************
 * In a worker, run semantic3 on the modules it takes from those not yet taken by
 * any worker, largest first, so that faster workers take more of them.
 * Params:
 *      w = the split
 *      modules = the root modules; narrowed to those this worker takes
 */
void semantic3Shared(ref Workers w, ref Modules modules) @system
{
    import core.atomic : atomicFetchAdd;
    import dmd.semantic3 : semantic3;

    auto taken = new bool[modules.length];
    while (true)
    {
        const i = atomicFetchAdd(*w.next, 1);
        if (i >= w.order.length)
            break;
        const j = w.order[i];
        taken[j] = true;
        modules[j].semantic3(null);
    }
    size_t k = 0;
    foreach (j; 0 .. modules.length)
    {
        if (taken[j])
            modules[k++] = modules[j];
        else
        {
            w.others ~= modules[j];
            w.seen ~= w.membersAtSplit[j];
        }
    }
    modules.setDim(k);
}

/**************************************
 * A template instance is added to the module declaring its template, which may be
 * one another worker compiles. Instances in the other workers' modules that this
 * worker has added since the split, or that were added before it and have completed
 * semantic analysis, are semantically analyzed here and added to this worker's first
 * module, so that it generates their code if it needs them. Which worker generates
 * the code of a template instance function is settled by `claimFunction`.
 * Params:
 *      w = the split
 *      modules = this worker's root modules
 */
void adoptForeignInstances(ref Workers w, ref Modules modules) @system
{
    import dmd.dsymbol : PASS;

    if (w.index < 0 || !modules.length)
        return;

    TemplateInstance[] adopted;
    foreach (k, m; w.others)
    {
        if (!m.members)
            continue;
        foreach (s; (*m.members)[0 .. w.seen[k]])
        {
            if (auto ti = s.isTemplateInstance())
                if (ti.semanticRun >= PASS.semantic3)
                    adopted ~= ti;
        }
    }
    adoptAdded(w, adopted);
    bool[void*] added;     // by identity, as frontend classes are extern(C++)
    foreach (ti; adopted)
    {
        if (cast(void*) ti in added)
            continue;
        added[cast(void*) ti] = true;
        modules[0].members.push(ti);
    }
    adopting = &w;
}

/**************************************
 * Code generation can instantiate templates too, adding the instances to the
 * modules other workers compile; this worker adopts those it has added since
 * `adoptForeignInstances` (or the last call), to generate their code itself.
 * Returns:
 *      the instances adopted, semantically analyzed; none if the compilation is not split
 */
TemplateInstance[] adoptLateInstances() @system
{
    TemplateInstance[] adopted;
    if (adopting)
        adoptAdded(*adopting, adopted);
    return adopted;
}

/* Returns: true if `ti` is a member of one of this worker's own root modules, which
 * it generates the code of as it does theirs
 */
private bool isOwnMember(ref Workers w, TemplateInstance ti)
{
    foreach (m; w.others)
        if (ti.memberOf is m)
            return false;
    return true;
}

/// The split this worker adopts instances from, once its modules have been analyzed
private __gshared Workers* adopting;

/**************************************
 * Returns: true if `m` is a root module another worker of the split compilation
 * generates the code of, after this worker's modules have been analyzed
 */
bool compiledElsewhere(const Module m) @system
{
    if (!adopting || !m)
        return false;
    foreach (o; adopting.others)
        if (o is m)
            return true;
    return false;
}

/* Semantically analyze the template instances added to the other workers' modules
 * since they were last looked at, and those of them that were speculative at the
 * split but that this worker has since needed, and append them to `adopted`.
 */
private void adoptAdded(ref Workers w, ref TemplateInstance[] adopted) @system
{
    import dmd.dsymbol : Dsymbol, PASS;
    import dmd.dsymbolsem : runDeferredSemantic3;
    import dmd.semantic3 : semantic3;

    bool again = true;
    while (again)
    {
        again = false;
        /* An instance that was speculative at the split stays in the module it
         * was added to; needing it does not add it to this worker's modules
         */
        size_t still = 0;
        foreach (ti; w.speculativeAtSplit)
        {
            if (!ti.minst)
                w.speculativeAtSplit[still++] = ti;
            else if (!isOwnMember(w, ti))
            {
                if (ti.semanticRun < PASS.semantic3)
                    semantic3(ti, null);
                adopted ~= ti;
                again = true;
            }
        }
        w.speculativeAtSplit = w.speculativeAtSplit[0 .. still];
        foreach (k, m; w.others)
        {
            while (m.members && w.seen[k] < m.members.length)
            {
                Dsymbol s = (*m.members)[w.seen[k]++];
                if (auto ti = s.isTemplateInstance())
                {
                    semantic3(ti, null);
                    adopted ~= ti;
                    again = true;
                }
            }
        }
        runDeferredSemantic3();
    }
}

nothrow:

/// The state of a compilation split across worker processes
struct Workers
{
    int index = -1;         /// in a worker, its number; -1 in the original process
    int count;              /// number of workers started, 0 if the compilation is not split
    bool succeeded;         /// in the original process: every worker wrote its output part
    shared(size_t)* next;   /// the position in `order` of the next module to take, shared by the workers
    size_t[] order;         /// indices of the root modules, largest first
    size_t[] membersAtSplit;/// the number of members of each root module when the split happened
    Module[] others;        /// in a worker: the root modules other workers take
    size_t[] seen;          /// how many members of each of `others` have been looked at
    /// the template instances of the root modules that were speculative when the
    /// split happened, until this worker adopts them
    TemplateInstance[] speculativeAtSplit;

    /// Returns: true if this is a forked worker
    bool isChild() const nothrow { return index >= 0; }
}

/// the process id of the original process of the split, which names the files it
/// and its workers write beside the output, so that no other compilation writing
/// the same output reads or replaces them
private __gshared int splitOwner;

/// Returns: the suffix added to the output file names of worker `index`
const(char)[] partSuffix(int index)
{
    char[32] buf = void;
    const n = snprintf(buf.ptr, buf.length, ".%d.part%d", splitOwner, index);
    return buf[0 .. n].idup;
}

/// Returns: the name of the temporary file the original process of the split writes
/// `file` to before renaming it to `file`
const(char)[] mergeTemporary(const(char)[] file)
{
    char[32] buf = void;
    const n = snprintf(buf.ptr, buf.length, ".%d.tmp", splitOwner);
    return file ~ buf[0 .. n];
}

version (Posix)
{
    /* Mangled names, each with a value, in memory shared by the workers
     */
    private struct NameTable
    {
        enum slotCount = 1 << 20;                   // a power of 2
        enum arenaSize = 64 << 20;
        shared(uint)[slotCount] slots;  // offset + 1 in `arena` of a name, 0 if free
        shared(uint) used;              // bytes of `arena` in use
        ubyte[arenaSize] arena;         // each name as its length and its value, uints, then its characters
    }
    /// in a worker: the template instance functions each worker generates, by the worker
    private __gshared NameTable* claims;
    /// in a worker: the functions found not to be inlinable, with a bit set for each
    /// way they were found not to be inlinable (see `inlineVerdictBit`)
    private __gshared NameTable* verdicts;
    private __gshared uint workerIndex;     // in a worker: its number

    /* In a worker: where it reports its results to the original process, and how
     * many library files were listed when it started
     */
    private __gshared FILE* resultFile;
    private __gshared size_t libfilesAtSplit;
}

/**************************************
 * Split the root modules across worker processes.
 *
 * The original process forks the workers and waits for them. A worker's output
 * goes to a temporary file: a worker that prints anything (errors, warnings,
 * deprecations, messages) or fails makes the split unsuccessful, and the original
 * process, still in its state from before the split, then compiles all the modules
 * itself, so that diagnostics are exactly those of an unsplit compilation.
 * Params:
 *      modules = the root modules
 *      requested = number of workers asked for, 0 for one per processor, or fewer for
 *                  a small compilation
 * Returns:
 *      the split
 */
Workers split(ref Modules modules, uint requested)
{
    Workers w;
    version (Posix)
    {
        size_t n = requested;
        if (!n)
        {
            /* Starting a worker costs more than compiling a little source, so by
             * default there is one worker for each `sourcePerWorker` bytes of source
             */
            enum sourcePerWorker = 128 * 1024;
            size_t total;
            foreach (m; modules)
                total += m.src.length;
            n = cast(size_t)sysconf(_SC_NPROCESSORS_ONLN);
            if (n > total / sourcePerWorker)
                n = total / sourcePerWorker;
        }
        if (n > modules.length)
            n = modules.length;
        if (n < 2)
            return w;

        /* Workers take the largest modules first
         */
        auto order = new size_t[modules.length];
        foreach (i, ref o; order)
            o = i;
        static size_t weight(Module m) { return m.src.length + 1; }
        __gshared Module[] sortModules;
        sortModules = modules[];
        extern (C) static int cmp(const void* a, const void* b)
        {
            const wa = weight(sortModules[*cast(size_t*)a]);
            const wb = weight(sortModules[*cast(size_t*)b]);
            return wa < wb ? 1 : wa > wb ? -1 : 0;
        }
        qsort(order.ptr, order.length, size_t.sizeof, &cmp);

        void* next = mmap(null, size_t.sizeof, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANON, -1, 0);
        if (next == MAP_FAILED)
            return w;
        w.next = cast(shared(size_t)*)next;
        splitOwner = getpid();
        void* c = mmap(null, NameTable.sizeof, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANON, -1, 0);
        if (c != MAP_FAILED)
            claims = cast(NameTable*)c;
        if (global.params.useInline)
        {
            void* v = mmap(null, NameTable.sizeof, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANON, -1, 0);
            if (v != MAP_FAILED)
                verdicts = cast(NameTable*)v;
        }
        w.order = order;
        foreach (m; modules)
        {
            w.membersAtSplit ~= m.members ? m.members.length : 0;
            if (m.members)
                foreach (s; *m.members)
                    if (auto ti = s.isTemplateInstance())
                        if (!ti.minst)
                            w.speculativeAtSplit ~= ti;
        }

        fflush(stdout);
        fflush(stderr);
        libfilesAtSplit = global.params.libfiles.length;
        pid_t[] children;
        FILE*[] outputs;
        FILE*[] results;
        foreach (k; 0 .. n)
        {
            FILE* output = tmpfile();
            FILE* result = tmpfile();
            if (!output || !result)
                break;
            const pid = fork();
            if (pid == -1)
                break;
            if (pid == 0)
            {
                dup2(fileno(output), 1);
                dup2(fileno(output), 2);
                resultFile = result;
                workerIndex = cast(uint)k;
                w.index = cast(int)k;
                break;
            }
            children ~= pid;
            outputs ~= output;
            results ~= result;
        }

        if (w.isChild)
        {
            w.count = cast(int)n;
            return w;
        }

        claims = null;              // the original process generates all it compiles
        verdicts = null;            // and analyzes all it inlines
        w.count = cast(int)children.length;
        w.succeeded = children.length == n;
        foreach (k, pid; children)
        {
            int status;
            if (waitpid(pid, &status, 0) == -1 || !WIFEXITED(status) || WEXITSTATUS(status) != 0 ||
                fseek(outputs[k], 0, SEEK_END) != 0 || ftell(outputs[k]) != 0)
                w.succeeded = false;
            fclose(outputs[k]);
        }
        if (w.succeeded)
        {
            foreach (result; results)
                readResult(result);
        }
        foreach (result; results)
            fclose(result);
    }
    return w;
}

/**************************************
 * Settle which worker generates the code of a template instance function, which
 * any worker needing it could.
 * Params:
 *      name = the function's mangled name
 *      claim = claim the function for this worker if no worker has
 * Returns:
 *      true if this worker is to generate the function: the compilation is not split,
 *      this worker has claimed it, or no worker had and `claim` is set
 */
bool claimFunction(const(char)[] name, bool claim)
{
    version (Posix)
    {
        import core.atomic : atomicLoad;

        if (!claims)
            return true;
        auto claimer = lookUp(claims, name, workerIndex, claim);
        return !claimer || atomicLoad(*claimer) == workerIndex;
    }
    else
        return true;
}

/// Returns: true if this is a worker sharing with the others what it finds cannot be inlined
bool sharingInlineVerdicts()
{
    version (Posix)
        return verdicts !is null;
    else
        return false;
}

/// Returns: the bit `noteNotInlinable` and `foundNotInlinable` keep for one way of
/// inlining a function
uint inlineVerdictBit(bool hasThis, bool statementsToo)
{
    return 1u << (hasThis * 2 + statementsToo);
}

/**************************************
 * In a worker: record for the other workers that a function this worker has analyzed
 * cannot be inlined in one way, so that they need not analyze it to find that out.
 * Params:
 *      name = the function's mangled name
 *      bit = the way it cannot be inlined, from `inlineVerdictBit`
 */
void noteNotInlinable(const(char)[] name, uint bit)
{
    version (Posix)
    {
        import core.atomic : atomicOp;

        if (!verdicts)
            return;
        if (auto bits = lookUp(verdicts, name, 0, true))
            atomicOp!"|="(*bits, bit);
    }
}

/// Returns: true if in a worker, a worker has recorded with `noteNotInlinable` that the
/// function mangled as `name` cannot be inlined in the way `bit` stands for
bool foundNotInlinable(const(char)[] name, uint bit)
{
    version (Posix)
    {
        import core.atomic : atomicLoad;

        if (!verdicts)
            return false;
        auto bits = lookUp(verdicts, name, 0, false);
        return bits && (atomicLoad(*bits) & bit) != 0;
    }
    else
        return false;
}

version (Posix)
{
    /* Find `name` in `table`, adding it with `value` if it is not there and `add` is set.
     * Returns: the name's value, null if the name is not there and not added, or the
     * table is out of space
     */
    private shared(uint)* lookUp(NameTable* table, const(char)[] name, uint value, bool add)
    {
        import core.atomic : atomicFetchAdd, atomicLoad, cas;

        ulong h = 14695981039346656037UL;          // FNV-1a
        foreach (c; name)
        {
            h ^= c;
            h *= 1099511628211UL;
        }
        uint mine;
        foreach (probe; 0 .. NameTable.slotCount)
        {
            shared(uint)* slot = &table.slots[(h + probe) & (NameTable.slotCount - 1)];
            uint v = atomicLoad(*slot);
            if (v == 0)
            {
                if (!add)
                    return null;
                if (!mine)
                {
                    const need = cast(uint)((2 * uint.sizeof + name.length + 3) & ~3);
                    const offset = atomicFetchAdd(table.used, need);
                    if (offset + need > NameTable.arenaSize)
                        return null;
                    auto header = cast(uint*)(table.arena.ptr + offset);
                    header[0] = cast(uint)name.length;
                    header[1] = value;
                    memcpy(table.arena.ptr + offset + 2 * uint.sizeof, name.ptr, name.length);
                    mine = offset + 1;
                }
                if (cas(slot, 0u, mine))
                    return cast(shared(uint)*)(table.arena.ptr + mine - 1 + uint.sizeof);
                v = atomicLoad(*slot);
            }
            auto header = cast(uint*)(table.arena.ptr + v - 1);
            if (header[0] == name.length && memcmp(header + 2, name.ptr, name.length) == 0)
                return cast(shared(uint)*)(header + 1);
        }
        return null;
    }
}

/**************************************
 * End a worker once its output part is written, reporting to the original process
 * the library files it added to the link.
 */
void exitWorker(bool ok)
{
    version (Posix)
    {
        foreach (name; global.params.libfiles[libfilesAtSplit .. $])
            fwrite(name, 1, strlen(name) + 1, resultFile);
        if (fflush(resultFile) != 0)
            ok = false;
    }
    // exit() rather than _exit(), so that an instrumented compiler writes its profile
    exit(ok ? 0 : 1);
}

/* Add the library files a worker reported to the link.
 */
version (Posix)
private void readResult(FILE* result)
{
    fseek(result, 0, SEEK_END);
    const size = ftell(result);
    if (size <= 0)
        return;
    auto buf = cast(char*)malloc(size);
    rewind(result);
    if (fread(buf, 1, size, result) != size)
        return;
    for (size_t i = 0; i < size; i += strlen(buf + i) + 1)
        global.params.libfiles.push(buf + i);
}

/// Returns: the names of the output parts written by `count` workers writing `file`;
/// a worker that took no modules writes none
const(char)[][] partNames(const(char)[] file, int count)
{
    const(char)[][] parts;
    foreach (k; 0 .. count)
    {
        const p = file ~ partSuffix(k);
        if (FileName.exists(p) == 1)
            parts ~= p;
    }
    return parts;
}

/// Delete output parts
void removeParts(const(char)[][] parts)
{
    foreach (p; parts)
        remove(toCString(p));
}

/**************************************
 * Combine object file parts into one object file with `ld -r`.
 * Params:
 *      objfile = the object file to write
 *      parts = the object files to combine
 * Returns:
 *      true on success
 */
bool mergeObjects(const(char)[] objfile, const(char)[][] parts)
{
    version (Posix)
    {
        const(char)*[] argv;
        argv ~= "ld";
        argv ~= "-r";
        const tmpfile = mergeTemporary(objfile);
        argv ~= "-o";
        argv ~= toCString(tmpfile);
        foreach (p; parts)
            argv ~= toCString(p);
        argv ~= null;

        fflush(stdout);
        fflush(stderr);
        const pid = fork();
        if (pid == -1)
            return false;
        if (pid == 0)
        {
            execvp(argv[0], argv.ptr);
            _exit(127);
        }
        int status;
        if (waitpid(pid, &status, 0) == -1 || !WIFEXITED(status) || WEXITSTATUS(status) != 0)
        {
            remove(toCString(tmpfile));
            return false;
        }
        return rename(toCString(tmpfile), toCString(objfile)) == 0;
    }
    else
        return false;
}

private const(char)* toCString(const(char)[] s)
{
    auto p = cast(char*)malloc(s.length + 1);
    memcpy(p, s.ptr, s.length);
    p[s.length] = 0;
    return p;
}

