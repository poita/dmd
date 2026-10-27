// An object file compiled with -g keeps its debug information when the compilation
// is split across worker processes: the debug information of every worker's part
// is in the object file, which dsymutil and lldb read without complaint, and the
// backtraces of a program linked from it have the file and line of each function,
// whichever worker generated it. The parts have copies of the same weak definitions
// (a function literal, and in the optimized compilation functions of other modules
// inlined), which the object file and the debug information have once.
module test.dshell.parallel_debuginfo;

import dshell;
import std.algorithm : canFind, count, filter, splitter;
import std.array : array;
import std.format : format;
import std.process : execute;
import std.string : lineSplitter;

enum modules = 4;

string moduleSource(int k)
{
    /* Each module calls the function of the previous one, the first throws. Each
     * part has a copy of the function literal `pick`.
     */
    return format(q{
module m%1$d;
%2$s
T twice%1$d(T)(T x) { return x + x; }
pragma(inline, true) int small%1$d(int x) { return x + %1$d; }
int f%1$d(int x)
{
    if (x >= 1000)
        throw new Exception("too big");
    auto r = %3$s;
    return r + twice%1$d(x) + small%1$d(x) + cast(int) [x, 1, 2].length;
}
%4$s
}, k, k ? format("import m%d; import m0;", k - 1) :
        "struct Q { int v; }\nalias pick = function int(int a, const Q q) { pragma(inline, false); return q.v + a; };",
    k ? format("m%d.f%d(x * 10) + m%d.small%d(x) + g%d(x)", k - 1, k - 1, k - 1, k - 1, k) : "x",
    k ? format("int g%1$d(int x) { return pick(x, Q(x)) + h%1$d(x, Q(2)); }\n" ~
               "int h%1$d(int a, const Q q) { return q.v * a; }", k) : "");
}

int check(string flags, string name)
{
    const dir = Vars.OUTPUT_BASE ~ "/" ~ name;
    mkdirRecurse(dir);
    string files;
    foreach (k; 0 .. modules)
    {
        std.file.write(dir ~ format("/m%d.d", k), moduleSource(k));
        files ~= format(" %s/m%d.d", dir, k);
    }
    std.file.write(dir ~ "/main.d", format(q{
import m%d;
void main() { f%d(1); }
}, modules - 1, modules - 1));

    const obj = dir ~ "/all" ~ Vars.OBJ;
    const exe = dir ~ "/prog" ~ Vars.EXE;
    // the compilation is split, and the parts merged into the object file
    const log = dir ~ "/split.log";
    run("$DMD -m$MODEL -j=" ~ format("%d", modules) ~ " -g " ~ flags ~ " -c -I" ~ dir ~ " -of=" ~ obj ~ files,
        stdout, stderr, ["DMD_SPLIT_LOG": log]);
    const splitLog = std.file.readText(log);
    if (!splitLog.canFind("succeeded") || splitLog.canFind("not done"))
    {
        writeln(name, ": ", splitLog);
        return 1;
    }
    run("$DMD -m$MODEL -g -I" ~ dir ~ " -of=" ~ exe ~ " " ~ dir ~ "/main.d " ~ obj);

    const sections = execute(["otool", "-l", obj]);
    assert(sections.status == 0, sections.output);
    if (!sections.output.canFind("__debug_info") || !sections.output.canFind("__debug_line"))
    {
        writeln(sections.output);
        writeln(name, ": the object file has no debug information");
        return 1;
    }

    // one compilation unit for each module, in the object file
    const units = execute(["dwarfdump", "--debug-info", obj]);
    assert(units.status == 0, units.output);
    foreach (k; 0 .. modules)
        if (!units.output.canFind(format("m%d.d", k)))
        {
            writeln(units.output);
            writefln("%s: no compilation unit for m%d.d", name, k);
            return 1;
        }

    const verify = execute(["dwarfdump", "--verify", obj]);
    if (verify.status != 0)
    {
        writeln(verify.output);
        writeln(name, ": dwarfdump --verify finds errors in the object file");
        return 1;
    }

    // the backtrace of the exception thrown by f0, through the other functions, has
    // the file and line of each of them that is not inlined
    const bt = execute([exe, "x"]);
    foreach (k; 0 .. modules)
        if (!bt.output.canFind(format("m%d.d:", k)) && !flags.canFind("-O"))
        {
            writeln(bt.output);
            writefln("%s: the backtrace has no line of m%d.d", name, k);
            return 1;
        }

    // lldb finds the source line of every function, through the debug map
    string[] lldbArgs = ["lldb", "--batch", "--no-lldbinit", exe];
    foreach (k; 0 .. modules)
        lldbArgs ~= ["-o", format("image lookup -n _D2m%1$d2f%1$dFiZi", k)];
    const lookup = execute(lldbArgs);
    foreach (k; 0 .. modules)
        if (!lookup.output.canFind(format("m%d.d:", k)))
        {
            writeln(lookup.output);
            writefln("%s: lldb finds no source line for m%d.f%d", name, k, k);
            return 1;
        }

    // dsymutil links the debug information without warnings, a subprogram for each
    // function once
    const dsym = execute(["dsymutil", exe, "-o", exe ~ ".dSYM"]);
    if (dsym.status != 0 || dsym.output.length)
    {
        writeln(dsym.output);
        writeln(name, ": dsymutil warns");
        return 1;
    }
    const linked = execute(["dwarfdump", "--debug-info", exe ~ ".dSYM"]);
    assert(linked.status == 0, linked.output);
    foreach (fn; ["m0.f0", "m1.f1", "m2.f2", "m3.f3", "m0.__funcliteral_L4_C1"])
    {
        const n = linked.output.lineSplitter.count!(l => l.canFind(`DW_AT_name	("` ~ fn ~ `")`));
        if (n != 1)
        {
            writeln(linked.output);
            writefln("%s: the dSYM has %d subprograms for %s", name, n, fn);
            return 1;
        }
    }
    const verifyDsym = execute(["dwarfdump", "--verify", exe ~ ".dSYM"]);
    if (verifyDsym.status != 0)
    {
        writeln(verifyDsym.output);
        writeln(name, ": dwarfdump --verify finds errors in the dSYM");
        return 1;
    }
    return 0;
}

int main()
{
    version (OSX) {} else return DISABLED;

    if (auto r = check("", "debug"))
        return r;
    return check("-O -inline", "optimized");
}
