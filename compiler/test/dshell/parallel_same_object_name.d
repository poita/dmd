// Root modules whose object files have the same name, without -op, write them one
// after the other, the last one staying, also when the compilation is split across
// worker processes, which then write them in the same order.
module test.dshell.parallel_same_object_name;

import dshell;
import std.algorithm : canFind;
import std.format : format;
import std.process : execute;

int main()
{
    version (Posix) {} else return DISABLED;

    string files;
    foreach (k; 0 .. 6)
    {
        const dir = format("%s/p%d", Vars.OUTPUT_BASE, k);
        std.file.mkdirRecurse(dir);
        // a large module, so that the others are dealt out to other workers
        string body = format("module p%d.x; int f%d(int v) { return v + %d; }\n", k, k, k);
        if (k == 0)
            foreach (i; 0 .. 400)
                body ~= format("int g%d(int v) { return v * %d + %d; }\n", i, i, i);
        std.file.write(dir ~ "/x.d", body);
        files ~= format(" $OUTPUT_BASE/p%d/x.d", k);
    }
    // modules with object files of their own names, so that the compilation is split
    foreach (k; 0 .. 3)
    {
        std.file.write(format("%s/y%d.d", Vars.OUTPUT_BASE, k), format("module y%d; int h() { return %d; }\n", k, k));
        files ~= format(" $OUTPUT_BASE/y%d.d", k);
    }
    const log = Vars.OUTPUT_BASE ~ "/split.log";
    foreach (round; 0 .. 4)
    {
        if (std.file.exists(log))
            std.file.remove(log);
        run("$DMD -m$MODEL -j=4 -c -od=$OUTPUT_BASE/out" ~ files, stdout, stderr, ["DMD_SPLIT_LOG": log]);
        if (!std.file.readText(log).canFind("succeeded"))
        {
            writeln(std.file.readText(log));
            return 1;
        }
        // the object file of the last module stays
        const nm = execute(["nm", Vars.OUTPUT_BASE ~ "/out/x" ~ Vars.OBJ]);
        assert(nm.status == 0, nm.output);
        if (!nm.output.canFind("f5") || nm.output.canFind("f0") || nm.output.canFind("f3"))
        {
            writeln(nm.output);
            writefln("compilation %s left the object file of another module than the last", round + 1);
            return 1;
        }
    }
    return 0;
}
