// A template instance with a static constructor that needs no code generated, as it
// was only instantiated speculatively, does not make the workers of a split
// compilation give the split up.
module test.dshell.parallel_speculative_ctor;

import dshell;
import std.algorithm : canFind;

int main()
{
    version (Posix) {} else return DISABLED;

    std.file.mkdirRecurse(Vars.OUTPUT_BASE ~ "/inc");
    std.file.write(Vars.OUTPUT_BASE ~ "/inc/lib.d", q{
        module lib;
        class P(T) { __gshared int n; shared static this() { n = 1; } T v; }
    });
    std.file.write(Vars.OUTPUT_BASE ~ "/a.d", q{
        module a;
        import lib;
        enum ok = __traits(compiles, new P!int);
        int fa() { return ok ? 1 : 0; }
    });
    std.file.write(Vars.OUTPUT_BASE ~ "/b.d", "module b; int fb(int v) { return v * 3; }\n");
    std.file.write(Vars.OUTPUT_BASE ~ "/c.d", "module c; int fc(int v) { return v * 5; }\n");
    const log = Vars.OUTPUT_BASE ~ "/split.log";
    if (std.file.exists(log))
        std.file.remove(log);
    run("$DMD -m$MODEL -j=3 -c -I$OUTPUT_BASE/inc -of=$OUTPUT_BASE/abc$OBJ $OUTPUT_BASE/a.d " ~
        "$OUTPUT_BASE/b.d $OUTPUT_BASE/c.d", stdout, stderr, ["DMD_SPLIT_LOG": log]);
    const result = std.file.readText(log);
    if (!result.canFind("succeeded"))
    {
        writeln(result);
        return 1;
    }
    return 0;
}
