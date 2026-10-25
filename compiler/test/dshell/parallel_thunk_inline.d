// Generating the thunk of a method implementing an interface's left the method
// unfit for the backend inliner, so whether a call to it compiled after the thunk
// was inlined depended on whether the compiler process had generated the thunk:
// here a split compilation's worker had not, and inlined it, where an unsplit
// compilation called it.
module test.dshell.parallel_thunk_inline;

import dshell;
import std.algorithm : canFind;
import std.process : execute;

int main()
{
    version (OSX) {} else return DISABLED;
    version (AArch64) {} else return DISABLED;

    std.file.write(Vars.OUTPUT_BASE ~ "/a.d", q{
        module a;
        interface I { int m() const @safe; }
        final class C : I
        {
            int x;
            int m() const @safe { return x; }
        }
        class D { int v; this(int v) @safe { this.v = v; } }
    });
    std.file.write(Vars.OUTPUT_BASE ~ "/b.d", q{
        module b;
        import a;
        D f(C c) @safe { return new D(c.m() == 3); }
    });
    std.file.write(Vars.OUTPUT_BASE ~ "/c.d", "module c; int g(int v) { return v * 3; }\n");
    foreach (j; ["1", "2"])
    {
        const obj = Vars.OUTPUT_BASE ~ "/abc" ~ j ~ Vars.OBJ;
        run("$DMD -m$MODEL -O -inline -release -c -j=" ~ j ~ " -of=" ~ obj ~
            " $OUTPUT_BASE/a.d $OUTPUT_BASE/b.d $OUTPUT_BASE/c.d");
        const dis = execute(["objdump", "-d", "-r", "--disassemble-symbols=__D1b1fFNfC1a1CZCQg1D", obj]);
        assert(dis.status == 0 && dis.output.canFind("<__D1b1f"), dis.output);
        if (dis.output.canFind("BRANCH26\t__D1a1C1mMxFNfZi"))
        {
            writeln(dis.output);
            writeln("a.C.m is called rather than inlined into b.f with -j=" ~ j);
            return 1;
        }
    }
    return 0;
}
