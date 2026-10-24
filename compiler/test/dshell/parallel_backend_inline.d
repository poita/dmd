// The backend inlines a function only into one compiled after it. In a compilation
// split across workers, what is inlined does not depend on which worker compiles
// what: a function calling one of another worker's template instances has it
// inlined as an unsplit compilation would.
module test.dshell.parallel_backend_inline;

import dshell;
import std.algorithm : canFind;
import std.process : execute;

int main()
{
    version (OSX) {} else return DISABLED;
    version (AArch64) {} else return DISABLED;

    std.file.write(Vars.OUTPUT_BASE ~ "/a.d", q{
        module a;
        class E : Exception { this(string m) { super(m); } }
        E make(string m) { return new E(m); }
    });
    std.file.write(Vars.OUTPUT_BASE ~ "/b.d", q{
        module b;
        import a;
        E fresh(string m) { return new E(m); }
    });
    foreach (j; ["1", "2"])
    {
        const obj = Vars.OUTPUT_BASE ~ "/ab" ~ j ~ Vars.OBJ;
        run("$DMD -m$MODEL -O -inline -release -c -j=" ~ j ~ " -of=" ~ obj ~
            " $OUTPUT_BASE/a.d $OUTPUT_BASE/b.d");
        // b.fresh, with core.lifetime._d_newclassT!(a.E), which a.make instantiates, inlined
        const dis = execute(["objdump", "-d", "-r", "--disassemble-symbols=__D1b5freshFAyaZC1a1E", obj]);
        assert(dis.status == 0, dis.output);
        if (!dis.output.canFind("fresh") || dis.output.canFind("_d_newclassT"))
        {
            writeln(dis.output);
            writeln("_d_newclassT!(a.E) is not inlined into b.fresh with -j=" ~ j);
            return 1;
        }
    }
    return 0;
}
