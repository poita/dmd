// With -lib, each template instance is written to an object file of its own. A
// zero-initialized variable of one is a common symbol, which the object files of
// the instances written after it refer to as an external symbol.
module test.dshell.lib_common_reference;

import dshell;

int main()
{
    version (Posix) {} else return DISABLED;

    std.file.write(Vars.OUTPUT_BASE ~ "/a.d", q{
        module a;
        template T(U)
        {
            __gshared U[4] x;
        }
        alias X = T!int;
        int f()() { return X.x[1]; }
        void g()(int v) { X.x[1] = v; }
        alias F = f!();
        alias G = g!();
    });
    std.file.write(Vars.OUTPUT_BASE ~ "/main.d", q{
        import a;
        int main() { G(42); return F() == 42 ? 0 : 1; }
    });
    foreach (flags; ["", "-O"])
    {
        run("$DMD -m$MODEL -lib " ~ flags ~ " -of=$OUTPUT_BASE/a$LIBEXT $OUTPUT_BASE/a.d");
        run("$DMD -m$MODEL -I$OUTPUT_BASE -of=$OUTPUT_BASE/main$EXE $OUTPUT_BASE/main.d $OUTPUT_BASE/a$LIBEXT");
        run("$OUTPUT_BASE/main$EXE");
    }
    return 0;
}
