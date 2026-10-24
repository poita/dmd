// A function nested in a template instance function reaches the enclosing
// function's frame at the offsets that function's code generation assigns, so
// one worker of a split compilation generates both.
module test.dshell.parallel_nested_instance;

import dshell;
import std.conv : to;

int main()
{
    version (Posix) {} else return DISABLED;

    // `outer!int` takes long enough to generate that another worker needing
    // `inner!1` reaches it while the worker generating `outer!int` is still busy
    std.file.mkdirRecurse(Vars.OUTPUT_BASE ~ "/inc");
    std.file.write(Vars.OUTPUT_BASE ~ "/inc/tmpl.d", q{
        module tmpl;
        int outer(T)(T x)
        {
            int v = x;
            int pad = x * 3;
            int inner(int k)() { return v * 10 + k + pad; }
            int s = 0;
            static foreach (i; 0 .. 3000)
                s += (x ^ i) * (s >> 2) + i;
            int delegate() d1 = &inner!1, d2 = &inner!2;
            if (x == 12345)
                d1 = d2;
            return d1() + d2() + (s & 0);
        }
    });
    string files, calls;
    foreach (i; 0 .. 8)
    {
        const m = "w" ~ i.to!string;
        std.file.write(Vars.OUTPUT_BASE ~ "/" ~ m ~ ".d",
            "module " ~ m ~ "; import tmpl; int use" ~ i.to!string ~ "() { return outer!int(" ~
            (i + 1).to!string ~ "); }\n");
        files ~= " $OUTPUT_BASE/" ~ m ~ ".d";
        calls ~= "    if (use" ~ i.to!string ~ "() != expect(" ~ (i + 1).to!string ~ ")) return 1;\n";
    }
    std.file.write(Vars.OUTPUT_BASE ~ "/main.d",
        "import w0, w1, w2, w3, w4, w5, w6, w7;\n" ~
        "int expect(int x) { return (x * 10 + 1 + x * 3) + (x * 10 + 2 + x * 3); }\n" ~
        "int main()\n{\n" ~ calls ~ "    return 0;\n}\n");

    foreach (round; 0 .. 3)
    {
        run("$DMD -m$MODEL -j=8 -I$OUTPUT_BASE/inc -of=$OUTPUT_BASE/nested$EXE" ~ files ~
            " $OUTPUT_BASE/main.d");
        run("$OUTPUT_BASE/nested$EXE");
    }
    return 0;
}
