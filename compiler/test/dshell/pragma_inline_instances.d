// pragma(inline, true) functions are inlined into the functions of template
// instances calling them, however deeply the instances nest, without -inline too.
module test.dshell.pragma_inline_instances;

import dshell;

enum source = q{
module m;
pragma(inline, true) int twice(int x) { return x + x; }

struct Outer(T)
{
    struct Inner(U)
    {
        U u;
        int get() { return twice(cast(int) u); }
    }
    mixin template Mixed() { int mixed(int y) { return twice(y) + 1; } }
    mixin Mixed;
    int run(T t) { Inner!T i = Inner!T(t); return i.get() + mixed(2); }
}

int plain(int x) { return x; }

int main()
{
    Outer!long o;
    return o.run(3) == 11 ? 0 : 1;
}
};

int main()
{
    std.file.write(Vars.OUTPUT_BASE ~ "/m.d", source);
    auto log = File(Vars.OUTPUT_BASE ~ "/log.txt", "w");
    run("$DMD -m$MODEL -v -o- $OUTPUT_BASE/m.d", log);
    log.close();
    const output = std.file.readText(Vars.OUTPUT_BASE ~ "/log.txt");
    foreach (caller; ["m.Outer!long.Inner!long.get", "m.Outer!long.Mixed!().mixed"])
    {
        if (output.indexOf("inlined   m.twice =>\n          " ~ caller) < 0)
        {
            writefln("m.twice is not inlined into %s:\n%s", caller, output);
            return 1;
        }
    }
    return 0;
}
