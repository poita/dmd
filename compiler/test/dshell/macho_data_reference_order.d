// A reference to data visible outside the object file goes through the GOT whether
// the data is defined before or after the function referring to it, so that the code
// of a function does not depend on the order the symbols are written in.
module test.dshell.macho_data_reference_order;

import dshell;
import std.algorithm : canFind, count, filter, splitter;
import std.process : execute;

int main()
{
    version (OSX) {} else return DISABLED;
    version (AArch64) {} else return DISABLED;

    std.file.write(Vars.OUTPUT_BASE ~ "/a.d", q{
        module a;
        int* before() { return &x; }
        __gshared int x = 3;
        int* after() { return &x; }
    });
    run("$DMD -m$MODEL -conf= -c -of=$OUTPUT_BASE/a$OBJ $OUTPUT_BASE/a.d");
    const r = execute(["otool", "-rv", Vars.OUTPUT_BASE ~ "/a" ~ Vars.OBJ]);
    assert(r.status == 0, r.output);
    // _D1a1xi, referred to by before() and after(), a page and a page offset each
    auto lines = r.output.splitter('\n').filter!(l => l.canFind("__D1a1xi"));
    const got = lines.save.count!(l => l.canFind("GOTLDP"));
    const all = lines.count;
    if (all != 4 || got != 4)
    {
        writeln(r.output);
        writefln("%s of the %s references to x go through the GOT", got, all);
        return 1;
    }

    /* With -lib, a template instance's zero-initialized variable is a common symbol
     * of the instance's object file, an external one of the object files written
     * after it
     */
    std.file.write(Vars.OUTPUT_BASE ~ "/s.d", q{
        module s;
        template Reg(T)
        {
            __gshared int count;
            shared static this() { ++count; }
        }
    });
    string files = " $OUTPUT_BASE/s.d";
    foreach (m; ["m0", "m1", "m2"])
    {
        std.file.write(Vars.OUTPUT_BASE ~ "/" ~ m ~ ".d",
            "module " ~ m ~ ";\nimport s;\nint use_" ~ m ~ "() { return Reg!int.count; }\n");
        files ~= " $OUTPUT_BASE/" ~ m ~ ".d";
    }
    run("$DMD -m$MODEL -conf= -O -lib -I$OUTPUT_BASE -of=$OUTPUT_BASE/b$LIBEXT" ~ files);
    const rl = execute(["otool", "-rv", Vars.OUTPUT_BASE ~ "/b" ~ Vars.LIBEXT]);
    assert(rl.status == 0, rl.output);
    auto refs = rl.output.splitter('\n').filter!(l => l.canFind("__D1s__T3RegTiZ5counti"));
    const gotRefs = refs.save.count!(l => l.canFind("GOTLDP"));
    const allRefs = refs.count;
    if (allRefs != 8 || gotRefs != 8)
    {
        writeln(rl.output);
        writefln("%s of the %s references to Reg!int.count go through the GOT", gotRefs, allRefs);
        return 1;
    }
    return 0;
}
