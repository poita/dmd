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
    return 0;
}
