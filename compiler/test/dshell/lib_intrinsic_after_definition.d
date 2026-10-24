// With -lib, each function is written to an object file of its own, after which its
// symbol refers to it as defined elsewhere. A call to an intrinsic function, such as
// core.bitop.bsr, compiled after the function's own object file is written still
// uses the instruction rather than calling the function.
module test.dshell.lib_intrinsic_after_definition;

import dshell;
import std.algorithm : canFind;
import std.process : execute;

int main()
{
    version (OSX) {} else return DISABLED;
    version (AArch64) {} else return DISABLED;

    std.file.mkdirRecurse(Vars.OUTPUT_BASE ~ "/core");
    std.file.write(Vars.OUTPUT_BASE ~ "/core/bitop.d", q{
        module core.bitop;
        int bsr(ulong v) pure nothrow @nogc @safe
        {
            int r = 63;
            while (!(v & (1UL << r)))
                --r;
            return r;
        }
    });
    std.file.write(Vars.OUTPUT_BASE ~ "/user.d", q{
        module user;
        import core.bitop : bsr;
        int highest(ulong v) { return bsr(v); }
    });
    // core.bitop's object file is written before user's
    run("$DMD -m$MODEL -conf= -lib -I$OUTPUT_BASE -of=$OUTPUT_BASE/l$LIBEXT " ~
        "$OUTPUT_BASE/core/bitop.d $OUTPUT_BASE/user.d");
    std.file.mkdirRecurse(Vars.OUTPUT_BASE ~ "/members");
    const ar = execute(["ar", "x", Vars.OUTPUT_BASE ~ "/l" ~ Vars.LIBEXT], null, Config.none, size_t.max,
        Vars.OUTPUT_BASE ~ "/members");
    assert(ar.status == 0, ar.output);
    foreach (member; std.file.dirEntries(Vars.OUTPUT_BASE ~ "/members", "*.o", SpanMode.shallow))
    {
        const dis = execute(["objdump", "-d", "-r", "--disassemble-symbols=__D4user7highestFmZi", member.name]);
        assert(dis.status == 0, dis.output);
        if (!dis.output.canFind("highest"))
            continue;
        if (dis.output.canFind("bsr") || !dis.output.canFind("clz"))
        {
            writeln(dis.output);
            writeln("core.bitop.bsr is called instead of being an instruction");
            return 1;
        }
        return 0;
    }
    writeln("no object file defines user.highest");
    return 1;
}
