// Calls of functions that read and write no memory, cannot throw or fail and
// return are merged when made twice with the same argument; calls of a function
// reading a global are not.
module test.dshell.callcse;

import dshell;
import std.algorithm : count;
import std.process : execute;

int main()
{
    version (OSX) {} else return DISABLED;
    version (AArch64) {} else return DISABLED;

    const obj = Vars.OUTPUT_BASE ~ "/shape" ~ Vars.OBJ;
    run("$DMD -m$MODEL -O -release -c -of=" ~ obj ~ " $EXTRA_FILES/callcse/shape.d");

    int failures;
    void expect(string sym, size_t calls)
    {
        const dis = execute(["objdump", "-d", "--no-show-raw-insn", "--disassemble-symbols=" ~ sym, obj]);
        assert(dis.status == 0, dis.output);
        const n = dis.output.count("\tbl\t");
        if (n != calls)
        {
            writefln("%s: %s calls, expected %s:\n%s", sym, n, calls, dis.output);
            ++failures;
        }
    }
    expect("__D5shape6mergedFfZf", 2);
    expect("__D5shape4libmFfZf", 1);
    expect("__D5shape4keptFfZf", 2);
    return failures != 0;
}
