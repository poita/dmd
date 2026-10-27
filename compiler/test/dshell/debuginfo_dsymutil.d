// dsymutil links the debug information of a program without warnings, also when the
// last function of an object file has parameters.
module test.dshell.debuginfo_dsymutil;

import dshell;
import std.process : execute;

int main()
{
    version (OSX) {} else return DISABLED;

    const dir = Vars.OUTPUT_BASE;
    std.file.write(dir ~ "/prog.d", q{
int first(int x) { return x + 1; }
void main() { last(first(1), 2); }
int last(int a, int b) { return a * b; }
});
    const exe = dir ~ "/prog" ~ Vars.EXE;
    run("$DMD -m$MODEL -g -of=" ~ exe ~ " " ~ dir ~ "/prog.d");
    const dsym = execute(["dsymutil", exe, "-o", exe ~ ".dSYM"]);
    if (dsym.status != 0 || dsym.output.length)
    {
        writeln(dsym.output);
        writeln("dsymutil warns");
        return 1;
    }
    return 0;
}
