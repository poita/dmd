// A compilation split across worker processes combines only the parts its own
// workers write, and leaves alone files beside the output that another
// compilation left or is writing.
module test.dshell.parallel_stale_parts;

import dshell;
import std.conv : to;
import std.algorithm : canFind, endsWith;
import std.process : execute;

int main()
{
    version (Posix) {} else return DISABLED;

    std.file.write(Vars.OUTPUT_BASE ~ "/stale.d", "module stale; int staleMarker() { return 1; }\n");
    string files;
    foreach (m; ["a", "b", "c", "d"])
    {
        std.file.write(Vars.OUTPUT_BASE ~ "/" ~ m ~ ".d",
            "module " ~ m ~ "; int " ~ m ~ "() { return 1; }\n");
        files ~= " $OUTPUT_BASE/" ~ m ~ ".d";
    }
    run("$DMD -m$MODEL -c -of=$OUTPUT_BASE/stale$OBJ $OUTPUT_BASE/stale.d");
    const stale = std.file.read(Vars.OUTPUT_BASE ~ "/stale" ~ Vars.OBJ);

    foreach (output; [Vars.OUTPUT_BASE ~ "/out" ~ Vars.OBJ, Vars.OUTPUT_BASE ~ "/out" ~ Vars.LIBEXT])
    {
        foreach (k; 0 .. 8)
            std.file.write(output ~ ".part" ~ k.to!string, stale);
        const lib = output.endsWith(Vars.LIBEXT) ? " -lib" : " -c";
        run("$DMD -m$MODEL -j=8" ~ lib ~ " -of=" ~ output ~ files);

        foreach (k; 0 .. 8)
        {
            const part = output ~ ".part" ~ k.to!string;
            if (!std.file.exists(part) || std.file.read(part) != stale)
            {
                writefln("%s, which the compilation did not write, was changed", part);
                return 1;
            }
        }
        const nm = execute(["nm", output]);
        if (nm.status != 0 || nm.output.canFind("staleMarker"))
        {
            writeln(nm.output);
            writefln("%s holds code from a stale part file", output);
            return 1;
        }
    }
    return 0;
}
