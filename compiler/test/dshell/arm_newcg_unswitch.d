// The program in extra-files/arm_newcg_unswitch runs correctly with and without
// optimization, and optimized by the new AArch64 code generator, without loop
// vectorization, each of its functions named keep_... has no conditional
// branch inside a loop but the loop's own back edge: the test of the
// condition that does not change in the loop is made before it.
module test.dshell.arm_newcg_unswitch;

import dshell;
import std.algorithm : canFind;
import std.conv : to;
import std.file : readText;
import std.regex : matchAll, matchFirst, regex;
import std.stdio : File, writeln;
import std.string : lineSplitter;

int main()
{
    version (AArch64) {} else return DISABLED;

    const src = shellExpand("$EXTRA_FILES/arm_newcg_unswitch/unswitch.d");
    const exe = OUTPUT_BASE ~ "_unswitch" ~ EXE;
    const asmLog = OUTPUT_BASE ~ "_unswitch.asm";
    {
        auto f = File(asmLog, "w");
        run("$DMD -m$MODEL -O -inline -release -vasm -of" ~ exe ~ " " ~ src, f, stderr,
            ["DMD_NEWCG": "1", "DMD_NEWCG_NOLOOPVEC": "1"]);
    }
    run(exe);
    run("$DMD -m$MODEL -O -inline -of" ~ exe ~ " " ~ src, stdout, stderr, ["DMD_NEWCG": "1"]);
    run(exe);
    run("$DMD -m$MODEL -of" ~ exe ~ " " ~ src, stdout, stderr, ["DMD_NEWCG": "1"]);
    run(exe);

    const listing = readText(asmLog);
    int failures;
    string[] seen;
    foreach (m; readText(src).matchAll(regex(`\bkeep_\w+`)))
    {
        const fn = m.hit;
        if (seen.canFind(fn))
            continue;
        seen ~= fn;
        const tag = fn.length.to!string ~ fn;
        bool inFn, found;
        // the conditional branches of the function by address, and the ranges of its loops
        struct Branch { uint addr; bool backEdge; }
        Branch[] branches;
        uint[2][] loops;
        foreach (line; listing.lineSplitter)
        {
            if (line.length && line[$ - 1] == ':' && !line.canFind(' '))
            {
                inFn = line.canFind(tag);
                found |= inFn;
                continue;
            }
            if (!inFn)
                continue;
            auto ins = line.matchFirst(regex(`^([0-9a-f]+):\s+(?:[0-9A-F]{2} ){4}\s*(\S+)\s*(\S*)`));
            if (!ins)
                continue;
            const addr = ins[1].to!uint(16);
            const op = ins[2];
            if (op.length > 2 && op[0 .. 2] == "b." && op != "b.al")
            {
                auto off = ins[3].matchFirst(regex(`#(-?\d+)$`));
                const back = off && off[1].to!int < 0;
                if (back)
                    loops ~= [addr + off[1].to!int * 4, addr];
                branches ~= Branch(addr, back);
            }
            else if (op == "cbz" || op == "cbnz" || op == "tbz" || op == "tbnz")
                branches ~= Branch(addr, false);
        }
        uint inside;
        foreach (br; branches)
            if (!br.backEdge)
                foreach (l; loops)
                    if (br.addr >= l[0] && br.addr < l[1])
                        ++inside;
        if (!found || !loops.length || inside)
        {
            writeln(fn, found ? " has " ~ inside.to!string ~ " conditional branches in " ~ loops.length.to!string ~ " loops" : " not found");
            ++failures;
        }
    }
    return failures ? 1 : 0;
}
