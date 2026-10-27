// Each program in extra-files/arm_newcg_ifconv runs correctly with and without
// optimization, and when optimized by the new AArch64 code generator, without loop
// vectorization, each of its
// functions named selN_... has at most N conditional branches, the choices
// between values it makes being selects, each named extN_... at most N
// sign or zero extensions, each named divN_... at most N divisions, and each
// named opsN_... at most N instructions but its return.
module test.dshell.arm_newcg_ifconv;

import dshell;
import std.algorithm : canFind, map, startsWith;
import std.array : array;
import std.conv : to;
import std.file : dirEntries, readText, SpanMode;
import std.path : baseName, stripExtension;
import std.regex : matchAll, matchFirst, regex;
import std.stdio : File, writeln;
import std.string : lineSplitter, strip;

int main()
{
    version (AArch64) {} else return DISABLED;

    const dir = shellExpand("$EXTRA_FILES/arm_newcg_ifconv");
    auto srcs = dirEntries(dir, "*.d", SpanMode.shallow).map!(e => e.name).array;
    int failures;
    foreach (src; srcs)
    {
        const name = src.baseName.stripExtension;
        const exe = OUTPUT_BASE ~ "_" ~ name ~ EXE;
        const asmLog = OUTPUT_BASE ~ "_" ~ name ~ ".asm";
        {
            auto f = File(asmLog, "w");
            run("$DMD -m$MODEL -O -inline -release -vasm -of" ~ exe ~ " " ~ src, f, stderr,
                ["DMD_NEWCG": "1", "DMD_NEWCG_NOLOOPVEC": "1"]);
        }
        run(exe);
        run("$DMD -m$MODEL -O -inline -release -of" ~ exe ~ " " ~ src, stdout, stderr, ["DMD_NEWCG": "1"]);
        run(exe);
        run("$DMD -m$MODEL -of" ~ exe ~ " " ~ src, stdout, stderr, ["DMD_NEWCG": "1"]);
        run(exe);

        // the conditional branches of each function, by the name its mangled name ends in
        const listing = readText(asmLog);
        string[] seen;
        foreach (m; readText(src).matchAll(regex(`\b(sel|ext|ops|div)(\d+)_\w+`)))
        {
            const fn = m.hit;
            if (seen.canFind(fn))
                continue;
            seen ~= fn;
            const ext = m[1] == "ext", ops = m[1] == "ops", div = m[1] == "div";
            const limit = m[2].to!uint;
            const tag = fn.length.to!string ~ fn;
            bool inFn, found;
            uint branches;
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
                auto ins = line.matchFirst(regex(`^[0-9a-f]+:\s+(?:[0-9A-F]{2} ){4}\s*(\S+)`));
                if (!ins)
                    continue;
                const op = ins[1];
                if (div ? op == "udiv" || op == "sdiv" : ops ? op != "ret" : ext ? op == "uxtb" || op == "uxth" || op == "sxtb" || op == "sxth" || op == "sxtw" :
                    op.startsWith("b.") && op != "b.al" || op == "cbz" || op == "cbnz" || op == "tbz" || op == "tbnz")
                    ++branches;
            }
            if (!found || branches > limit)
            {
                writeln(name, ": ", fn, found ? " has " ~ branches.to!string ~ (div ? " divisions" : ops ? " instructions" : ext ? " extensions" : " conditional branches") : " not found");
                ++failures;
            }
        }
    }
    return failures ? 1 : 0;
}
