// In the determinism stress mode (DMD_SPLIT_STRESS), every process of a split
// compilation sleeps for pseudo-random short times where the processes synchronize;
// whatever the seed, the split succeeds and writes the output it writes without it.
module test.dshell.parallel_stress;

import dshell;
import std.format : format;

/* Modules sharing template instances, which they need in different orders, so
 * that the workers settle in rounds who generates them
 */
string moduleSource(int k, int count)
{
    string s = format("module m%d;\nimport shared_;\nimport std.algorithm, std.array, std.conv, std.range;\n", k);
    foreach (j; 0 .. count)
    {
        const t = ["int", "long", "double", "uint", "ubyte", "short"][(j * 5 + k) % 6];
        s ~= format(q{
int f%1$d_%2$d(int n)
{
    auto a = iota(n).map!(i => cast(%3$s) (i * %2$d + %1$d).to!string.length).array;
    Box!(%3$s) b;
    b.put(a.length ? a[0] : %3$s.init);
    a.sort!((x, y) => x > y);
    return cast(int) (a.length + twice(n) + b.count + pairUp(n, %2$d).sum);
}
}, k, j, t);
    }
    return s;
}

enum sharedSource = q{
module shared_;
struct Box(T) { T[] items; void put(T x) { items ~= x; } size_t count() const { return items.length; } }
int twice(T)(T x) { return cast(int) (x + x); }
int[] pairUp(T)(T a, T b) { return [cast(int) a, cast(int) b, cast(int) (a * b)]; }
};

int main()
{
    version (Posix) {} else return DISABLED;

    enum modules = 6;
    std.file.write(Vars.OUTPUT_BASE ~ "/shared_.d", sharedSource);
    string files = "$OUTPUT_BASE/shared_.d";
    foreach (k; 0 .. modules)
    {
        std.file.write(format("%s/m%d.d", Vars.OUTPUT_BASE, k), moduleSource(k, 6));
        files ~= format(" $OUTPUT_BASE/m%d.d", k);
    }
    const log = Vars.OUTPUT_BASE ~ "/split.log";

    foreach (output; ["-c -of=$OUTPUT_BASE/all$OBJ", "-lib -of=$OUTPUT_BASE/all$LIBEXT"])
    {
        const file = shellExpand(output[output.indexOf("=") + 1 .. $]);
        ubyte[] first;
        foreach (seed; 0 .. 5)
        {
            if (std.file.exists(log))
                std.file.remove(log);
            // the members of a library record SOURCE_DATE_EPOCH rather than the time
            string[string] env = ["SOURCE_DATE_EPOCH": "0", "DMD_SPLIT_LOG": log];
            if (seed)
                env["DMD_SPLIT_STRESS"] = format("%d", seed);
            run("$DMD -m$MODEL -j=4 -O -inline -release -I$OUTPUT_BASE " ~ output ~ " " ~ files,
                stdout, stderr, env);
            const status = std.file.readText(log);
            if (status.indexOf("succeeded") < 0)
            {
                writefln("compilation with '%s' and stress seed %s was not split: %s", output, seed, status);
                return 1;
            }
            auto bytes = cast(ubyte[]) std.file.read(file);
            if (!seed)
                first = bytes;
            else if (bytes != first)
            {
                writefln("compilation with '%s' and stress seed %s differs from the one without", output, seed);
                return 1;
            }
        }
    }
    return 0;
}
