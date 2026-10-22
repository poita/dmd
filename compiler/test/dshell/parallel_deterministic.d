// A compilation split across worker processes writes the same output every time:
// which worker compiles a module, and which generates a template instance function
// several of them need, does not depend on how fast the workers run.
module test.dshell.parallel_deterministic;

import dshell;
import std.format : format;

/* Modules sharing many template instances, of their own templates and of Phobos',
 * which they need in different orders, and which inline across modules
 */
string moduleSource(int k, int count)
{
    string s = format("module m%d;\nimport shared_;\nimport std.algorithm, std.array, std.conv, std.format, std.range;\n", k);
    foreach (j; 0 .. count)
    {
        const t = ["int", "long", "double", "uint", "ubyte", "short"][(j * 7 + k) % 6];
        s ~= format(q{
int f%1$d_%2$d(int n)
{
    auto a = iota(n).map!(i => cast(%3$s) (i * %2$d + %1$d).to!string.length).array;
    Box!(%3$s) b;
    b.put(a.length ? a[0] : %3$s.init);
    a.sort!((x, y) => x > y);
    return cast(int) (format("%%s:%%s", a.length, n).length + twice(n) + b.count + pairUp(n, %2$d).sum);
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

    enum modules = 8;
    std.file.write(Vars.OUTPUT_BASE ~ "/shared_.d", sharedSource);
    string files = "$OUTPUT_BASE/shared_.d";
    foreach (k; 0 .. modules)
    {
        std.file.write(format("%s/m%d.d", Vars.OUTPUT_BASE, k), moduleSource(k, 12));
        files ~= format(" $OUTPUT_BASE/m%d.d", k);
    }

    foreach (output; ["-c -of=$OUTPUT_BASE/all$OBJ", "-lib -of=$OUTPUT_BASE/all$LIBEXT"])
    {
        const file = shellExpand(output[output.indexOf("=") + 1 .. $]);
        foreach (flags; ["-O -inline -release", "-g"])
        {
            ubyte[] first;
            foreach (k; 0 .. 4)
            {
                // the members of a library record SOURCE_DATE_EPOCH rather than the time
                run("$DMD -m$MODEL -j=4 " ~ flags ~ " -I$OUTPUT_BASE " ~ output ~ " " ~ files,
                    stdout, stderr, ["SOURCE_DATE_EPOCH": "0"]);
                auto bytes = cast(ubyte[]) std.file.read(file);
                if (k == 0)
                    first = bytes;
                else if (bytes != first)
                {
                    writefln("compilation %s with '%s %s' differs from the first", k + 1, flags, output);
                    return 1;
                }
            }
        }
    }
    return 0;
}
