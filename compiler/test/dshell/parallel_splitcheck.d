// A compilation split across worker processes generates the same code and data as an
// unsplit one, function by function and symbol by symbol, as tools/splitcheck.py
// checks: for modules sharing template instances, with functions nested in template
// instance functions (templates and not), closures, static constructors of template
// instances and thread local variables. The program each writes also runs the same.
module test.dshell.parallel_splitcheck;

import dshell;
import std.format : format;
import std.path : buildPath, dirName;

enum modules = 6;

enum sharedSource = q{
module shared_;

struct Box(T)
{
    T[] items;
    void put(T x) { items ~= x; }
    T total() const
    {
        T s = 0;
        foreach (x; items)
            s += x;
        return s;
    }
}

T twice(T)(T x) { return cast(T) (x + x); }

int outer(T)(T x)
{
    int v = cast(int) x;
    int inner(int k)() { return v * 10 + k; }       // a template nested in an instance function
    int plain() { return v + 1; }                   // a function nested in an instance function
    int delegate() d = &inner!1;                    // a closure over the instance function's frame
    return d() + inner!2() + plain();
}

template Reg(T)
{
    __gshared int count;
    shared static this() { ++count; }               // a static constructor of an instance
}

int tlsBump(T)()
{
    static T t;                                     // thread local, of an instance function
    ++t;
    return cast(int) t;
}

int tlsCounter;                                     // thread local, of a module
};

string moduleSource(int k)
{
    return format(q{
module m%1$d;
import shared_;

struct S%1$d { int v; }

int closure%1$d(int n)
{
    int acc = %1$d;
    auto dg = (int x) => acc += x;
    foreach (i; 0 .. n)
        dg(i);
    return acc;
}

int nestedPlain%1$d(int n)
{
    int base = n * 2;
    int helper(int m) { return base + m; }
    return helper(%1$d);
}

int use%1$d(int n)
{
    Box!int b;
    b.put(n);
    b.put(%1$d);
    int r = outer!long(n) + outer!int(n + %1$d) + twice(n) + b.total;
    r += Reg!(S%1$d).count + Reg!int.count;
    r += tlsBump!int() + tlsBump!short();
    tlsCounter += 1;
    return r + closure%1$d(3) + nestedPlain%1$d(n);
}
}, k);
}

int main()
{
    version (Posix) {} else return DISABLED;

    const checker = buildPath(__FILE_FULL_PATH__.dirName.dirName, "tools", "splitcheck.py");
    string files = "$OUTPUT_BASE/shared_.d";
    string imports, calls;
    std.file.write(Vars.OUTPUT_BASE ~ "/shared_.d", sharedSource);
    foreach (k; 0 .. modules)
    {
        std.file.write(format("%s/m%d.d", Vars.OUTPUT_BASE, k), moduleSource(k));
        files ~= format(" $OUTPUT_BASE/m%d.d", k);
        imports ~= format("import m%d;\n", k);
        calls ~= format("    writeln(use%d(%d));\n", k, k + 3);
    }
    std.file.write(Vars.OUTPUT_BASE ~ "/main.d", imports ~ "import shared_, std.stdio;\nvoid main()\n{\n" ~
        calls ~ "    writeln(tlsCounter);\n}\n");

    foreach (flags; ["-O -inline -release", ""])
    {
        foreach (output; ["-c -of=$OUTPUT_BASE/all$OBJ", "-lib -of=$OUTPUT_BASE/all$LIBEXT"])
        {
            run("python3 " ~ checker ~ " -j 2,3,4 -r 2 --require-split -- $DMD -m$MODEL " ~ flags ~
                " -I$OUTPUT_BASE " ~ output ~ " " ~ files);

            // the program runs the same with the code of either
            string[2] results;
            foreach (i, j; ["1", "3"])
            {
                const exe = "$OUTPUT_BASE/main" ~ j ~ "$EXE";
                run("$DMD -m$MODEL -j=" ~ j ~ " " ~ flags ~ " -I$OUTPUT_BASE " ~ output ~ " " ~ files);
                run("$DMD -m$MODEL " ~ flags ~ " -I$OUTPUT_BASE -of=" ~ exe ~ " $OUTPUT_BASE/main.d " ~
                    output[output.indexOf("=") + 1 .. $]);
                auto log = File(Vars.OUTPUT_BASE ~ "/run.log", "w");
                run(exe, log);
                log.close();
                results[i] = std.file.readText(Vars.OUTPUT_BASE ~ "/run.log");
            }
            if (results[0] != results[1])
            {
                writefln("with '%s %s', -j=1 runs:\n%s-j=3 runs:\n%s", flags, output, results[0], results[1]);
                return 1;
            }
        }
    }
    return 0;
}
