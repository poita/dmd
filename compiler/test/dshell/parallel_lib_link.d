// A library a split compilation writes links and runs: the data of a template
// instance is written even when other workers generate its functions, and the
// object files the workers write for template instances have different names.
module test.dshell.parallel_lib_link;

import dshell;
import std.conv : to;

int main()
{
    version (Posix) {} else return DISABLED;

    std.file.mkdirRecurse(Vars.OUTPUT_BASE ~ "/inc");
    std.file.write(Vars.OUTPUT_BASE ~ "/inc/tmpl.d", q{
        module tmpl;
        __gshared int constructed;
        struct Box(T)
        {
            T v = 7;
            __gshared T[4] table;
            T get() const { return v + table[1]; }
            static void set(T x) { table[1] = x; }
        }
        class Counter(T)
        {
            T n;
            shared static this() { ++constructed; }
            void add(T x) { n += x; }
        }
    });
    string files, imports, calls;
    foreach (i; 0 .. 6)
    {
        const m = "m" ~ i.to!string;
        std.file.write(Vars.OUTPUT_BASE ~ "/" ~ m ~ ".d", "module " ~ m ~ "; import tmpl;\n" ~
            "int use" ~ i.to!string ~ "() { Box!int b; Box!int.set(" ~ i.to!string ~ "); " ~
            "auto c = new Counter!long; c.add(b.get()); Box!long l; return cast(int) (c.n + l.get()); }\n");
        files ~= " $OUTPUT_BASE/" ~ m ~ ".d";
        imports ~= "import " ~ m ~ ";\n";
        calls ~= "    if (use" ~ i.to!string ~ "() != 14 + " ~ i.to!string ~ ") return 1;\n";
    }
    std.file.write(Vars.OUTPUT_BASE ~ "/main.d", imports ~ "import tmpl;\nint main()\n{\n" ~ calls ~
        "    return constructed == 1 ? 0 : 2;\n}\n");

    foreach (flags; ["", "-O -inline -release"])
    {
        run("$DMD -m$MODEL -j=3 -lib " ~ flags ~ " -I$OUTPUT_BASE/inc -of=$OUTPUT_BASE/link$LIBEXT" ~ files);
        run("$DMD -m$MODEL -I$OUTPUT_BASE -I$OUTPUT_BASE/inc -of=$OUTPUT_BASE/link$EXE $OUTPUT_BASE/main.d " ~
            "$OUTPUT_BASE/inc/tmpl.d $OUTPUT_BASE/link$LIBEXT");
        run("$OUTPUT_BASE/link$EXE");
    }
    return 0;
}
