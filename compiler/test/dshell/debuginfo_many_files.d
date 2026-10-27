// The debug information of an object file of more than 255 source files names the
// file of each function.
module test.dshell.debuginfo_many_files;

import dshell;
import std.algorithm : canFind, countUntil;
import std.format : format;
import std.process : execute;
import std.string : lineSplitter;

enum modules = 300;

int main()
{
    version (OSX) {} else return DISABLED;

    const dir = Vars.OUTPUT_BASE;
    string files;
    foreach (k; 0 .. modules)
    {
        std.file.write(dir ~ format("/f%d.d", k), format("module f%1$d; int g%1$d(int x) { return x + %1$d; }\n", k));
        files ~= format(" %s/f%d.d", dir, k);
    }
    std.file.write(dir ~ "/files.rsp", files);
    const obj = dir ~ "/files" ~ Vars.OBJ;
    run("$DMD -m$MODEL -j=1 -g -c -of=" ~ obj ~ " @" ~ dir ~ "/files.rsp");

    const info = execute(["dwarfdump", "--debug-info", obj]);
    assert(info.status == 0, info.output);
    // the DW_AT_decl_file of each subprogram follows its DW_AT_name
    string name;
    size_t checked;
    foreach (line; info.output.lineSplitter)
    {
        if (line.canFind("DW_AT_name"))
            name = line;
        else if (line.canFind("DW_AT_decl_file") && name.canFind(`("f`) && name.canFind(".g"))
        {
            // DW_AT_name ("f12.g12")
            const k = name[name.countUntil(`("f`) + 3 .. $];
            const n = k[0 .. k.countUntil(".")];
            if (!line.canFind("/f" ~ n ~ ".d"))
            {
                writefln("the subprogram %s is declared in %s", name, line);
                return 1;
            }
            ++checked;
        }
    }
    if (checked != modules)
    {
        writeln(info.output);
        writefln("%d subprograms checked", checked);
        return 1;
    }
    return 0;
}
