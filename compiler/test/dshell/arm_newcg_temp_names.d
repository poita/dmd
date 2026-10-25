// The code of a function does not depend on the names of the temporaries the
// compiler generates for it, which are numbered in the order a compiler process
// generates them: here after the temporaries of a module compiled before it, of
// several sizes.
module test.dshell.arm_newcg_temp_names;

import dshell;
import std.format : format;
import std.process : execute;
import std.regex : regex, replaceAll;

int main()
{
    version (OSX) {} else return DISABLED;
    version (AArch64) {} else return DISABLED;

    enum f = "__D5mouse16createMouseJointFNeSQBc9b3WorldIdSQBq6Body3DQlSQCd4Vec3fffZSQCq12MotorJoint3D";
    string first;
    foreach (n; [1, 1000, 2147, 2240, 2581, 2953, 3077, 3263, 4348, 4410, 4534])
    {
        string pre = format("module pre%d;\nstruct P { int a, b; }\nP g(P p) { return P(p.b, p.a); }\n" ~
            "int h(int x)\n{\n    int s;\n", n);
        foreach (i; 0 .. n)
            pre ~= format("    s += g(P(x, %d)).a;\n", i);
        pre ~= "    return s;\n}\n";
        std.file.write(format("%s/pre%d.d", Vars.OUTPUT_BASE, n), pre);
        const obj = format("%s/o%d%s", Vars.OUTPUT_BASE, n, Vars.OBJ);
        run(format("$DMD -m$MODEL -O -inline -release -c -of=%s $OUTPUT_BASE/pre%d.d " ~
            "$EXTRA_FILES/arm_newcg_temp_names/mouse.d", obj, n));
        const dis = execute(["objdump", "-d", "--no-show-raw-insn", "--disassemble-symbols=" ~ f, obj]);
        assert(dis.status == 0, dis.output);
        // the code, without the addresses, which the module before it moves
        const code = dis.output.replaceAll(regex(`(?m)^\s*[0-9a-f]+:`), "")
            .replaceAll(regex(`(0x)?[0-9a-f]+ <[^>]*>`), "<>")
            .replaceAll(regex(`(?m)^.*file format.*$`), "");
        if (n == 1)
            first = code;
        else if (code != first)
        {
            writefln("createMouseJoint compiled after %s temporaries of another module differs:\n%s\nfrom:\n%s",
                n, code, first);
            return 1;
        }
    }
    return 0;
}
