// The code generated does not depend on what memory the backend's arrays grow into
// holds: compiling with DMD_BARRAY_FILL set to different bytes, which the arrays'
// new elements are filled with, writes the same object file.
module test.dshell.barray_fill;

import dshell;

// loops the AArch64 code generator vectorizes, with registers defined before them
// that are used after them
enum source = q{
module m;
uint xorAll(uint[] a, uint x, uint y)
{
    foreach (i; 0 .. a.length)
        a[i] ^= x;
    return x + y;
}
int sumScaled(const(int)[] a, int k, int b)
{
    int s;
    foreach (i; 0 .. a.length)
        s += a[i] * k;
    return s + k * b;
}
float scaleAll(float[] a, float f, float g)
{
    foreach (i; 0 .. a.length)
        a[i] = a[i] * f + g;
    return f - g;
}
};

int main()
{
    std.file.write(Vars.OUTPUT_BASE ~ "/m.d", source);
    foreach (flags; ["-O -release", "-O -inline -release", ""])
    {
        ubyte[] first;
        foreach (fill; ["0", "255", "85"])
        {
            run("$DMD -m$MODEL -c " ~ flags ~ " -of$OUTPUT_BASE/m$OBJ $OUTPUT_BASE/m.d",
                stdout, stderr, ["DMD_BARRAY_FILL": fill]);
            auto bytes = cast(ubyte[]) std.file.read(shellExpand("$OUTPUT_BASE/m$OBJ"));
            if (fill == "0")
                first = bytes;
            else if (bytes != first)
            {
                writefln("with '%s', DMD_BARRAY_FILL=%s gives another object file than DMD_BARRAY_FILL=0",
                    flags, fill);
                return 1;
            }
        }
    }
    return 0;
}
