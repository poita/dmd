/* PERMUTE_ARGS: -O -inline
 */
// A floating-point variable stepped by a constant is no induction variable:
// `r * c` recomputed each pass and `t += step * c` carried along round
// differently, so the product must be taken afresh every time.

pragma(inline, false) void scaled(float[] outp)
{
    float r = 0;
    foreach (i; 0 .. outp.length)
    {
        outp[i] = r * (1.0f / 17.0f);
        r += 3.0f;
    }
}

pragma(inline, false) void offset(double[] outp)
{
    double r = 0;
    foreach (i; 0 .. outp.length)
    {
        outp[i] = r + 0.1;
        r += 0.7;
    }
}

void main()
{
    float[14] f;
    scaled(f[]);
    foreach (i, v; f)
    {
        float r = 0;
        foreach (k; 0 .. i)
            r += 3.0f;
        assert(v == r * (1.0f / 17.0f));
    }
    double[20] d;
    offset(d[]);
    foreach (i, v; d)
    {
        double r = 0;
        foreach (k; 0 .. i)
            r += 0.7;
        assert(v == r + 0.1);
    }
}
