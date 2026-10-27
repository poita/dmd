// Elementwise float loops vectorized 4 lanes at a time give bit for bit what the
// scalar loop does, NaNs, signed zeros and infinities included; a float sum is
// not reassociated, so stays scalar.
module float_ops;

// asserts are compiled out by -release
void check(bool ok, int line = __LINE__)
{
    import core.stdc.stdio : printf;
    import core.stdc.stdlib : abort;
    if (!ok)
    {
        printf("check failed at line %d\n", line);
        abort();
    }
}

pragma(inline, false) float id(float x) { return x; }
pragma(inline, false) int idi(int x) { return x; }

void vecArith(float[] c, const(float)[] a, const(float)[] b)
{
    foreach (i; 0 .. c.length)
        c[i] = a[i] * b[i] - a[i] / (b[i] + 1.5f);
}

void vecUnary(float[] c, const(float)[] a)
{
    import core.math : sqrt;
    foreach (i; 0 .. c.length)
        c[i] = -(a[i] < 0 ? -a[i] : a[i]) + sqrt(a[i] * a[i]);
}

void vecFmin(float[] c, const(float)[] a, const(float)[] b)
{
    foreach (i; 0 .. c.length)
        c[i] = a[i] < b[i] ? a[i] : b[i];
}

void vecFmaxGe(float[] c, const(float)[] a, const(float)[] b)
{
    foreach (i; 0 .. c.length)
        c[i] = a[i] >= b[i] ? a[i] : b[i];
}

void vecSelectNe(float[] c, const(float)[] a, const(float)[] b)
{
    foreach (i; 0 .. c.length)
        c[i] = a[i] != b[i] ? 1.0f : 2.0f;
}

void vecToInt(int[] c, const(float)[] a)
{
    foreach (i; 0 .. c.length)
        c[i] = cast(int)(a[i] * 2.5f);
}

// the truncation fixed up to round down, as fcvtms
int ifloor(float x)
{
    const i = cast(int) x;
    return x < i ? i - 1 : i;
}

void vecFloor(int[] c, const(float)[] a)
{
    foreach (i; 0 .. c.length)
        c[i] = ifloor(a[i] * 3.0f);
}

void vecFromInt(float[] c, const(int)[] a)
{
    foreach (i; 0 .. c.length)
        c[i] = cast(float)a[i] * 0.5f;
}

void vecZeroCompare(float[] c, const(float)[] a)
{
    foreach (i; 0 .. c.length)
        c[i] = a[i] > 0 ? a[i] : 0;
}

struct Grid
{
    float[] hu, wu, hv, wv, div;
    uint size, uw;

    void vecDivergence()
    {
        foreach (j; 0 .. size)
            foreach (i; 0 .. size)
            {
                const c = size_t(j) * size + i;
                const uL = size_t(j) * uw + i;
                const vB = size_t(j) * size + i;
                div[c] = hu[uL + 1] * wu[uL + 1] - hu[uL] * wu[uL]
                    + hv[vB + size] * wv[vB + size] - hv[vB] * wv[vB];
            }
    }
}

float novecSum(const(float)[] a)
{
    float s = 0;
    foreach (v; a)
        s += v;
    return s;
}

bool same(float x, float y) { return *cast(uint*)&x == *cast(uint*)&y; }

int main()
{
    static immutable float[] specials = [0.0f, -0.0f, float.nan, -float.nan, float.infinity, -float.infinity,
        1.0f, -1.0f, float.min_normal, float.max, 3e9f, -3e9f, 0.4f, -0.6f];
    foreach (n; 0 .. 40)
    {
        auto a = new float[](n), b = new float[](n), c = new float[](n);
        auto ia = new int[](n), ic = new int[](n);
        foreach (i; 0 .. n)
        {
            a[i] = specials[i % specials.length];
            b[i] = specials[(i * 5 + 3) % specials.length] * 0.75f;
            ia[i] = idi(cast(int)(i * 2654435761u));
        }
        vecArith(c, a, b);
        foreach (i; 0 .. n) check(same(c[i], id(a[i]) * b[i] - a[i] / (b[i] + 1.5f)));
        vecUnary(c, a);
        {
            import core.math : sqrt;
            foreach (i; 0 .. n) check(same(c[i], -(id(a[i]) < 0 ? -a[i] : a[i]) + sqrt(id(a[i]) * a[i])));
        }
        vecFmin(c, a, b);
        foreach (i; 0 .. n) check(same(c[i], id(a[i]) < b[i] ? a[i] : b[i]));
        vecFmaxGe(c, a, b);
        foreach (i; 0 .. n) check(same(c[i], id(a[i]) >= b[i] ? a[i] : b[i]));
        vecSelectNe(c, a, b);
        foreach (i; 0 .. n) check(same(c[i], id(a[i]) != b[i] ? 1.0f : 2.0f));
        vecToInt(ic, a);
        foreach (i; 0 .. n) check(ic[i] == cast(int)(id(a[i]) * 2.5f));
        vecFloor(ic, a);
        foreach (i; 0 .. n) check(ic[i] == ifloor(id(a[i]) * 3.0f));
        vecFromInt(c, ia);
        foreach (i; 0 .. n) check(same(c[i], cast(float)idi(ia[i]) * 0.5f));
        vecZeroCompare(c, a);
        foreach (i; 0 .. n) check(same(c[i], id(a[i]) > 0 ? a[i] : 0));
        float s = 0;
        foreach (v; a[0 .. n])
            s = id(s + v);
        const t = novecSum(a);
        check(same(t, s) || t != t && s != s);      // which NaN an addition of two keeps may differ
    }

    foreach (size; 0 .. 12)
    {
        Grid g;
        g.size = size;
        g.uw = size + 1;
        g.hu = new float[](size * (size + 1) + 1);
        g.wu = new float[](size * (size + 1) + 1);
        g.hv = new float[]((size + 1) * size);
        g.wv = new float[]((size + 1) * size);
        g.div = new float[](size * size);
        foreach (i, ref v; g.hu) v = id(i * 0.25f + 1);
        foreach (i, ref v; g.wu) v = id(i * -0.5f + 3);
        foreach (i, ref v; g.hv) v = id(i * 0.125f - 2);
        foreach (i, ref v; g.wv) v = id(i * 0.75f);
        g.vecDivergence();
        foreach (j; 0 .. size)
            foreach (i; 0 .. size)
            {
                const c = size_t(j) * size + i;
                const uL = size_t(j) * g.uw + i;
                const vB = size_t(j) * size + i;
                check(same(g.div[c], id(g.hu[uL + 1] * g.wu[uL + 1]) - id(g.hu[uL] * g.wu[uL])
                    + id(g.hv[vB + size] * g.wv[vB + size]) - id(g.hv[vB] * g.wv[vB])));
            }
    }
    return 0;
}
