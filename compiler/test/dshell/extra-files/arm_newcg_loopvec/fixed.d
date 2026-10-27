// Loops over static arrays, their indices bounds checked, with ifs choosing between
// values, and loops finding the first index of a minimum or maximum, as the BC4
// encoder's search for each texel's nearest level, are vectorized and give what the
// scalar loops do.
module fixed;

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

pragma(inline, false) int id(int x) @safe { return x; }

// a loop the optimizer unrolls, as it finds its 8 iterations
@safe int unrolledAbsSum(const ref int[8] p, int v)
{
    int s;
    foreach (k; 0 .. 8)
        s += v > p[k] ? v - p[k] : p[k] - v;
    return s;
}

// unrolled completely, its 8 iterations a straight line of selects
@safe int unrolledArgminFixed(const ref int[8] p, int v)
{
    int best = 0, bestErr = int.max;
    foreach (k; 0 .. 8)
    {
        const e = v > p[k] ? v - p[k] : p[k] - v;
        if (e < bestErr)
        {
            bestErr = e;
            best = k;
        }
    }
    return best;
}

// 22 iterations: 5 of 4 lanes and 2 left
@safe int vecFirstOver(const ref int[22] p, int v)
{
    int best = 99, bestErr = int.max;
    foreach (k; 0 .. 22)
    {
        const e = p[k] > v ? p[k] - v : v - p[k];
        if (e < bestErr)
        {
            bestErr = e;
            best = k;
        }
    }
    return best;
}

int vecArgmin(const(int)* p, int n)
{
    int best = -1, bestErr = int.max;
    for (int k = 0; k < n; ++k)
        if (p[k] < bestErr)
        {
            bestErr = p[k];
            best = k;
        }
    return best ^ (bestErr << 4);
}

uint vecArgmaxU(const(uint)* p, uint n)
{
    uint best = 7, m = 5;
    foreach (uint k; 0 .. n)
        if (p[k] > m)
        {
            m = p[k];
            best = k;
        }
    return best;
}

// the last index of the minimum: doing 4 at a time, which index a lane starts with matters
int novecArgminLast(const(int)* p, int n)
{
    int best = 0, bestErr = int.max;
    for (int k = 0; k < n; ++k)
        if (p[k] <= bestErr)
        {
            bestErr = p[k];
            best = k;
        }
    return best;
}

void vecClampDiff(int* c, const(int)* a, size_t n)
{
    foreach (i; 0 .. n)
    {
        int d = a[i] - 100;
        if (d < 0)
            d = -d;
        c[i] = d;
    }
}

// BC4's eight levels and nearest level search, as whiteout's encoder has them
void bc4Palette(int r0, int r1, ref int[8] p) @safe pure nothrow @nogc
{
    p[0] = r0;
    p[1] = r1;
    foreach (i; 2 .. 8)
        p[i] = ((8 - i) * r0 + (i - 1) * r1 + 3) / 7;
}

void bc4EncodeBlock(const ref ubyte[16] px, ref ubyte[8] blk) @safe pure nothrow @nogc
{
    int lo = 255, hi = 0;
    foreach (v; px)
    {
        lo = v < lo ? v : lo;
        hi = v > hi ? v : hi;
    }
    blk[] = 0;
    blk[0] = cast(ubyte) hi;
    blk[1] = cast(ubyte) lo;
    if (hi == lo)
        return;
    int[8] p;
    bc4Palette(hi, lo, p);
    ulong bits = 0;
    foreach (i, v; px)
    {
        int best = 0, bestErr = int.max;
        foreach (k; 0 .. 8)
        {
            const e = v > p[k] ? v - p[k] : p[k] - v;
            if (e < bestErr)
            {
                bestErr = e;
                best = k;
            }
        }
        bits |= cast(ulong) best << (3 * i);
    }
    foreach (b; 0 .. 6)
        blk[2 + b] = cast(ubyte)(bits >> (8 * b));
}

int refArgmin(const(int)[] p, int v, bool last)
{
    int best = 0, bestErr = int.max;
    foreach (k; 0 .. p.length)
    {
        const e = id(v > p[k] ? v - p[k] : p[k] - v);
        if (last ? e <= bestErr : e < bestErr)
        {
            bestErr = e;
            best = id(cast(int)k);
        }
    }
    return best;
}

int main()
{
    uint seed = 1;
    int rnd() { seed = seed * 1103515245 + 12345; return id(cast(int)(seed >> 8)); }
    foreach (t; 0 .. 2000)
    {
        int[8] p;
        foreach (ref x; p)
            x = rnd() % (t % 3 == 0 ? 4 : 300) - 20;     // many ties when the range is small
        const v = rnd() % 300 - 20;
        int s;
        foreach (x; p)
            s = id(s + (v > x ? v - x : x - v));
        check(unrolledAbsSum(p, v) == s);
        check(unrolledArgminFixed(p, v) == refArgmin(p[], v, false));
        int[22] q;
        foreach (ref x; q)
            x = rnd() % (t % 3 == 0 ? 4 : 300) - 20;
        check(vecFirstOver(q, v) == refArgmin(q[], v, false));
    }
    foreach (n; 0 .. 40)
    {
        auto a = new int[](n), c = new int[](n);
        foreach (ref x; a)
            x = rnd() % (n % 2 ? 5 : 1000) - 2;
        int best = -1, bestErr = int.max;
        foreach (k; 0 .. n)
            if (a[k] < bestErr)
            {
                bestErr = id(a[k]);
                best = id(cast(int)k);
            }
        check(vecArgmin(a.ptr, n) == (best ^ (bestErr << 4)));
        uint ub = 7, um = 5;
        foreach (k; 0 .. n)
            if (cast(uint)a[k] > um)
            {
                um = id(a[k]);
                ub = id(cast(int)k);
            }
        check(vecArgmaxU(cast(uint*)a.ptr, n) == ub);
        best = 0; bestErr = int.max;
        foreach (k; 0 .. n)
            if (a[k] <= bestErr)
            {
                bestErr = id(a[k]);
                best = id(cast(int)k);
            }
        check(novecArgminLast(a.ptr, n) == best);
        vecClampDiff(c.ptr, a.ptr, n);
        foreach (k; 0 .. n)
            check(c[k] == (id(a[k]) - 100 < 0 ? 100 - a[k] : a[k] - 100));
    }
    // blocks encode to the levels nearest their texels
    foreach (t; 0 .. 500)
    {
        ubyte[16] px;
        foreach (ref x; px)
            x = cast(ubyte)(t % 4 == 0 ? 100 + rnd() % 3 : rnd());
        ubyte[8] blk;
        bc4EncodeBlock(px, blk);
        int hi = blk[0], lo = blk[1];
        if (hi == lo)
            continue;
        int[8] p;
        bc4Palette(hi, lo, p);
        ulong bits;
        foreach (b; 0 .. 6)
            bits |= cast(ulong)blk[2 + b] << (8 * b);
        foreach (i, v; px)
            check(((bits >> (3 * i)) & 7) == refArgmin(p[], v, false));
    }
    return 0;
}
