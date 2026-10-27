// Loops of 32 bit lanes that also make 64 bit values: shifts by a variable amount,
// right shifts, selects and reductions of 64 bits, done as two vectors of 2 lanes
// beside the vector of 4; and a loop whose small inner loop is unrolled, so that
// its iterations are lanes.
module wide_lanes;

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

pragma(inline, false) T id(T)(T x) { return x; }

ulong vecOrShifted(const(ubyte)* s, size_t n)
{
    ulong bits = 0;
    foreach (i; 0 .. n)
        bits |= cast(ulong)(s[i] & 7) << ((3 * i) & 63);
    return bits;
}

long vecXorSigned(const(int)* a, size_t n)
{
    long x = 0x1234_5678_9ABC_DEF0;
    foreach (i; 0 .. n)
        x ^= cast(long)a[i] << (i & 31);
    return x;
}

long vecAddSigned(const(int)* a, uint n)
{
    long sum = -5;
    foreach (i; 0 .. n)
        sum += cast(long)a[i] << (a[i] & 15);
    return sum;
}

ulong vecRightShifts(const(int)* a, const(uint)* b, size_t n)
{
    ulong acc = ~0UL;
    foreach (i; 0 .. n)
        acc &= (cast(ulong)b[i] << 32 | b[i]) >> (a[i] & 63) | cast(ulong)(cast(long)a[i] >> (b[i] & 63));
    return acc;
}

long vecWideSelect(const(int)* a, const(int)* b, size_t n)
{
    long x = 0;
    foreach (i; 0 .. n)
        x ^= a[i] > b[i] ? cast(long)a[i] << 33 : cast(long)b[i];
    return x;
}

long vecWideAnd(const(uint)* a, size_t n)
{
    long x = -1;
    foreach (i; 0 .. n)
        x &= ~(cast(long)a[i] << (a[i] & 31));
    return x;
}

/* The indices of the nearest of 8 levels to each of 16 values, 3 bits each, as BC4
 * texture compression finds them
 */
ulong vecNearest(const ref ubyte[16] px, const ref int[8] p)
{
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
    return bits;
}

ulong refOrShifted(const(ubyte)* s, size_t n)
{
    ulong bits = 0;
    foreach (i; 0 .. n)
        bits = id(bits | cast(ulong)(s[i] & 7) << ((3 * i) & 63));
    return bits;
}

long refXorSigned(const(int)* a, size_t n)
{
    long x = 0x1234_5678_9ABC_DEF0;
    foreach (i; 0 .. n)
        x = id(x ^ cast(long)a[i] << (i & 31));
    return x;
}

long refAddSigned(const(int)* a, uint n)
{
    long sum = -5;
    foreach (i; 0 .. n)
        sum = id(sum + (cast(long)a[i] << (a[i] & 15)));
    return sum;
}

ulong refRightShifts(const(int)* a, const(uint)* b, size_t n)
{
    ulong acc = ~0UL;
    foreach (i; 0 .. n)
        acc = id(acc & ((cast(ulong)b[i] << 32 | b[i]) >> (a[i] & 63) | cast(ulong)(cast(long)a[i] >> (b[i] & 63))));
    return acc;
}

long refWideSelect(const(int)* a, const(int)* b, size_t n)
{
    long x = 0;
    foreach (i; 0 .. n)
        x = id(x ^ (a[i] > b[i] ? cast(long)a[i] << 33 : cast(long)b[i]));
    return x;
}

long refWideAnd(const(uint)* a, size_t n)
{
    long x = -1;
    foreach (i; 0 .. n)
        x = id(x & ~(cast(long)a[i] << (a[i] & 31)));
    return x;
}

ulong refNearest(const ref ubyte[16] px, const ref int[8] p)
{
    ulong bits = 0;
    foreach (i; 0 .. 16)
    {
        const v = px[i];
        int best = 0, bestErr = int.max;
        foreach (k; 0 .. 8)
        {
            const e = id(v > p[k] ? v - p[k] : p[k] - v);
            if (e < bestErr)
            {
                bestErr = e;
                best = k;
            }
        }
        bits |= cast(ulong) best << (3 * i);
    }
    return bits;
}

int main()
{
    enum N = 80;
    uint seed = 7;
    uint rnd() { seed = seed * 1664525 + 1013904223; return seed; }
    ubyte[N] s;
    int[N] a, b;
    uint[N] u;
    foreach (round; 0 .. 4)
    {
        foreach (i; 0 .. N)
        {
            s[i] = cast(ubyte)rnd();
            a[i] = cast(int)rnd() >> (round * 7);
            b[i] = round & 1 ? -a[i] : cast(int)rnd();
            u[i] = round == 3 ? uint.max - cast(uint)i : rnd();
        }
        foreach (n; 0 .. 66)
            foreach (off; 0 .. 3)
            {
                check(vecOrShifted(s.ptr + off, n) == refOrShifted(s.ptr + off, n));
                check(vecXorSigned(a.ptr + off, n) == refXorSigned(a.ptr + off, n));
                check(vecAddSigned(a.ptr + off, cast(uint)n) == refAddSigned(a.ptr + off, cast(uint)n));
                check(vecRightShifts(a.ptr + off, u.ptr + off, n) == refRightShifts(a.ptr + off, u.ptr + off, n));
                check(vecWideSelect(a.ptr + off, b.ptr + off, n) == refWideSelect(a.ptr + off, b.ptr + off, n));
                check(vecWideAnd(u.ptr + off, n) == refWideAnd(u.ptr + off, n));
            }
    }
    foreach (round; 0 .. 2000)
    {
        ubyte[16] px;
        int[8] p;
        foreach (ref x; px)
            x = cast(ubyte)(round & 1 ? rnd() & 0x3F : rnd());
        foreach (ref x; p)
            x = round % 7 == 0 ? 100 : rnd() & 0xFF;
        if (round % 5 == 0)
            p[3] = p[6];        // ties pick the first
        check(vecNearest(px, p) == refNearest(px, p));
    }
    return 0;
}
