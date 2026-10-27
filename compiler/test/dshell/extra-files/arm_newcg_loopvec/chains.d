// Chains of additions, bitwise operations, minimums and maximums of values loaded
// one after the other, as fully unrolled loops make them, done across the lanes of
// vectors of the values; and those that are not.
module chains;

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

void vecMinMax(const ref ubyte[16] px, out int rlo, out int rhi)
{
    int lo = 255, hi = 0;
    foreach (v; px)
    {
        lo = v < lo ? v : lo;
        hi = v > hi ? v : hi;
    }
    rlo = lo;
    rhi = hi;
}

int vecSumBytes(const ref ubyte[16] a, int start)
{
    int s = start;
    foreach (v; a)
        s += v;
    return s;
}

int vecSumSigned(const ref byte[8] a)
{
    int s = 0;
    foreach (v; a)
        s += v;
    return s;
}

int vecMinSigned(const ref byte[16] a, int lo)
{
    foreach (v; a)
        lo = v < lo ? v : lo;
    return lo;
}

uint maxUnsignedOfSigned(const ref byte[16] a)
{
    uint hi = 0;
    foreach (v; a)
        hi = cast(uint)v > hi ? cast(uint)v : hi;
    return hi;
}

int vecSumShorts(const ref short[8] a)
{
    int s = 7;
    foreach (v; a)
        s += v;
    return s;
}

int vecMaxInts(const ref int[8] a)
{
    int m = int.min;
    foreach (v; a)
        m = v > m ? v : m;
    return m;
}

uint vecMinUints(const ref uint[16] a, uint m)
{
    foreach (v; a)
        m = v < m ? v : m;
    return m;
}

int vecSumInts(const ref int[16] a)
{
    int s = 0;
    foreach (v; a)
        s += v;
    return s;
}

uint vecOrBytes(const ref ubyte[16] a)
{
    uint r = 0x100;
    foreach (v; a)
        r |= v;
    return r;
}

int vecXorShorts(const ref short[8] a)
{
    int r = 0;
    foreach (v; a)
        r ^= v;
    return r;
}

uint vecAndInts(const ref uint[8] a, uint r)
{
    foreach (v; a)
        r &= v;
    return r;
}

// a value of the chain is read elsewhere too: the chains before and after it
int vecSumUsed(const ref int[8] a, ref int mid)
{
    int s = 0;
    foreach (i, v; a)
    {
        s += v;
        if (i == 3)
            mid = s;
    }
    return s;
}

// a store between the loads
int novecSumStored(ref int[8] a)
{
    int s = a[0] + a[1] + a[2] + a[3];
    a[5] = 1;
    return s + a[4] + a[5] + a[6] + a[7];
}

void refMinMax(const ref ubyte[16] px, out int lo, out int hi)
{
    lo = 255;
    hi = 0;
    foreach (i; 0 .. 16)
    {
        const v = id(px[i]);
        lo = v < lo ? v : lo;
        hi = v > hi ? v : hi;
    }
}

int main()
{
    uint seed = 3;
    uint rnd() { seed = seed * 1664525 + 1013904223; return seed >> 8; }
    foreach (round; 0 .. 3000)
    {
        const small = round % 3 == 0;
        ubyte[16] ub;
        byte[16] sb;
        byte[8] sb8;
        short[8] ss;
        int[8] i8;
        int[16] i16;
        uint[16] u16;
        uint[8] u4;
        foreach (ref x; ub) x = cast(ubyte)(small ? rnd() & 3 : rnd());
        foreach (ref x; sb) x = cast(byte)rnd();
        foreach (ref x; sb8) x = cast(byte)rnd();
        foreach (ref x; ss) x = cast(short)(rnd() << (round & 7));
        foreach (ref x; i8) x = cast(int)(rnd() << 8) ^ round;
        foreach (ref x; i16) x = cast(int)(rnd() << 9);
        foreach (ref x; u16) x = rnd() << (round & 15);
        foreach (ref x; u4) x = ~(1u << (rnd() & 31));
        if (round % 7 == 0)
            i8[] = int.min;

        int lo, hi, rlo, rhi;
        vecMinMax(ub, lo, hi);
        refMinMax(ub, rlo, rhi);
        check(lo == rlo && hi == rhi);

        int s = id(round);
        foreach (x; ub) s += id(x);
        check(vecSumBytes(ub, round) == s);
        s = 0;
        foreach (x; sb8) s += id(x);
        check(vecSumSigned(sb8) == s);
        int m = id(round % 5 == 0 ? -200 : 50);
        const m0 = m;
        foreach (x; sb) m = id(x) < m ? x : m;
        check(vecMinSigned(sb, m0) == m);
        uint um = 0;
        foreach (x; sb) um = id(cast(uint)x) > um ? cast(uint)x : um;
        check(maxUnsignedOfSigned(sb) == um);
        s = 7;
        foreach (x; ss) s += id(x);
        check(vecSumShorts(ss) == s);
        m = int.min;
        foreach (x; i8) m = id(x) > m ? x : m;
        check(vecMaxInts(i8) == m);
        uint mu = id(round & 1 ? uint.max : 12345u);
        const mu0 = mu;
        foreach (x; u16) mu = id(x) < mu ? x : mu;
        check(vecMinUints(u16, mu0) == mu);
        s = 0;
        foreach (x; i16) s += id(x);
        check(vecSumInts(i16) == s);
        uint r = 0x100;
        foreach (x; ub) r |= id(x);
        check(vecOrBytes(ub) == r);
        int xr = 0;
        foreach (x; ss) xr ^= id(x);
        check(vecXorShorts(ss) == xr);
        uint ar = id(round * 2654435761u);
        const ar0 = ar;
        foreach (x; u4) ar &= id(x);
        check(vecAndInts(u4, ar0) == ar);

        int mid;
        s = 0;
        int rmid;
        foreach (i, x; i8) { s += id(x); if (i == 3) rmid = s; }
        check(vecSumUsed(i8, mid) == s && mid == rmid);
        auto c = i8;
        const t = c[0] + c[1] + c[2] + c[3] + c[4] + 1 + c[6] + c[7];
        check(novecSumStored(c) == t && c[5] == 1);
    }
    return 0;
}
