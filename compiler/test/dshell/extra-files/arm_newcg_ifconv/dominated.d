// A test that the branch leading to it decides is not made again

struct Teams { ubyte[8] team; }

// p < 8 decides the bounds check of team[p]
ubyte sel1_teamOf(ref const Teams t, ubyte p) @safe
{
    return p < t.team.length ? t.team[p] : p;
}

bool sel2_allied(ref const Teams t, ubyte a, ubyte b) @safe
{
    return sel1_teamOf(t, a) == sel1_teamOf(t, b);
}

__gshared int calls;
pragma(inline, false) void hit(int k) { calls = calls * 10 + k; }

// x < 4 decides x < 10, and so x != 7
void sel1_below(uint x)
{
    if (x < 4)
    {
        if (x < 10)
            hit(1);
        else
            hit(2);
        if (x == 7)
            hit(3);
    }
    else
        hit(4);
}

// x > 5, signed, decides x >= 0 and x > -3
void sel1_positive(int x)
{
    if (x > 5)
    {
        if (x >= 0)
            hit(1);
        else
            hit(2);
        if (x <= -3)
            hit(3);
    }
}

// a < b decides b > a and b <= a, the operands the other way round
void sel1_swapped(long a, long b)
{
    if (a < b)
    {
        if (b > a)
            hit(1);
        if (b <= a)
            hit(2);
    }
    else
        hit(3);
}

// x != 0 decides x == 0 as a test of zero
void sel1_nonzero(ulong x)
{
    if (x != 0)
    {
        if (x == 0)
            hit(1);
        else
            hit(2);
    }
}

// what the first test does not decide is tested again
void undecided(uint x)
{
    if (x < 10)
    {
        if (x < 4)
            hit(1);
        else
            hit(2);
    }
}

// a value changed between the tests is tested again
void changed(uint x)
{
    if (x < 4)
    {
        x += 10;
        if (x < 10)
            hit(1);
        else
            hit(2);
    }
}

// the comparison of floats d < m, then d == m, is made once
int ops12_closer(float d, float m, int a, int b)
{
    if (d < m || d == m && a < b)
        return 1;
    return 0;
}

// NaN compares unordered: d < m being false does not make d == m
int nanCloser(float d, float m)
{
    if (d < m)
        return 1;
    if (d == m)
        return 2;
    if (d > m)
        return 3;
    return 4;
}

int run(scope void delegate() dg)
{
    calls = 0;
    dg();
    return calls;
}

void main()
{
    Teams t;
    foreach (i, ref v; t.team)
        v = cast(ubyte)(i / 2);
    if (sel1_teamOf(t, 0) != 0 || sel1_teamOf(t, 7) != 3 || sel1_teamOf(t, 8) != 8 || sel1_teamOf(t, 255) != 255)
        assert(0);
    if (!sel2_allied(t, 2, 3) || sel2_allied(t, 1, 2) || !sel2_allied(t, 9, 9) || sel2_allied(t, 7, 8))
        assert(0);

    if (run({ sel1_below(0); }) != 1 || run({ sel1_below(3); }) != 1 || run({ sel1_below(4); }) != 4 ||
        run({ sel1_below(7); }) != 4 || run({ sel1_below(uint.max); }) != 4)
        assert(0);
    if (run({ sel1_positive(6); }) != 1 || run({ sel1_positive(int.max); }) != 1 || run({ sel1_positive(5); }) != 0 ||
        run({ sel1_positive(-4); }) != 0 || run({ sel1_positive(int.min); }) != 0)
        assert(0);
    if (run({ sel1_swapped(1, 2); }) != 1 || run({ sel1_swapped(2, 2); }) != 3 || run({ sel1_swapped(long.min, long.max); }) != 1 ||
        run({ sel1_swapped(long.max, long.min); }) != 3)
        assert(0);
    if (run({ sel1_nonzero(0); }) != 0 || run({ sel1_nonzero(1); }) != 2 || run({ sel1_nonzero(ulong.max); }) != 2)
        assert(0);
    if (run({ undecided(3); }) != 1 || run({ undecided(4); }) != 2 || run({ undecided(10); }) != 0)
        assert(0);
    if (run({ changed(0); }) != 2 || run({ changed(3); }) != 2 || run({ changed(4); }) != 0)
        assert(0);

    if (ops12_closer(1, 2, 5, 0) != 1 || ops12_closer(2, 2, 1, 2) != 1 || ops12_closer(2, 2, 2, 1) != 0 ||
        ops12_closer(3, 2, 1, 2) != 0 || ops12_closer(float.nan, 2, 1, 2) != 0 || ops12_closer(2, float.nan, 1, 2) != 0)
        assert(0);
    if (nanCloser(1, 2) != 1 || nanCloser(2, 2) != 2 || nanCloser(3, 2) != 3 || nanCloser(float.nan, 2) != 4 ||
        nanCloser(2, float.nan) != 4 || nanCloser(-0.0f, 0.0f) != 2)
        assert(0);
}
