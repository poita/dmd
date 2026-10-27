/* REQUIRED_ARGS: -O -inline
 * PERMUTE_ARGS: -release -g
 */
// Loops whose branches have conditions that are the same on every iteration,
// which the optimizer can take out of the loop, and loops with conditions
// that only look so.

int g;              // a global the loops read
__gshared int gs;   // a global written by a call in a loop
shared int sh;      // shared data is never taken as unchanging

pragma(inline, false) void bump() { ++gs; }
pragma(inline, false) void bumpPtr(int* p) { ++*p; }

pragma(inline, false)
int sumParam(const(int)[] a, bool neg)
{
    int s;
    foreach (x; a)
    {
        if (neg)
            s -= x;
        else
            s += x;
    }
    return s;
}

// the loop runs zero times, so only the evaluation of the condition before it would show
pragma(inline, false)
int zeroTrip(int* p, size_t n, int k)
{
    int s = 7;
    foreach (i; 0 .. n)
    {
        if (k > 3)
            s += p[i];
        else
            s -= p[i];
    }
    return s;
}

pragma(inline, false)
int globalCond(const(int)[] a)
{
    int s;
    foreach (x; a)
        s += g == 1 ? x : 2 * x;
    return s;
}

// the call writes gs, which the condition reads
pragma(inline, false)
int globalWrittenByCall(int n)
{
    int s;
    gs = 0;
    foreach (i; 0 .. n)
    {
        if (gs < 3)
            s += 1;
        else
            s += 100;
        bump();
    }
    return s;
}

// the condition's variable changes in the loop
pragma(inline, false)
int modifiedInLoop(int n, int k)
{
    int s;
    foreach (i; 0 .. n)
    {
        if (k & 1)
            s += i;
        else
            s += 2 * i;
        k += i;
    }
    return s;
}

// the variable changes through a pointer to it
pragma(inline, false)
int modifiedThroughPointer(int n)
{
    int k = 0;
    int* p = &k;
    int s;
    foreach (i; 0 .. n)
    {
        if (k < 2)
            s += 1;
        else
            s += 10;
        bumpPtr(p);
    }
    return s;
}

pragma(inline, false)
int sharedCond(int n)
{
    int s;
    foreach (i; 0 .. n)
    {
        if (sh != 0)
            s += 1;
        else
            s += 2;
    }
    return s;
}

pragma(inline, false)
int nested(int n, int m, bool flag)
{
    int s;
    foreach (i; 0 .. n)
        foreach (j; 0 .. m)
        {
            if (flag)
                s += i * j;
            else
                s -= i + j;
        }
    return s;
}

// the inner loop's condition is the outer loop's variable
pragma(inline, false)
int nestedOuterVar(int n, int m)
{
    int s;
    foreach (i; 0 .. n)
        foreach (j; 0 .. m)
        {
            if (i & 1)
                s += j;
            else
                s -= j;
        }
    return s;
}

pragma(inline, false)
int breakContinue(const(int)[] a, int limit, bool skipOdd)
{
    int s;
    foreach (x; a)
    {
        if (skipOdd && (x & 1))
            continue;
        if (s > limit)
            break;
        if (skipOdd)
            s += x;
        else
            s += 3 * x;
    }
    return s;
}

pragma(inline, false)
int withReturn(const(int)[] a, int stop, bool twice)
{
    int s;
    foreach (x; a)
    {
        if (x == stop)
            return twice ? -s : s;
        if (twice)
            s += 2 * x;
        else
            s += x;
    }
    return s + 1000;
}

pragma(inline, false)
int withGoto(const(int)[] a, bool flag)
{
    int s;
    size_t i;
Lagain:
    if (i < a.length)
    {
        if (flag)
            s += a[i];
        else
            s ^= a[i];
        ++i;
        goto Lagain;
    }
    return s;
}

int finallies;

pragma(inline, false)
int tryFinally(const(int)[] a, bool flag)
{
    int s;
    foreach (x; a)
    {
        try
        {
            if (flag)
                s += x;
            else
                s -= x;
            if (x == 100)
                throw new Exception("x");
        }
        finally
            ++finallies;
    }
    return s;
}

pragma(inline, false)
long mixed(const(long)[] a, long lo, long hi)
{
    long s;
    const inside = lo >= 0 && hi < 100;
    foreach (i, x; a)
    {
        if (inside)
            s += x * i;
        else
        {
            if (x < lo || x > hi)
                break;
            s += x;
        }
    }
    return s;
}

pragma(inline, false)
double floats(const(double)[] a, double t)
{
    double s = 0;
    foreach (x; a)
    {
        if (t > 0.5)
            s += x * t;
        else
            s -= x;
    }
    return s;
}

// a nested function changes the condition's variable through the frame
pragma(inline, false)
int nestedFunctionWrites(int n)
{
    int k = 0;
    pragma(inline, false) void step() { ++k; }
    int s;
    foreach (i; 0 .. n)
    {
        if (k < 2)
            s += 1;
        else
            s += 10;
        step();
    }
    return s;
}

// a delegate changes it through a closure
pragma(inline, false)
int delegateWrites(int n, ref void delegate() dg)
{
    int k = 0;
    dg = () { ++k; };
    int s;
    foreach (i; 0 .. n)
    {
        if (k < 2)
            s += 1;
        else
            s += 10;
        dg();
    }
    return s;
}

// a loop on the way to a throw only
pragma(inline, false)
void coldLoop(const(int)[] a, bool flag)
{
    int s;
    foreach (x; a)
    {
        if (flag)
            s += x;
        else
            s -= x;
    }
    throw new Exception(s > 0 ? "positive" : "not positive");
}

// a check that -release keeps
void check(bool c, int line = __LINE__)
{
    import core.stdc.stdio : printf;
    if (!c)
    {
        printf("failure at line %d\n", line);
        assert(0);
    }
}

void main()
{
    immutable int[] a = [1, 2, 3, 4, 5, 6];
    check(sumParam(a, false) == 21);
    check(sumParam(a, true) == -21);
    check(sumParam([], true) == 0);

    check(zeroTrip(null, 0, 5) == 7);
    check(zeroTrip(null, 0, 1) == 7);
    int[3] b = [1, 2, 3];
    check(zeroTrip(b.ptr, 3, 5) == 13);
    check(zeroTrip(b.ptr, 3, 1) == 1);

    g = 1;
    check(globalCond(a) == 21);
    g = 2;
    check(globalCond(a) == 42);

    check(globalWrittenByCall(5) == 1 + 1 + 1 + 100 + 100);
    check(gs == 5);

    // k: 1 (odd) +0 -> 1, odd +1 -> 2, even +2*2 -> 4, even +2*3 -> 7, odd +4
    check(modifiedInLoop(5, 1) == 0 + 1 + 4 + 6 + 4);

    check(modifiedThroughPointer(4) == 1 + 1 + 10 + 10);

    check(sharedCond(3) == 6);

    check(nested(3, 3, true) == 9);
    check(nested(3, 3, false) == -18);
    check(nested(0, 3, true) == 0);
    check(nested(3, 0, false) == 0);

    check(nestedOuterVar(3, 4) == -6 + 6 - 6);

    check(breakContinue(a, 100, true) == 12);
    check(breakContinue(a, 100, false) == 63);
    check(breakContinue(a, 5, false) == 9);

    check(withReturn(a, 4, true) == -12);
    check(withReturn(a, 4, false) == 6);
    check(withReturn(a, 9, false) == 1021);

    check(withGoto(a, true) == 21);
    check(withGoto(a, false) == (1 ^ 2 ^ 3 ^ 4 ^ 5 ^ 6));

    finallies = 0;
    check(tryFinally(a, true) == 21);
    check(tryFinally(a, false) == -21);
    check(finallies == 12);
    bool caught;
    try
        tryFinally([1, 100, 2], true);
    catch (Exception)
        caught = true;
    check(caught && finallies == 14);

    immutable long[] c = [5, 6, 200, 7];
    check(mixed(c, 0, 99) == 0 + 6 + 400 + 21);
    check(mixed(c, -1, 99) == 11);
    check(mixed(c, 0, 100) == 11);
    check(mixed([], 0, 1) == 0);

    check(floats([1.0, 2.0], 2.0) == 6.0);
    check(floats([1.0, 2.0], double.nan) == -3.0);

    check(nestedFunctionWrites(4) == 22);
    void delegate() dg;
    check(delegateWrites(4, dg) == 22);

    foreach (flag; [false, true])
    {
        string msg;
        try
            coldLoop(a, flag);
        catch (Exception e)
            msg = e.msg;
        check(msg == (flag ? "positive" : "not positive"));
    }
}
