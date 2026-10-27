// REQUIRED_ARGS: -O -inline
// Calls merged because the function reads and writes no memory give the results
// of calling it each time; calls of functions that look alike but read or write
// memory, or throw, are all made.
import core.stdc.math : sinf, cosf, sqrt;

pragma(inline, false) float ssin(float x) { return sinf(x); }
pragma(inline, false) float scos(float x) { return cosf(x); }
pragma(inline, false) int sq(int x) { int y = x * x; if (y > 100) y -= 1; return y; }

__gshared int counter;
__gshared int gval;

pragma(inline, false) int writesGlobal(int x) { ++counter; return x + 1; }
pragma(inline, false) int readsGlobal(int x) { return x + gval; }
pragma(inline, false) int throughPointer(int* p) { return *p + 1; }
pragma(inline, false) int throws(int x) { if (x < 0) throw new Exception("neg"); return x * 2; }
pragma(inline, false) int loops(int x) { int s; foreach (i; 0 .. x) s += i; return s; }
pragma(inline, false) int recurses(int x) { return x <= 1 ? 1 : x * recurses(x - 1); }
pragma(inline, false) int asserts(int x) { assert(x != 7); return x; }

float rot(float a)
{
    return scos(a) * 2 + scos(a) * ssin(a) + ssin(a) - scos(a);
}

int pure2(int x) { return sq(x) + sq(x) * sq(x); }

int global2(int x)
{
    const a = readsGlobal(x);
    gval += 5;
    return a + readsGlobal(x);
}

int written2(int x) { return writesGlobal(x) + writesGlobal(x); }

int ptr2(int* p)
{
    const a = throughPointer(p);
    *p += 10;
    return a + throughPointer(p);
}

int throw2(int x)
{
    int r;
    try { r = throws(x); } catch (Exception) { r = -1; }
    return r + throws(x < 0 ? -x : x);
}

float stored(float a, int* p)
{
    const x = scos(a);
    *p = 1;
    return x + scos(a);
}

void main()
{
    int w;
    assert(stored(0.5f, &w) == 2 * cosf(0.5f) && w == 1);
    foreach (i; 0 .. 50)
    {
        const a = i * 0.37f - 7;
        assert(rot(a) == cosf(a) * 2 + cosf(a) * sinf(a) + sinf(a) - cosf(a));
    }
    assert(pure2(3) == 9 + 81);
    assert(pure2(11) == 120 + 120 * 120);

    gval = 1;
    assert(global2(10) == 11 + 16);

    counter = 0;
    assert(written2(4) == 10);
    assert(counter == 2);

    int v = 1;
    assert(ptr2(&v) == 2 + 12);

    assert(throw2(-3) == -1 + 6);
    assert(loops(5) + loops(5) == 20);
    assert(recurses(5) + recurses(5) == 240);
    assert(asserts(3) + asserts(3) == 6);
    assert(sqrt(2.0) * sqrt(2.0) == sqrt(2.0) ^^ 2);
}
