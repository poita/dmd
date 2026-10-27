// A loop over many arrays, three of them updated, is vectorized behind the checks
// that the arrays do not overlap, and gives what the scalar loop does when they do.
module many_arrays;

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

void vecUpdate(float* s, float* dx, float* dy, const(float)* a, const(float)* b, const(float)* c,
    const(float)* d, const(float)* qx, const(float)* qy, const(int)* ix, const(int)* iy, size_t n)
{
    foreach (i; 0 .. n)
    {
        const fx = qx[i] - ix[i], fy = qy[i] - iy[i];
        const k1 = b[i] - a[i], k2 = c[i] - a[i], k3 = a[i] - b[i] - c[i] + d[i];
        dx[i] += (k1 + k3 * fy) * fx;
        dy[i] += (k2 + k3 * fx) * fy;
        s[i] += (a[i] + k1 * fx + k2 * fy) / (1.0f + dx[i] * dx[i] + dy[i] * dy[i]);
    }
}

pragma(inline, false) float id(float x) { return x; }

// the call keeps it scalar
void scalarUpdate(float* s, float* dx, float* dy, const(float)* a, const(float)* b, const(float)* c,
    const(float)* d, const(float)* qx, const(float)* qy, const(int)* ix, const(int)* iy, size_t n)
{
    foreach (i; 0 .. n)
    {
        const fx = id(qx[i]) - ix[i], fy = qy[i] - iy[i];
        const k1 = b[i] - a[i], k2 = c[i] - a[i], k3 = a[i] - b[i] - c[i] + d[i];
        dx[i] += (k1 + k3 * fy) * fx;
        dy[i] += (k2 + k3 * fx) * fy;
        s[i] += (a[i] + k1 * fx + k2 * fy) / (1.0f + dx[i] * dx[i] + dy[i] * dy[i]);
    }
}

bool same(float x, float y) { return *cast(uint*)&x == *cast(uint*)&y; }

int main()
{
    foreach (n; 0 .. 30)
        foreach (shift; 0 .. 3)
        {
            // apart, and with the outputs overlapping the inputs by shift
            auto m = new float[](11 * 40), r = new float[](11 * 40);
            auto ints = new int[](80);
            foreach (i, ref v; m)
                v = (i * 37 % 101) * 0.125f - 3;
            foreach (i, ref v; ints)
                v = cast(int)(i % 7) - 3;
            r[] = m[];
            float* p(float[] x, size_t k) { return x.ptr + k * 40 - (k < 3 ? 0 : shift); }
            vecUpdate(p(m, 0), p(m, 1), p(m, 2), p(m, 3), p(m, 4), p(m, 5), p(m, 6), p(m, 7), p(m, 8),
                ints.ptr, ints.ptr + 40, n);
            scalarUpdate(p(r, 0), p(r, 1), p(r, 2), p(r, 3), p(r, 4), p(r, 5), p(r, 6), p(r, 7), p(r, 8),
                ints.ptr, ints.ptr + 40, n);
            foreach (i; 0 .. m.length)
                check(same(m[i], r[i]));
        }
    return 0;
}
