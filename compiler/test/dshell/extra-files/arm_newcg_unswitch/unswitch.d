// Functions named keep_... have a loop whose branch on a parameter that the loop
// does not change is taken out of it; the result is checked by main.

pragma(inline, false)
void keep_stores(int* a, int* b, size_t n, bool flag)
{
    foreach (i; 0 .. n)
    {
        if (flag)
            a[i] = cast(int) i;
        else
            b[i] = cast(int) (i * 3);
    }
}

pragma(inline, false)
int keep_sum(const(int)[] a, int mode)
{
    int s;
    foreach (x; a)
    {
        if (mode > 2)
            s += x;
        else
            s ^= x;
    }
    return s;
}

int main()
{
    int[4] a, b;
    keep_stores(a.ptr, b.ptr, 4, true);
    keep_stores(a.ptr, b.ptr, 4, false);
    if (a != [0, 1, 2, 3] || b != [0, 3, 6, 9])
        return 1;
    keep_stores(null, null, 0, true);
    if (keep_sum([1, 2, 4], 3) != 7 || keep_sum([1, 3], 0) != 2 || keep_sum([], 5) != 0)
        return 1;
    return 0;
}
