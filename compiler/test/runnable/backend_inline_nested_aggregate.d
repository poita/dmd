/* REQUIRED_ARGS: -O
 */
// The member functions of an aggregate nested in a function reach the function's
// frame, whose layout the backend inliner must not assume before the function is
// compiled.

void dtorOfNestedStruct()
{
    int local;
    struct HasDtor
    {
        ~this() { ++local; }
    }
    {
        HasDtor[4] a = HasDtor();
        assert(local == 1);
    }
    assert(local == 5);
}

void methodOfNestedClass()
{
    int a = 1, b = 2, c = 3;
    class C
    {
        int sum() { return a + b * 10 + c * 100; }
    }
    auto o = new C;
    assert(o.sum() == 321);
}

int structNestedInFunction()
{
    int x = 7, y = 9;
    struct S
    {
        int get() { return x * 100 + y; }
        void set(int v) { y = v; }
    }
    S s;
    s.set(4);
    return s.get();
}

void main()
{
    dtorOfNestedStruct();
    methodOfNestedClass();
    assert(structNestedInFunction() == 704);
}
