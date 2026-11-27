// REQUIRED_ARGS: -preview=orderIndependence

// https://github.com/dlang/dmd/issues/18151
const FOO_VER = 2;
static if (FOO_VER >= 2)
struct Bar
{
    Foo foo;
}
static if (FOO_VER >= 1)
struct Foo { }

// A member declared later by a `static if` shadows the module-level symbol
int value(int x) { return x; }
struct V
{
    enum isMember = is(typeof(value) == int);
    static if (true) int value;
}
static assert(V.isMember);

// Forcing goes through nested `static if` and `static foreach`
struct W
{
    enum hasB = is(typeof(b));
    static if (true)
    {
        static foreach (i; 0 .. 1)
            static if (i == 0) int b;
    }
}
static assert(W.hasB);

// An overload declared later by a `static if` takes part in overload resolution
void h(int) {}
long h(long) { return 1; }
static if (true) int h(long, int) { return 2; }
enum hn = h(1L, 1);

// Forward reference to a string mixin is deferred, not an error
type x;
mixin("alias int type;");

// Recursion through the template's own name
template Len(T...)
{
    static if (T.length == 0) enum Len = 0;
    else enum Len = 1 + Len!(T[1 .. $]);
}
static assert(Len!(int, long) == 2);

// A module import in a condition's body does not hide a symbol that the
// condition found through a closer import
struct ImportInBody(T)
{
    static if (__traits(compiles, { import imports.orderindependence_c; auto x = oic(T.init); }))
    {
        import imports.orderindependence_c;
        int f() { return oic(1); }
    }
}
alias ImportInBodyInt = ImportInBody!int;
static assert(ImportInBodyInt.init.f() == 1);
