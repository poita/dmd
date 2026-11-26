// Order-dependence cases detected with DMD_ORDERCHECK=1 (see dmd/orderdep.d).
// Run: ./run.sh   (compares stderr against expected.txt)
module cases;
// 1. self-referential negative check
static if (!is(typeof(foo))) void foo() {}

// 2. shadowing: earlier member resolves `bar` from outer import... here via module order
struct S {
    enum x = is(typeof(bar));     // looks up bar in S (absent), finds none
    static if (true) int bar;     // inserted later
}

// 3. overload added after resolution
void g(int) {}
enum r = g2();
int g2() { g(1); return 1; }
static if (r) void g(long) {}

// 4. allMembers seal
struct T {
    enum n = __traits(allMembers, T).length;
    mixin("int late;");
}

// 5. mixin template providing a name looked up earlier
mixin template M() { int mm; }
struct U {
    enum y = is(typeof(mm));
    static if (y || !y) mixin M;
}
// 6. shadowing: S.a uses the module-level `value`, a later member hides it
int value(int x) { return x; }
struct V {
    enum a = value(1);
    static if (true) int value;
}

// not reported: forward reference to a mixin is deferred and retried
type x;
mixin("alias int type;");

// not reported: recursion through the template's own name
template Len(T...)
{
    static if (T.length == 0) enum Len = 0;
    else enum Len = 1 + Len!(T[1 .. $]);
}
static assert(Len!(int, long) == 2);
