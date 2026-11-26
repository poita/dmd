/*
REQUIRED_ARGS: -preview=orderIndependence
EXTRA_FILES: imports/orderindependence_b.d
TEST_OUTPUT:
---
fail_compilation/orderindependence.d(33): Error: cannot look up `pbv` in module `imports.orderindependence_b`: whether it exists depends on this lookup
fail_compilation/imports/orderindependence_b.d(3):        `pbv` may be declared by this `static if`, which is still being evaluated
fail_compilation/orderindependence.d(26): Error: cannot look up `self` in module `orderindependence`: whether it exists depends on this lookup
fail_compilation/orderindependence.d(26):        `self` may be declared by this `static if`, which is still being evaluated
fail_compilation/orderindependence.d(30): Error: cannot look up `b1` in module `orderindependence`: whether it exists depends on this lookup
fail_compilation/orderindependence.d(29):        `b1` may be declared by this `static if`, which is still being evaluated
fail_compilation/orderindependence.d(38): Error: cannot look up `g` in module `orderindependence`: whether it exists depends on this lookup
fail_compilation/orderindependence.d(39):        `g` may be declared by this `static if`, which is still being evaluated
fail_compilation/orderindependence.d(37):        called from here: `g2()`
fail_compilation/orderindependence.d-mixin-45(45): Error: member `late` added to struct `orderindependence.T` after its members were listed
fail_compilation/orderindependence.d(44):        members were listed here
fail_compilation/orderindependence.d(53): Error: `mm` made visible here changes the result of an earlier lookup
fail_compilation/orderindependence.d(52):        `mm` was looked up in struct `orderindependence.U` here in a speculative context, and not found
fail_compilation/orderindependence.d(53): Error: mixin `orderindependence.U.M!()` error instantiating
---
*/
module orderindependence;
import imports.orderindependence_b;

// A `static if` that tests for the name it declares
static if (!is(typeof(self))) void self() {}

// Two declarations that each exist only if the other does not
static if (!is(typeof(b2))) enum b1 = true;
static if (!is(typeof(b1))) enum b2 = true;

// The same across modules: the result used to depend on the command line order
static if (!is(typeof(pbv))) int pav;

// An overload that may change the result of the call deciding whether it exists
void g(int) {}
enum r = g2();
int g2() { g(1); return 1; }
static if (r) void g(long) {}

// A string mixin adds a member after the members were listed
struct T
{
    enum n = __traits(allMembers, T).length;
    mixin("int late;");
}

// A mixin template declares a name already looked up
mixin template M() { int mm; }
struct U
{
    enum y = is(typeof(mm));
    mixin M;
}
