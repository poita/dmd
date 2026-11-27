/*
REQUIRED_ARGS: -preview=orderIndependenceLexical
EXTRA_FILES: imports/orderindependence_lexical_b.d
TEST_OUTPUT:
---
fail_compilation/orderindependence_lexical.d(19): Error: cannot look up `pbv` in module `imports.orderindependence_lexical_b`: whether it exists depends on this lookup
fail_compilation/imports/orderindependence_lexical_b.d(3):        `pbv` may be declared by this `static if`, which is still being evaluated
fail_compilation/orderindependence_lexical.d(24): Error: cannot look up `g` in module `orderindependence_lexical`: whether it exists depends on this lookup
fail_compilation/orderindependence_lexical.d(25):        `g` may be declared by this `static if`, which is still being evaluated
fail_compilation/orderindependence_lexical.d(23):        called from here: `g2()`
fail_compilation/orderindependence_lexical.d-mixin-31(31): Error: member `late` added to struct `orderindependence_lexical.T` after its members were listed
fail_compilation/orderindependence_lexical.d(30):        members were listed here
---
*/
module orderindependence_lexical;
import imports.orderindependence_lexical_b;

// Different scopes have no source order between them
static if (!is(typeof(pbv))) int pav;

// A lookup from another declaration's semantic sees every conditional
void g(int) {}
enum r = g2();
int g2() { g(1); return 1; }
static if (r) void g(long) {}

// A mixin is not a conditional: adding a member after the members were listed
struct T
{
    enum n = __traits(allMembers, T).length;
    mixin("int late;");
}
