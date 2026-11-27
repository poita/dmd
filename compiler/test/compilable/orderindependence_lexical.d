// REQUIRED_ARGS: -preview=orderIndependenceLexical
// A condition sees the declarations of the conditionals before it in the
// same scope, not its own or later ones.

// The "already defined" short-circuit idiom
template anySatisfy(alias F, T...)
{
    static foreach (Ti; T)
    {
        static if (!is(typeof(anySatisfy) == bool) && F!Ti)
            enum anySatisfy = true;
    }
    static if (!is(typeof(anySatisfy) == bool))
        enum anySatisfy = false;
}
enum isInt(T) = is(T == int);
static assert(anySatisfy!(isInt, long, int, int));
static assert(!anySatisfy!(isInt, long, char));
static assert(!anySatisfy!(isInt));

// Each condition is answered from the declarations before it
static if (!is(typeof(self))) void self() {}
static assert(is(typeof(self)));

static if (!is(typeof(b2))) enum b1 = true;
static if (!is(typeof(b1))) enum b2 = true;
static assert(is(typeof(b1)) && !is(typeof(b2)));

// A lookup from another declaration's initializer sees every conditional,
// whoever evaluates it first
enum r = is(typeof(x));
static if (r) {}
static if (true) int x;
static assert(r);

// Forward references from ordinary code still work
struct Bar { Foo foo; }
static if (true) struct Foo {}

// A function literal in a condition is part of the condition
static if (__traits(compiles, { import imports.orderindependence_c; oic(0); }))
    import imports.orderindependence_c;
else
    int oic(int);
static assert(oic(2) == 2);
