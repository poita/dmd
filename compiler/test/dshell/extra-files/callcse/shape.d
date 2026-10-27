module shape;

import core.stdc.math : sinf, cosf;

pragma(inline, false) float ssin(float x) { return sinf(x); }
pragma(inline, false) float scos(float x) { return cosf(x); }

__gshared float g;
pragma(inline, false) float reader(float x) { return x + g; }

// Two calls of each read-none wrapper become one
float merged(float a) { return scos(a) * 2 + scos(a) * ssin(a) + ssin(a); }

// The libm functions themselves
float libm(float a) { return sinf(a) * a + sinf(a) * 3; }

// A function reading a global is called each time
float kept(float a) { return reader(a) * reader(a); }

// A store between the calls changes nothing they read
float stored(float a, int* p)
{
    const x = scos(a);
    *p = 1;
    return x + scos(a);
}
