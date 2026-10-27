// What is computed from a copy of a register is what is computed from the register

struct V { float x, y; }

struct Grid
{
    uint size;
    float cs, half;
    V center(uint c) const { return V((c % size + 0.5f) * cs - half, (c / size + 0.5f) * cs - half); }
}

// the quotient c / size, of the remainder's division, is not divided again
float div1_nearest(ref const Grid g, V p, size_t n)
{
    float best = 1e30f;
    foreach (cell; 0 .. n)
    {
        const c = g.center(cast(uint) cell);
        const dx = c.x - p.x, dy = c.y - p.y;
        if (dx * dx + dy * dy < best)
            best = dx * dx + dy * dy;
    }
    return best;
}

// the register copied changes after the copy: what is computed from it is computed again
uint changedAfterCopy(uint a, uint b)
{
    uint c = a;
    uint q = c / b;
    a += 7;
    return q * 1000 + a / b;
}

void main()
{
    const g = Grid(10, 2.0f, 10.0f);
    if (div1_nearest(g, V(-9.0f, -9.0f), 25) != 0)
        assert(0);
    if (div1_nearest(g, V(-8.5f, -9.5f), 25) != 0.5f)
        assert(0);
    if (changedAfterCopy(20, 3) != 6 * 1000 + 9)
        assert(0);
}
