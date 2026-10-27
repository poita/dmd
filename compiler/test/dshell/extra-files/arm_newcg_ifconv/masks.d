// A mask keeping every bit a value can have is not applied

// the comparison's 0 or 1 is not masked with 1 again
bool ops3_orEquals(uint x)
{
    bool c;
    c |= x == 3;
    return c;
}

// a byte is not masked with 0xFF
uint ops2_lowByte(const ref ubyte b)
{
    return b & 0xFF;
}

// a mask clearing bits the value may have stays
uint lowBits(const ref ubyte b)
{
    return b & 0x7F;
}

void main()
{
    if (!ops3_orEquals(3) || ops3_orEquals(4))
        assert(0);
    ubyte b = 0xF3;
    if (ops2_lowByte(b) != 0xF3 || lowBits(b) != 0x73)
        assert(0);
}
