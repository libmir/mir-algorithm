module mir.bignum.internal.parse;

/+
https://arxiv.org/abs/2101.11408
Number Parsing at a Gigabyte per Second
Daniel Lemire
+/
bool isMadeOfEightDigits()(ref const char[8] chars)
{
    pragma(inline, true);
    ulong val = (cast(ulong[1]) cast(ubyte[8]) chars)[0];
    return !((((val + 0x4646464646464646) | (val - 0x3030303030303030)) & 0x8080808080808080));
}

// ditto
uint parseEightDigits()(ref const char[8] chars)
{
    pragma(inline, true);
    ulong val = (cast(ulong[1]) cast(ubyte[8]) chars)[0];
    val = (val & 0x0F0F0F0F0F0F0F0F) * 2561 >> 8;
    val = (val & 0x00FF00FF00FF00FF) * 6553601 >> 16;
    return uint((val & 0x0000FFFF0000FFFF) * 42949672960001 >> 32);
}
