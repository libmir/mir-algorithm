/++
This module contains a collection of bit-level operations.

Authors: Ilya Yaroshenko, Phobos & LDC Authors (unittests, docs, conventions).
+/
module mir.bitop;

version(LDC)
    import ldc.intrinsics;

import mir.math.common: fastmath;

/// Right shift vallue for bit index to get element's index (5 for `uint`).
enum uint bitElemShift(T : ubyte) = 3;
/// ditto
enum uint bitElemShift(T : byte) = 3;
/// ditto
enum uint bitElemShift(T : ushort) = 4;
/// ditto
enum uint bitElemShift(T : short) = 4;
/// ditto
enum uint bitElemShift(T : uint) = 5;
/// ditto
enum uint bitElemShift(T : int) = 5;
/// ditto
enum uint bitElemShift(T : ulong) = 6;
/// ditto
enum uint bitElemShift(T : long) = 6;
static if (is(ucent))
/// ditto
enum uint bitElemShift(T : ucent) = 7;
/// ditto
static if (is(cent))
enum uint bitElemShift(T : cent) = 7;

/// Bit mask for bit index to get element's bit shift (31 for uint).
enum uint bitShiftMask(T : ubyte) = 7;
/// ditto
enum uint bitShiftMask(T : byte) = 7;
/// ditto
enum uint bitShiftMask(T : ushort) = 15;
/// ditto
enum uint bitShiftMask(T : short) = 15;
/// ditto
enum uint bitShiftMask(T : uint) = 31;
/// ditto
enum uint bitShiftMask(T : int) = 31;
/// ditto
enum uint bitShiftMask(T : ulong) = 63;
/// ditto
enum uint bitShiftMask(T : long) = 63;
static if (is(ucent))
/// ditto
enum uint bitShiftMask(T : ucent) = 127;
static if (is(cent))
/// ditto
enum uint bitShiftMask(T : cent) = 127;

// no effect on this function, but better for optimization of other @fastmath code that uses this
@fastmath:


/++
+/
T bitCountUntil(T)(T value, T popcnt)
    if (__traits(isUnsigned, T))
{
    alias S = typeof(1 + value);
    S mask = S(-1) << T.sizeof * 4;
    foreach_reverse (s; Iota!(0, bitElemShift!T - 2))
    {{
        enum shist = 1 << s;
        popcnt -= llvm_ctpop(cast(T)(a & ~mask));
        if (popcnt == 0)
            goto R;
        if (popcnt < 0)
            mask >>= shist;
        else
        if (popcnt > 0)
            mask <<= shist;
    }}
R:
    return llvm_ctpop(cast(T)~mask);
}

///
unittest
{
}


/++
Tests the bit.
Returns:
     A non-zero value if the bit was set, and a zero
     if it was clear.
+/
auto bt(Field, T = typeof(Field.init[size_t.init]))(auto ref Field p, size_t bitnum)
    if (__traits(isIntegral, T))
{
    auto index = bitnum >> bitElemShift!T;
    auto mask = T(1) << (bitnum & bitShiftMask!T);
    return p[index] & mask;
}

///
@system pure unittest
{
    size_t[2] array;

    array[0] = 2;
    array[1] = 0x100;

    assert(bt(array.ptr, 1));
    assert(array[0] == 2);
    assert(array[1] == 0x100);
}

/++
Tests and assign the bit.
Returns:
     A non-zero value if the bit was set, and a zero if it was clear.
+/
auto bta(Field, T = typeof(Field.init[size_t.init]))(auto ref Field p, size_t bitnum, bool value)
    if (__traits(isIntegral, T))
{
    auto index = bitnum >> bitElemShift!T;
    auto shift = bitnum & bitShiftMask!T;
    auto mask = T(1) << shift;
    static if (__traits(compiles, &p[size_t.init]))
    {
        auto qp = &p[index];
        auto q = *qp;
        auto ret = q & mask;
        *qp = cast(T)((q & ~mask) ^ (T(value) << shift));
    }
    else
    {
        auto q = p[index];
        auto ret = q & mask;
        p[index] = cast(T)((q & ~mask) ^ (T(value) << shift));
    }
    return ret;    
}

/++
Tests and complements the bit.
Returns:
     A non-zero value if the bit was set, and a zero if it was clear.
+/
auto btc(Field, T = typeof(Field.init[size_t.init]))(auto ref Field p, size_t bitnum)
    if (__traits(isIntegral, T))
{
    auto index = bitnum >> bitElemShift!T;
    auto mask = T(1) << (bitnum & bitShiftMask!T);
    static if (__traits(compiles, &p[size_t.init]))
    {
        auto qp = &p[index];
        auto q = *qp;
        auto ret = q & mask;
        *qp = cast(T)(q ^ mask);
    }
    else
    {
        auto q = p[index];
        auto ret = q & mask;
        p[index] = cast(T)(q ^ mask);
    }
    return ret;
}

/++
Tests and resets (sets to 0) the bit.
Returns:
     A non-zero value if the bit was set, and a zero if it was clear.
+/
auto btr(Field, T = typeof(Field.init[size_t.init]))(auto ref Field p, size_t bitnum)
    if (__traits(isIntegral, T))
{
    auto index = bitnum >> bitElemShift!T;
    auto mask = T(1) << (bitnum & bitShiftMask!T);
    static if (__traits(compiles, &p[size_t.init]))
    {
        auto qp = &p[index];
        auto q = *qp;
        auto ret = q & mask;
        *qp = cast(T)(q & ~mask);
    }
    else
    {
        auto q = p[index];
        auto ret = q & mask;
        p[index] = cast(T)(q & ~mask);
    }
    return ret;
}

/++
Tests and sets the bit.
Params:
p = a non-NULL field / pointer to an array of unsigned integers.
bitnum = a bit number, starting with bit 0 of p[0],
and progressing. It addresses bits like the expression:
---
p[index / (T.sizeof*8)] & (1 << (index & ((T.sizeof*8) - 1)))
---
Returns:
     A non-zero value if the bit was set, and a zero if it was clear.
+/
auto bts(Field, T = typeof(Field.init[size_t.init]))(auto ref Field p, size_t bitnum)
    if (__traits(isIntegral, T))
{
    auto index = bitnum >> bitElemShift!T;
    auto mask = T(1) << (bitnum & bitShiftMask!T);
    static if (__traits(compiles, &p[size_t.init]))
    {
        auto qp = &p[index];
        auto q = *qp;
        auto ret = q & mask;
        *qp = cast(T)(q | mask);
    }
    else
    {
        auto q = p[index];
        auto ret = q & mask;
        p[index] = cast(T)(q | mask);
    }
    return ret;
}

///
@system pure unittest
{
    size_t[2] array;

    array[0] = 2;
    array[1] = 0x100;

    assert(btc(array.ptr, 35) == 0);
    if (size_t.sizeof == 8)
    {
        assert(array[0] == 0x8_0000_0002);
        assert(array[1] == 0x100);
    }
    else
    {
        assert(array[0] == 2);
        assert(array[1] == 0x108);
    }

    assert(btc(array.ptr, 35));
    assert(array[0] == 2);
    assert(array[1] == 0x100);

    assert(bts(array.ptr, 35) == 0);
    if (size_t.sizeof == 8)
    {
        assert(array[0] == 0x8_0000_0002);
        assert(array[1] == 0x100);
    }
    else
    {
        assert(array[0] == 2);
        assert(array[1] == 0x108);
    }

    assert(btr(array.ptr, 35));
    assert(array[0] == 2);
    assert(array[1] == 0x100);
}

/// The 'ctpop' family of intrinsics counts the number of bits set in a value.
T ctpop(T)(T src)
    if (__traits(isIntegral, T))
{
    version(LDC) if (!__ctfe)
        return llvm_ctpop(src);
    import core.bitop: popcnt;
    return cast(T) popcnt(src);
}

/++
The 'ctlz' family of intrinsic functions counts the number of leading zeros in a variable.
Result is undefined if the argument is zero.
+/
T ctlz(T)(T src)
    if (__traits(isIntegral, T))
{
    version(LDC) if (!__ctfe)
        return llvm_ctlz(src, true);
    import core.bitop: bsf;
    return cast(T) bsf(src);
}

/++
The 'cttz' family of intrinsic functions counts the number of trailing zeros.
Result is undefined if the argument is zero.
+/
T cttz(T)(T src)
    if (__traits(isIntegral, T))
{
    version(LDC) if (!__ctfe)
        return llvm_cttz(src, true);
    import core.bitop: bsf;
    return cast(T) bsf(src);
}
