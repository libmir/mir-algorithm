/++
$(H1 @nogc and nothrow Parsing Utilities)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors:   Ilya Yaroshenko
Copyright: Symmetry Investments and Kaleidic Associates
+/
module mir.parse;

import mir.primitives;
import std.range.primitives: isInputRange;
import std.traits: isMutable, isFloatingPoint, isSomeChar;

/++
Performs `nothorw` and `@nogc` string to native type conversion.

Returns:
    parsed value
Throws:
    `nogc` Exception in case of parse error or non-empty remaining input.

Floating_point:
    Mir parsing supports up-to quadruple precision.
The conversion error is 0 ULP for normal numbers. 
    Subnormal numbers with an exponent greater than or equal to -512 have upper error bound equal to 1 ULP.+/
T fromString(T, C)(scope const(C)[] str)
    if (isMutable!T)
{
    import mir.utility: _expect;
    static immutable excfp = new Exception("fromString failed to parse " ~ T.stringof);

    static if (isFloatingPoint!T)
    {
        T value;
        if (_expect(fromString(str, value), true))
            return value;
        version (D_Exceptions)
            throw excfp;
        else
            assert(0);
    }
    else
    {
        static immutable excne = new Exception("fromString: remaining input is not empty after parsing " ~ T.stringof);

        T value;
        if (_expect(parse!T(str, value), true))
        {
            if (_expect(str.empty, true))
                return value;
            version (D_Exceptions)
                throw excne;
            else
                assert(0);
        }
        else
        {
            version (D_Exceptions)
                throw excfp;
            else
                assert(0);
        }
    }
}

///
version(mir_test)
@safe pure @nogc unittest
{
    assert("123".fromString!int == 123);
    static assert("-123".fromString!int == -123);

    assert("12.3".fromString!double == 12.3);
    assert("12.3".fromString!float == 12.3f);
    assert("12.3".fromString!real == 12.3L);
    assert("-12.3e-30".fromString!double == -12.3e-30);

    /// Test CTFE support  
    static assert("-12.3e-30".fromString!double == -0x1.f2f280b2414d5p-97);
    static assert("+12.3e+30".fromString!double == 0x1.367ee3119d2bap+103);

    static assert("1.448997445238699".fromString!double == 0x1.72f17f1f49aadp0);
    static if (real.mant_dig >= 64)
        static assert("1.448997445238699".fromString!real == 1.448997445238699L);

    static assert("3.518437208883201171875".fromString!float == 0x1.c25c26p+1);
    static assert("3.518437208883201171875".fromString!double == 0x1.c25c268497684p+1);
    static if (real.mant_dig >= 64)
        static assert("3.518437208883201171875".fromString!real == 3.518437208883201171875L);

//  Related DMD Issues:
// https://issues.dlang.org/show_bug.cgi?id=20951
// https://issues.dlang.org/show_bug.cgi?id=20952
// https://issues.dlang.org/show_bug.cgi?id=20953
// https://issues.dlang.org/show_bug.cgi?id=20957
// https://issues.dlang.org/show_bug.cgi?id=20963
// https://issues.dlang.org/show_bug.cgi?id=20967
}

/++
Performs `nothorw` and `@nogc` string to native type conversion.

Returns: true if success and false otherwise.
+/
bool fromString(T, C)(scope const(C)[] str, ref T value)
    if (isSomeChar!C)
{
    static if (isFloatingPoint!T)
    {
        import mir.bignum.decimal: Decimal, DecimalExponentKey, parseDecimal;
        import mir.utility: _expect;

        Decimal!256 decimal;
        DecimalExponentKey key;
        auto ret = parseDecimal(str, decimal, key);
        if (_expect(ret, true))
            value =  cast(T) decimal;
        return ret;
    }
    else
    {
        return parse!T(str, value) && str.empty;
    }
}

///
version(mir_test)
@safe pure nothrow @nogc unittest
{
    int value;
    assert("123".fromString(value) && value == 123);
}

/++
Integer parsing utilities.

Returns: true if success and false otherwise.
+/
bool parse(T : byte, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && !__traits(isUnsigned, T))
{
    int lvalue;
    auto ret = parse!(int, Range)(r, lvalue);
    value = cast(byte) lvalue;
    return ret && value == lvalue;
}
/// ditto
bool parse(T : short, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && !__traits(isUnsigned, T))
{
    int lvalue;
    auto ret = parse!(int, Range)(r, lvalue);
    value = cast(short) lvalue;
    return ret && value == lvalue;
}

/// ditto
pragma(inline, false)
bool parse(T : int, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && !__traits(isUnsigned, T))
{
    return parseSignedImpl!(int, Range)(r, value);
}

/// ditto
pragma(inline, false)
bool parse(T : long, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && !__traits(isUnsigned, T))
{
    return parseSignedImpl!(long, Range)(r, value);
}

/// ditto
bool parse(T : ubyte, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && __traits(isUnsigned, T))
{
    uint lvalue;
    auto ret = parse!(uint, Range)(r, lvalue);
    value = cast(ubyte) lvalue;
    return ret && value == lvalue;
}

/// ditto
bool parse(T : ushort, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && __traits(isUnsigned, T))
{
    uint lvalue;
    auto ret = parse!(uint, Range)(r, lvalue);
    value = cast(ushort) lvalue;
    return ret && value == lvalue;
}

/// ditto
pragma(inline, false)
bool parse(T : uint, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && __traits(isUnsigned, T))
{
    return parseUnsignedImpl!(uint, Range)(r, value);
}

/// ditto
pragma(inline, false)
bool parse(T : ulong, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && __traits(isUnsigned, T))
{
    return parseUnsignedImpl!(ulong, Range)(r, value);
}


///
version (mir_test) unittest
{
    import std.meta: AliasSeq;
    foreach (T; AliasSeq!(byte, ubyte, short, ushort, int, uint, long, ulong))
    {
        auto str = "123";
        T val;
        assert(parse(str, val));
        assert(val == 123);
        str = "0";
        assert(parse(str, val));
        assert(val == 0);
        str = "9";
        assert(parse(str, val));
        assert(val == 9);
        str = "";
        assert(!parse(str, val));
        assert(val == 0);
        str = "text";
        assert(!parse(str, val));
        assert(val == 0);
    }
}

///
version (mir_test) unittest
{
    import std.meta: AliasSeq;
    foreach (T; AliasSeq!(byte, short, int, long))
    {
        auto str = "-123";
        T val;
        assert(parse(str, val));
        assert(val == -123);
        str = "-0";
        assert(parse(str, val));
        assert(val == 0);
        str = "-9text";
        assert(parse(str, val));
        assert(val == -9);
        assert(str == "text");
        enum m = T.min + 0;
        str = m.stringof;
        assert(parse(str, val));
        assert(val == T.min);
    }
}

alias r1 = parseUnsignedImpl!(uint, string);
alias r2 = parseUnsignedImpl!(ulong, string);
alias r3 = parseSignedImpl!(int, string);
alias r4 = parseSignedImpl!(long, string);

private bool parseUnsignedImpl(T, Range)(scope ref Range r, scope ref T value)
    if(__traits(isUnsigned, T))
{
    import core.checkedint: addu, mulu;

    bool sign;
B:
    if (!r.empty)
    {
        auto f = r.front + 0u;
        if (!sign && f == '+')
        {
            r.popFront;
            sign = true;
            goto B;
        }
        uint c = f - '0';
        if (c >= 10)
            goto F;
        T x = c;
        for(;;)
        {
            r.popFront;
            if (r.empty)
                break;
            c = r.front - '0';
            if (c >= 10)
                break;
            bool overflow;
            T y = mulu(x, cast(uint)10, overflow);
            if (overflow)
                goto R;
            x = y;
            T z = addu(x, cast(uint)c, overflow);
            if (overflow)
                goto R;
            x = z;
        }
        value = x;
        return true;
    }
F:  value = 0;
R:  return false;
}

private bool parseSignedImpl(T, Range)(scope ref Range r, scope ref T value)
    if(!__traits(isUnsigned, T))
{
    import core.checkedint: negs;
    import std.traits: Unsigned;

    bool sign;
B:
    if (!r.empty)
    {
        auto f = r.front + 0u;
        if (!sign && f == '-')
        {
            r.popFront;
            sign = true;
            goto B;
        }
        auto retu = (()@trusted=>parse(r, *cast(Unsigned!T*) &value))();
        // auto retu = false;
        if (!retu)
            goto R;
        if (!sign)
        {
            if (value < 0)
                goto R;
        }
        else
        {
            if (value < 0 && value != T.min)
                goto R;
            value = -value;
        }
        return true;
    }
F:  value = 0;
R:  return false;
}
