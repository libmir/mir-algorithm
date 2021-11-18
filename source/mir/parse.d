/++
$(H1 @nogc and nothrow Parsing Utilities)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
+/
module mir.parse;

/// `mir.conv: to` extension.
version(mir_test)
@safe pure @nogc
unittest
{
    import mir.conv: to;

    assert("123.0".to!double == 123);
    assert("123".to!int == 123);
    assert("123".to!byte == 123);

    import mir.small_string;
    alias S = SmallString!32;
    assert(S("123.0").to!double == 123);
    assert(S("123.").to!double == 123.);
    assert(S(".123").to!double == .123);
    assert(S("123").to!(immutable int) == 123);
}

import mir.primitives;
import std.traits: isMutable, isFloatingPoint, isSomeChar;

/++
Performs `nothrow` and `@nogc` string to native type conversion.

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
version(mir_bignum_test)
@safe pure @nogc unittest
{
    assert("123".fromString!int == 123);
    static assert("-123".fromString!int == -123);

    assert(".5".fromString!float == .5);
    assert("12.3".fromString!double == 12.3);
    assert("12.3".fromString!float == 12.3f);
    assert("12.3".fromString!real == 12.3L);
    assert("-12.3e-30".fromString!double == -12.3e-30);
    assert("2.9802322387695312E-8".fromString!double == 2.9802322387695312E-8);

    // default support of underscores
    assert("123_456.789_012".fromString!double == 123_456.789_012);
    assert("12_34_56_78_90_12e-6".fromString!double == 123_456.789_012);

    // default support of leading zeros
    assert("010".fromString!double == 10.0);
    assert("000010".fromString!double == 10.0);
    assert("0000.10".fromString!double == 0.1);
    assert("0000e10".fromString!double == 0);

    /// Test CTFE support  
    static assert("-12.3e-30".fromString!double == -0x1.f2f280b2414d5p-97);
    static assert("+12.3e+30".fromString!double == 0x1.367ee3119d2bap+103);

    static assert("1.448997445238699".fromString!double == 0x1.72f17f1f49aadp0);
    static if (real.mant_dig >= 64)
        static assert("1.448997445238699".fromString!real == 1.448997445238699L);

    static assert("3.518437208883201171875".fromString!float == 0x1.c25c26p+1);
    static assert("3.518437208883201171875".fromString!double == 0x1.c25c268497684p+1);
    static if (real.mant_dig >= 64)
        static assert("3.518437208883201171875".fromString!real == 0xe.12e13424bb4232fp-2L);    

//  Related DMD Issues:
// https://issues.dlang.org/show_bug.cgi?id=20951
// https://issues.dlang.org/show_bug.cgi?id=20952
// https://issues.dlang.org/show_bug.cgi?id=20953
// https://issues.dlang.org/show_bug.cgi?id=20967
}

// unittest
// {
//     import std.stdio;
//     import mir.conv;
//     import mir.format;
//     text(double.min_normal).writeln;
//     text(double.min_normal * double.epsilon).writeln;
//     assert("2.2250738585072014e-308".fromString!double == double.min_normal);
//     assert("5e-324".fromString!double == double.min_normal * double.epsilon);
//     assert("2.5e-324".fromString!double == double.min_normal * double.epsilon);
// }

version(mir_bignum_test)
@safe pure unittest
{
    import std.exception: assertThrown;
    assertThrown("1_".fromString!float);
    assertThrown("1__2".fromString!float);
    assertThrown("_1".fromString!float);
    assertThrown("123_.456".fromString!float);
    assertThrown("123_e0".fromString!float);
    assertThrown("123._456".fromString!float);
    assertThrown("12__34.56".fromString!float);
    assertThrown("123.456_".fromString!float);
    assertThrown("-_123.456".fromString!float);
    assertThrown("_123.456".fromString!float);
}

/++
Performs `nothrow` and `@nogc` string to native type conversion.

Returns: true if success and false otherwise.
+/
bool fromString(T, C)(scope const(C)[] str, ref T value)
    if (isSomeChar!C)
{
    static if (isFloatingPoint!T)
    {
        import mir.bignum.decimal: Decimal, DecimalExponentKey;
        import mir.utility: _expect;

        Decimal!256 decimal = void;
        DecimalExponentKey key;
        auto ret = decimal.fromStringImpl(str, key);
        if (_expect(ret, true))
        {
            switch(key) with(DecimalExponentKey)
            {
                case nan: value = decimal.coefficient.sign ? -T.nan : T.nan; break;
                case infinity: value = decimal.coefficient.sign ? -T.infinity : T.infinity; break;
                default: value =  cast(T) decimal; break;
            }
        }
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
Single character parsing utilities.

Returns: true if success and false otherwise.
+/
bool parse(T, Range)(scope ref Range r, scope ref T value)
    if (isInputRange!Range && isSomeChar!T)
{
    if (r.empty)
        return false;
    value = r.front;
    r.popFront;
    return true;
}

///
version(mir_test) @safe pure nothrow @nogc
unittest
{
    auto s = "str";
    char c;
    assert(parse(s, c));
    assert(c == 's');
    assert(s == "tr");
}

/++
Integer parsing utilities.

Returns: true if success and false otherwise.
+/
bool parse(T, Range)(scope ref Range r, scope ref T value)
    if ((is(T == byte) || is(T == short)) && isInputRange!Range && !__traits(isUnsigned, T))
{
    int lvalue;
    auto ret = parse!(int, Range)(r, lvalue);
    value = cast(T) lvalue;
    return ret && value == lvalue;
}

/// ditto
bool parse(T, Range)(scope ref Range r, scope ref T value)
    if (is(T == int) && isInputRange!Range && !__traits(isUnsigned, T))
{
    version(LDC) pragma(inline, true);
    return parseSignedImpl!(int, Range)(r, value);
}

/// ditto
bool parse(T, Range)(scope ref Range r, scope ref T value)
    if (is(T == long) && isInputRange!Range && !__traits(isUnsigned, T))
{
    version(LDC) pragma(inline, true);
    return parseSignedImpl!(long, Range)(r, value);
}

/// ditto
bool parse(T, Range)(scope ref Range r, scope ref T value)
    if ((is(T == ubyte) || is(T == ushort)) && isInputRange!Range && __traits(isUnsigned, T))
{
    uint lvalue;
    auto ret = parse!(uint, Range)(r, lvalue);
    value = cast(T) lvalue;
    return ret && value == lvalue;
}

/// ditto
bool parse(T, Range)(scope ref Range r, scope ref T value)
    if (is(T == uint) && isInputRange!Range && __traits(isUnsigned, T))
{
    version(LDC) pragma(inline, true);
    return parseUnsignedImpl!(uint, Range)(r, value);
}

/// ditto
bool parse(T, Range)(scope ref Range r, scope ref T value)
    if (is(T == ulong) && isInputRange!Range && __traits(isUnsigned, T))
{
    version(LDC) pragma(inline, true);
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

private bool parseUnsignedImpl(T, Range)(scope ref Range r, scope ref T value)
    if(__traits(isUnsigned, T))
{
    version(LDC) pragma(inline, true);
    import mir.checkedint: addu, mulu;

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
    version(LDC) pragma(inline, true);
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
