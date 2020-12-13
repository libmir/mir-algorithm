/++
Stack-allocated decimal type.

Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.decimal;

import mir.serde: serdeProxy, serdeScoped;
import std.traits: isSomeChar;
public import mir.bignum.low_level_view: DecimalExponentKey;
import mir.bignum.low_level_view: ceilLog10Exp2;

private enum expBufferShift = 2 + ceilLog10Exp2(size_t.sizeof * 8);

/++
Stack-allocated decimal type.
Params:
    maxSize64 = count of 64bit words in coefficient
+/
@serdeScoped @serdeProxy!(const(char)[])
struct Decimal(size_t maxSize64)
    if (maxSize64 && maxSize64 <= ushort.max)
{
    import mir.bignum.integer;
    import mir.bignum.low_level_view;
    import std.traits: isMutable, isFloatingPoint;

    ///
    sizediff_t exponent;
    ///
    BigInt!maxSize64 coefficient;

    ///
    DecimalView!size_t view()
    {
        return typeof(return)(coefficient.sign, exponent, coefficient.view.unsigned);
    }

    /// ditto
    DecimalView!(const size_t) view() const
    {
        return typeof(return)(coefficient.sign, exponent, coefficient.view.unsigned);
    }

    ///
    this(C)(scope const(C)[] str) @safe pure @nogc
        if (isSomeChar!C)
    {
        DecimalExponentKey key;
        if (fromStringImpl(str, key) || key == DecimalExponentKey.nan || key == DecimalExponentKey.infinity)
            return;
        static if (__traits(compiles, () @nogc { throw new Exception("Can't parse Decimal."); }))
        {
            import mir.exception: MirException;
            throw new MirException("Can't parse Decimal!" ~ maxSize64.stringof ~ " from string `", str , "`");
        }
        else
        {
            static immutable exception = new Exception("Can't parse Decimal!" ~ maxSize64.stringof ~ ".");
            throw exception;
        }
    }

    static if (maxSize64 == 3)
    ///
    version(mir_test) @safe pure @nogc unittest
    {
        import mir.math.constant: PI;
        Decimal!2 decimal = "3.141592653589793378e-40"; // constructor
        assert(cast(double) decimal.view == double(PI) / 1e40);
    }

    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients.
    +/
    bool fromStringImpl(C)(scope const(C)[] str, out DecimalExponentKey key)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        import mir.bignum.low_level_view: DecimalView, BigUIntView, MaxWordPow10;
        auto work = DecimalView!size_t(false, 0, BigUIntView!size_t(coefficient.data));
        auto ret = work.fromStringImpl(str, key);
        coefficient.length = cast(uint) work.coefficient.coefficients.length;
        coefficient.sign = work.sign;
        exponent = work.exponent;
        return ret;
    }

    static if (maxSize64 == 3)
    ///
    version(mir_bignum_test) 
    @safe pure nothrow @nogc
    unittest
    {
        import mir.conv: to;
        Decimal!3 decimal;
        DecimalExponentKey key;

        assert(decimal.fromStringImpl("1.334", key));
        assert(cast(double) decimal.view == 1.334);
        assert(key == DecimalExponentKey.dot);

        assert(decimal.fromStringImpl("+0.334e-5"w, key));
        assert(cast(double) decimal.view == 0.334e-5);
        assert(key == DecimalExponentKey.e);

        assert(decimal.fromStringImpl("-334D-5"d, key));
        assert(cast(double) decimal.view == -334e-5);
        assert(key == DecimalExponentKey.D);

        assert(decimal.fromStringImpl("2482734692817364218734682973648217364981273648923423", key));
        assert(cast(double) decimal.view == 2482734692817364218734682973648217364981273648923423.0);
        assert(key == DecimalExponentKey.none);

        assert(decimal.fromStringImpl(".023", key));
        assert(cast(double) decimal.view == .023);
        assert(key == DecimalExponentKey.dot);

        assert(decimal.fromStringImpl("0E100", key));
        assert(cast(double) decimal.view == 0);
        assert(key == DecimalExponentKey.E);

        assert(decimal.fromStringImpl("-nan", key));
        assert(decimal.coefficient.length == 0);
        assert(cast(double) decimal.view == 0);
        assert(decimal.coefficient.sign);
        assert(key == DecimalExponentKey.nan);

        assert(decimal.fromStringImpl("inf", key));
        assert(cast(double) decimal.view == 0);
        assert(key == DecimalExponentKey.infinity);

        assert(!decimal.fromStringImpl("3.3.4", key));
        assert(!decimal.fromStringImpl("3.4.", key));
        assert(!decimal.fromStringImpl("4.", key));
        assert(!decimal.fromStringImpl(".", key));
        assert(!decimal.fromStringImpl("0.", key));
        assert(!decimal.fromStringImpl("00", key));
        assert(!decimal.fromStringImpl("0d", key));
    }

    private enum eDecimalLength = 2 + ceilLog10Exp2(coefficient.data.length * (size_t.sizeof * 8)) + expBufferShift;

    private const(C)[] toStringImpl(C = char)(ref scope return C[eDecimalLength] buffer) scope const @safe pure nothrow
        if(isSomeChar!C && isMutable!C)
    {
        import mir.utility: _expect;
        // handle special values
        if (_expect(exponent == exponent.max, false))
        {
            immutable(C)[] nan = "nan";
            immutable(C)[] ninf = "-inf";
            immutable(C)[] pinf = "+inf";
            return coefficient.length == 0 ? coefficient.sign ? ninf : pinf : nan;
        }

        size_t coefficientLength;
        if (__ctfe && size_t.sizeof == 8)
        {
            uint[coefficient.data.length * 2] data;
            foreach (i; 0 .. coefficient.length)
            {
                auto l = cast(uint)coefficient.data[i];
                auto h = cast(uint)(coefficient.data[i] >> 32);
                version (LittleEndian)
                {
                    data[i * 2 + 0] = l;
                    data[i * 2 + 1] = h;
                }
                else
                {
                    data[$ - 1 - (i * 2 + 0)] = l;
                    data[$ - 1 - (i * 2 + 1)] = h;
                }
            }
            auto work = BigUIntView!uint(data);
            work = work.topLeastSignificantPart(coefficient.length * 2).normalized;
            coefficientLength = work.toStringImpl(buffer[0 .. $ - expBufferShift]);
        }
        else
        {
            BigInt!maxSize64 work = coefficient;
            coefficientLength = work.view.unsigned.toStringImpl(buffer[0 .. $ - expBufferShift]);
        }

        assert(coefficientLength);
        sizediff_t exponent = this.exponent + coefficientLength - 1;

        if (coefficientLength > 1)
        {
            auto c = buffer[$ - expBufferShift - coefficientLength];
            buffer[$ - expBufferShift - coefficientLength] = '.';
            buffer[$ - expBufferShift - ++coefficientLength] = c;
        }

        if (coefficient.sign)
        {
            buffer[$ - expBufferShift - ++coefficientLength] = '-';
        }

        size_t exponentLength;
        {
            bool expSign = exponent < 0;
            size_t unsignedExponent = expSign ? -exponent : exponent;
            size_t i = buffer.length;

            do
            {
                buffer[--i] = cast(char)(unsignedExponent % 10 + '0');
                unsignedExponent /= 10;
            }
            while(unsignedExponent);
            if (expSign)
                buffer[--i] = '-';
            exponentLength = buffer.length - i;
        }

        buffer[$ - expBufferShift] = 'e';

        assert(exponentLength <= expBufferShift + 1);
        size_t i;
        do buffer[$ - (expBufferShift - 1) + i] = buffer[$ - exponentLength + i];
        while(++i < exponentLength);
        return buffer[$ - (expBufferShift + coefficientLength) .. $ - (expBufferShift - 1) + exponentLength];
    }

    ///
    immutable(C)[] toString(C = char)() const @safe pure nothrow
        if(isSomeChar!C && isMutable!C)
    {
        C[eDecimalLength] buffer = void;
        return toStringImpl(buffer).idup;
    }

    static if (maxSize64 == 3)
    ///
    version(mir_bignum_test) @safe pure unittest
    {
        auto str = "-3.4010447314490204552169750449563978034784726557588085989975288830070948234680e-13245";
        auto integer = Decimal!4(str);
        assert(integer.toString == str, integer.toString);

        integer = Decimal!4.init;
        assert(integer.toString == "0e0");
    }

    ///
    void toString(C = char, W)(scope ref W w) const
        if(isSomeChar!C && isMutable!C)
    {
        C[eDecimalLength] buffer = void;
        w.put(toStringImpl(buffer));
    }

    static if (maxSize64 == 3)
    /// Check @nogc toString impl
    version(mir_bignum_test) @safe pure @nogc unittest
    {
        import mir.format: stringBuf;
        auto str = "5.28238923728e9876543210";
        auto integer = Decimal!1(str);
        stringBuf buffer;
        buffer << integer;
        assert(buffer.data == str, buffer.data);
    }

    /++
    Mir parsing supports up-to quadruple precision. The conversion error is 0 ULP for normal numbers. 
    Subnormal numbers with an exponent greater than or equal to -512 have upper error bound equal to 1 ULP.    +/
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() const
        if (isFloatingPoint!T && isMutable!T)
    {
        return view.opCast!(T, wordNormalized, nonZero);
    }

    ///
    bool isNaN() const @property
    {
        return exponent == exponent.max && coefficient.length;
    }

    ///
    bool isInfinity() const @property
    {
        return exponent == exponent.max && !coefficient.length;
    }
}

///
version(mir_bignum_test) 
@safe pure nothrow @nogc
unittest
{
    import mir.conv: to;
    Decimal!3 decimal;
    DecimalExponentKey key;

    import mir.math.constant: PI;
    assert(decimal.fromStringImpl("3.141592653589793378e-10", key));
    assert(cast(double) decimal.view == double(PI) / 1e10);
    assert(key == DecimalExponentKey.e);
}


deprecated("use decimal.fromStringImpl insteade")
@trusted @nogc pure nothrow
bool parseDecimal(size_t maxSize64, C)(scope const(C)[] str, ref Decimal!maxSize64 decimal, out DecimalExponentKey key)
    if (isSomeChar!C)
{
    return decimal.fromStringImpl(str, key);
}
