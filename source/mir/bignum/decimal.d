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

private enum expBufferLength = 2 + ceilLog10Exp2(size_t.sizeof * 8);
private static immutable C[9] zerosImpl(C) = "0.00000.0";

/++
Stack-allocated decimal type.
Params:
    maxSize64 = count of 64bit words in coefficient
+/
@serdeScoped @serdeProxy!(const(char)[])
struct Decimal(size_t maxSize64)
    if (maxSize64 && maxSize64 <= ushort.max)
{
    import mir.format: NumericSpec;
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
        assert(cast(double) decimal == double(PI) / 1e40);
    }

    /++
    Constructs Decimal from the floating point number using the $(HTTPS https://github.com/ulfjack/ryu, Ryu algorithm).

    The number is the shortest decimal representation that being converted back would result the same floating-point number.
    +/
    this(T)(const T x)
        if (isFloatingPoint!T && maxSize64 >= 1 + (T.mant_dig >= 64))
    {
        import mir.bignum.internal.ryu.generic_128: genericBinaryToDecimal;
        this = genericBinaryToDecimal(x);
    }
    
    static if (maxSize64 == 3)
    ///
    version(mir_bignum_test)
    @safe pure nothrow @nogc
    unittest
    {
        // float and double can be used to construct Decimal of any length
        auto decimal64 = Decimal!1(-1.235e-7);
        assert(decimal64.exponent == -10);
        assert(decimal64.coefficient == -1235);

        // real number may need Decimal at least length of 2
        auto decimal128 = Decimal!2(-1.235e-7L);
        assert(decimal128.exponent == -10);
        assert(decimal128.coefficient == -1235);

        decimal128 = Decimal!2(1234e3f);
        assert(decimal128.exponent == 3);
        assert(decimal128.coefficient == 1234);
    }

    ///
    ref opAssign(size_t rhsMaxSize64)(auto ref scope const Decimal!rhsMaxSize64 rhs) return
        if (rhsMaxSize64 < maxSize64)
    {
        this.exponent = rhs.exponent;
        this.coefficient = rhs.coefficient;
        return this;
    }

    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients.
    +/
    bool fromStringImpl(C, bool allowSpecialValues = true, bool allowDotOnBounds = true, bool allowDExponent = true, bool allowStartingPlus = true, bool checkEmpty = true)(scope const(C)[] str, out DecimalExponentKey key)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        enum optimize = size_t.sizeof == 8 && maxSize64 == 1;
        version(LDC)
        {
            static if (optimize || (allowSpecialValues && allowDExponent && allowStartingPlus && checkEmpty) == false)
                pragma(inline, true);
        }
        static if (optimize)
        {
            import mir.utility: _expect;
            static if (checkEmpty)
            {
                if (_expect(str.length == 0, false))
                    return false;
            }

            coefficient.sign = str[0] == '-';
            if (coefficient.sign)
            {
                str = str[1 .. $];
                if (_expect(str.length == 0, false))
                    return false;
            }
            else
            static if (allowStartingPlus)
            {
                if (_expect(str[0] == '+', false))
                {
                    str = str[1 .. $];
                    if (_expect(str.length == 0, false))
                        return false;
                }
            }

            uint d = str[0] - '0';
            str = str[1 .. $];
            exponent = 0;

            ulong v;
            uint afterDot;
            bool dot;

            if (d == 0)
            {
                if (str.length == 0)
                    goto R;
                if (str[0] == '0')
                    return false;
                goto S;
            }

            if (d < 10)
            {
                goto S;
            }

            static if (allowDotOnBounds)
            {
                if (d == '.' - '0')
                {
                    if (str.length == 0)
                        return false;
                    key = DecimalExponentKey.dot;
                    dot = true;
                    goto F;
                }
            }

            static if (allowSpecialValues)
            {
                goto NI;
            }
            else
            {
                return false;
            }

            F: for(;;)
            {
                d = str[0] - '0';
                str = str[1 .. $];

                if (_expect(d <= 10, true))
                {
                    {
                        import core.checkedint: addu, mulu;
                        bool overflow;
                        v = mulu(v, cast(uint)10, overflow);
                        if (overflow)
                            break;
                    }
                S:
                    v += d;
                    afterDot += dot;
                    if (str.length)
                        continue;
                E:
                    exponent -= afterDot;
                R:
                    coefficient.data[0] = v;
                    coefficient.length = v != 0;
                    return true;
                }
                switch (d)
                {
                    D:
                    case DecimalExponentKey.dot:
                        if (dot)
                            break;
                        key = cast(DecimalExponentKey)d;
                        dot = true;
                        if (str.length)
                            continue;
                        static if (allowDotOnBounds)
                        {
                            goto R;
                        }
                        else
                        {
                            break;
                        }
                    static if (allowDExponent)
                    {
                        case DecimalExponentKey.d:
                        case DecimalExponentKey.D:
                            goto case DecimalExponentKey.e;
                    }
                    case DecimalExponentKey.e:
                    case DecimalExponentKey.E:
                        key = cast(DecimalExponentKey)d;
                        import mir.parse: parse;
                        if (parse(str, exponent) && str.length == 0)
                            goto E;
                        break;
                    default:
                }
                break;
            }
            return false;
            static if (allowSpecialValues)
            {
            NI:
                exponent = exponent.max;
                if (str.length == 2)
                {
                    auto stail = cast(C[2])str[0 .. 2];
                    if (d == 'i' - '0' && stail == cast(C[2])"nf" || d == 'I' - '0' && (stail == cast(C[2])"nf" || stail == cast(C[2])"NF"))
                    {
                        key = DecimalExponentKey.infinity;
                        goto R;
                    }
                    if (d == 'n' - '0' && stail == cast(C[2])"an" || d == 'N' - '0' && (stail == cast(C[2])"aN" || stail == cast(C[2])"AN"))
                    {
                        v = 1;
                        key = DecimalExponentKey.nan;
                        goto R;
                    }
                }
                return false;
            }
        }
        else
        {
            import mir.bignum.low_level_view: DecimalView, BigUIntView, MaxWordPow10;
            auto work = DecimalView!size_t(false, 0, BigUIntView!size_t(coefficient.data));
            auto ret = work.fromStringImpl!(C, allowSpecialValues, allowDExponent, allowStartingPlus)(str, key);
            coefficient.length = cast(uint) work.coefficient.coefficients.length;
            coefficient.sign = work.sign;
            exponent = work.exponent;
            return ret;
        }
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
        assert(key == DecimalExponentKey.dot);
        assert(cast(double) decimal == 1.334);

        assert(decimal.fromStringImpl("+0.334e-5"w, key));
        assert(key == DecimalExponentKey.e);
        assert(cast(double) decimal == 0.334e-5);

        assert(decimal.fromStringImpl("-334D-5"d, key));
        assert(key == DecimalExponentKey.D);
        assert(cast(double) decimal == -334e-5);

        assert(decimal.fromStringImpl("2482734692817364218734682973648217364981273648923423", key));
        assert(key == DecimalExponentKey.none);
        assert(cast(double) decimal == 2482734692817364218734682973648217364981273648923423.0);

        assert(decimal.fromStringImpl(".023", key));
        assert(key == DecimalExponentKey.dot);
        assert(cast(double) decimal == .023);

        assert(decimal.fromStringImpl("0E100", key));
        assert(key == DecimalExponentKey.E);
        assert(cast(double) decimal == 0);

        foreach (str; ["-nan", "-NaN", "-NAN"])
        {
            assert(decimal.fromStringImpl(str, key));
            assert(decimal.coefficient.length > 0);
            assert(decimal.exponent == decimal.exponent.max);
            assert(decimal.coefficient.sign);
            assert(key == DecimalExponentKey.nan);
            assert(cast(double) decimal != cast(double) decimal);
        }

        foreach (str; ["inf", "Inf", "INF"])
        {
            assert(decimal.fromStringImpl(str, key));
            assert(decimal.coefficient.length == 0);
            assert(decimal.exponent == decimal.exponent.max);
            assert(key == DecimalExponentKey.infinity);
            assert(cast(double) decimal == double.infinity);
        }

        assert(decimal.fromStringImpl("-inf", key));
        assert(decimal.coefficient.length == 0);
        assert(decimal.exponent == decimal.exponent.max);
        assert(key == DecimalExponentKey.infinity);
        assert(cast(double) decimal == -double.infinity);

        assert(!decimal.fromStringImpl("3.3.4", key));
        assert(!decimal.fromStringImpl("3.4.", key));
        assert(decimal.fromStringImpl("4.", key));
        assert(!decimal.fromStringImpl(".", key));
        assert(decimal.fromStringImpl("0.", key));
        assert(!decimal.fromStringImpl("00", key));
        assert(!decimal.fromStringImpl("0d", key));
    }

    static if (maxSize64 == 3)
    version(mir_bignum_test)
    // @safe pure nothrow @nogc
    unittest
    {
        import mir.conv: to;
        Decimal!1 decimal;
        DecimalExponentKey key;

        assert(decimal.fromStringImpl("1.334", key));
        assert(key == DecimalExponentKey.dot);
        assert(cast(double) decimal == 1.334);

        assert(decimal.fromStringImpl("+0.334e-5"w, key));
        assert(key == DecimalExponentKey.e);
        assert(cast(double) decimal == 0.334e-5);

        assert(decimal.fromStringImpl("-334D-5"d, key));
        assert(key == DecimalExponentKey.D);
        assert(cast(double) decimal == -334e-5);

        assert(!decimal.fromStringImpl("2482734692817364218734682973648217364981273648923423", key));

        assert(decimal.fromStringImpl(".023", key));
        assert(key == DecimalExponentKey.dot);
        assert(cast(double) decimal == .023);

        assert(decimal.fromStringImpl("0E100", key));
        assert(key == DecimalExponentKey.E);
        assert(cast(double) decimal == 0);

        foreach (str; ["-nan", "-NaN", "-NAN"])
        {
            assert(decimal.fromStringImpl(str, key));
            assert(decimal.coefficient.length > 0);
            assert(decimal.exponent == decimal.exponent.max);
            assert(decimal.coefficient.sign);
            assert(key == DecimalExponentKey.nan);
            assert(cast(double) decimal != cast(double) decimal);
        }

        foreach (str; ["inf", "Inf", "INF"])
        {
            assert(decimal.fromStringImpl(str, key));
            assert(decimal.coefficient.length == 0);
            assert(decimal.exponent == decimal.exponent.max);
            assert(key == DecimalExponentKey.infinity);
            assert(cast(double) decimal == double.infinity);
        }

        assert(decimal.fromStringImpl("-inf", key));
        assert(decimal.coefficient.length == 0);
        assert(decimal.exponent == decimal.exponent.max);
        assert(key == DecimalExponentKey.infinity);
        assert(cast(double) decimal == -double.infinity);

        assert(!decimal.fromStringImpl("3.3.4", key));
        assert(!decimal.fromStringImpl("3.4.", key));
        assert(decimal.fromStringImpl("4.", key));
        assert(!decimal.fromStringImpl(".", key));
        assert(decimal.fromStringImpl("0.", key));
        assert(!decimal.fromStringImpl("00", key));
        assert(!decimal.fromStringImpl("0d", key));
    }

    private enum coefficientBufferLength = 2 + ceilLog10Exp2(coefficient.data.length * (size_t.sizeof * 8)); // including dot and sign
    private enum eDecimalLength = coefficientBufferLength + expBufferLength;

    ///
    immutable(C)[] toString(C = char)(NumericSpec spec = NumericSpec.init) const @safe pure nothrow
        if(isSomeChar!C && isMutable!C)
    {
        import mir.appender: UnsafeArrayBuffer;
        C[eDecimalLength] data = void;
        auto buffer = UnsafeArrayBuffer!C(data);
        toString(buffer, spec);
        return buffer.data.idup;
    }

    static if (maxSize64 == 3)
    ///
    version(mir_bignum_test) @safe pure unittest
    {
        auto str = "-3.4010447314490204552169750449563978034784726557588085989975288830070948234680e-13245";
        auto decimal = Decimal!4(str);
        assert(decimal.toString == str, decimal.toString);

        decimal = Decimal!4.init;
        assert(decimal.toString == "0.0");
    }

    ///
    void toString(C = char, W)(scope ref W w, NumericSpec spec = NumericSpec.init) const
        if(isSomeChar!C && isMutable!C)
    {
        assert(spec.format == NumericSpec.Format.exponent || spec.format == NumericSpec.Format.human);
        import mir.utility: _expect;
        // handle special values
        if (_expect(exponent == exponent.max, false))
        {
            static immutable C[3] nan = "nan";
            static immutable C[4] ninf = "-inf";
            static immutable C[4] pinf = "+inf";
            w.put(coefficient.length == 0 ? coefficient.sign ? ninf[] : pinf[] : nan[]);
            return;
        }

        C[coefficientBufferLength + 16] buffer0 = void;
        auto buffer = buffer0[0 .. $ - 16];

        size_t coefficientLength;
        static if (size_t.sizeof == 8)
        {
            if (__ctfe)
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
                coefficientLength = work.toStringImpl(buffer);
            }
            else
            {
                BigInt!maxSize64 work = coefficient;
                coefficientLength = work.view.unsigned.toStringImpl(buffer);
            }
        }
        else
        {
            BigInt!maxSize64 work = coefficient;
            coefficientLength = work.view.unsigned.toStringImpl(buffer);
        }

        C[1] sign = coefficient.sign ? "-" : "+";
        bool addSign = coefficient.sign || spec.plus;
        sizediff_t s = this.exponent + coefficientLength;

        alias zeros = zerosImpl!C;

        if (spec.format == NumericSpec.Format.human)
        {
            if (!spec.separatorCount)
                spec.separatorCount = 3;
            void putL(scope const(C)[] b)
            {
                assert(b.length);

                if (addSign)
                    w.put(sign[]);

                auto r = b.length % spec.separatorCount;
                if (r == 0)
                    r = spec.separatorCount;
                C[1] sep = spec.separatorChar;
                goto LS;
                do
                {
                    w.put(sep[]);
                LS:
                    w.put(b[0 .. r]);
                    b = b[r .. $];
                    r = spec.separatorCount;
                }
                while(b.length);
            }

            // try print decimal form without exponent
            // up to 6 digits exluding leading 0. or final .0
            if (s <= 0)
            {
                //0.001....
                //0.0001
                //0.00001
                //0.000001
                //If separatorChar is defined lets be less greed for space.
                if (this.exponent >= -6 || s >= -2 - (spec.separatorChar != 0) * 3)
                {
                    if (addSign)
                        w.put(sign[]);
                    w.put(zeros[0 .. -s + 2]);
                    w.put(buffer[$ - coefficientLength .. $]);
                    return;
                }
            }
            else
            if (this.exponent >= 0)
            {
                ///dddddd.0
                if (!spec.separatorChar)
                {
                    if (s <= 6)
                    {
                        buffer[$ - coefficientLength - 1] = sign[0];
                        w.put(buffer[$ - coefficientLength - addSign .. $]);
                        w.put(zeros[$ - (this.exponent + 2) .. $]);
                        return;
                    }
                }
                else
                {
                    if (s <= 12)
                    {
                        buffer0[$ - 16 .. $] = '0';
                        putL(buffer0[$ - coefficientLength - 16 .. $ - 16 + this.exponent]);
                        w.put(zeros[$ - 2 .. $]);
                        return;
                    }
                }
            }
            else
            {
                ///dddddd.0
                if (!spec.separatorChar)
                {
                    ///dddddd.d....
                    if (s <= 6 || coefficientLength <= 6)
                    {
                        buffer[$ - coefficientLength - 1] = sign[0];
                        w.put(buffer[$ - coefficientLength  - addSign .. $ - coefficientLength + s]);
                    T2:
                        buffer[$ - coefficientLength + s - 1] = '.';
                        w.put(buffer[$ - coefficientLength + s - 1 .. $]);
                        return;
                    }
                }
                else
                {
                    if (s <= 12 || coefficientLength <= 12)
                    {
                        putL(buffer[$ - coefficientLength .. $ - coefficientLength + s]);
                        goto T2;
                    }
                }
            }
        }

        assert(coefficientLength);

        sizediff_t exponent = s - 1;

        if (coefficientLength > 1)
        {
            auto c = buffer[$ - coefficientLength];
            buffer[$ - coefficientLength] = '.';
            buffer[$ - ++coefficientLength] = c;
        }

        buffer[$ - coefficientLength - 1] = sign[0];
        w.put(buffer[$ - coefficientLength - addSign .. $]);

        import mir.format_impl: printSignedToTail;

        static if (sizediff_t.sizeof == 8)
            enum N = 21;
        else
            enum N = 11;

        // prints e+/-exponent
        auto expLength = printSignedToTail(exponent, buffer0[$ - N - 16 .. $ - 16], '+');
        buffer[$ - ++expLength] = spec.exponentChar;
        w.put(buffer[$ - expLength .. $]);
    }

    static if (maxSize64 == 3)
    /// Check @nogc toString impl
    version(mir_bignum_test) @safe pure @nogc unittest
    {
        import mir.format: stringBuf;
        auto str = "5.28238923728e-876543210";
        auto decimal = Decimal!1(str);
        stringBuf buffer;
        buffer << decimal;
        assert(buffer.data == str, buffer.data);
    }

    /++
    Mir parsing supports up-to quadruple precision. The conversion error is 0 ULP for normal numbers. 
    Subnormal numbers with an exponent greater than or equal to -512 have upper error bound equal to 1 ULP.    +/
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() const
        if (isFloatingPoint!T && isMutable!T)
    {

        enum optimize = maxSize64 == 1 && size_t.sizeof == 8 && T.mant_dig < 64;

        version(LDC)
        {
            static if (optimize || wordNormalized)
                pragma(inline, true);
        }

        static if (optimize)
        {
            import mir.bignum.fixed: UInt;
            import mir.bignum.fp: Fp, extendedMul;
            import mir.bignum.internal.dec2flt_table;
            import mir.bignum.low_level_view: MaxWordPow5, MaxFpPow5;
            import mir.math.common: floor;
            import mir.utility: _expect;

            T ret = 0;
            size_t length = coefficient.length;


            static if (!wordNormalized)
            {
                if (coefficient.data[0] == 0)
                    length = 0;
            }

            if (_expect(exponent == exponent.max, false))
            {
                ret = length ? T.nan : T.infinity;
                goto R;
            }

            static if (!nonZero)
                if (length == 0)
                    goto R;
            enum S = 9;

            Fp!64 load(typeof(exponent) e)
            {
                auto p10coeff = p10_coefficients[cast(sizediff_t)e - min_p10_e][0];
                auto p10exp = p10_exponents[cast(sizediff_t)e - min_p10_e];
                return Fp!64(false, p10exp, UInt!64(p10coeff));
            }
            {
                auto expSign = exponent < 0;
                if (_expect((expSign ? -exponent : exponent) >>> S == 0, true))
                {
                    enum ulong mask = (1UL << (64 - T.mant_dig)) - 1;
                    enum ulong half = (1UL << (64 - T.mant_dig - 1));
                    enum ulong bound = ulong(1) << T.mant_dig;

                    auto c = Fp!64(UInt!64(coefficient.data[0]));
                    auto z = c.extendedMul(load(exponent));
                    ret = cast(T) z;
                    long bitsDiff = (cast(ulong) z.opCast!(Fp!64).coefficient & mask) - half;
                    if (_expect((bitsDiff < 0 ? -bitsDiff : bitsDiff) > 3 * expSign, true))
                        goto R;
                    if (!expSign && exponent <= MaxWordPow5!ulong || exponent == 0)
                        goto R;
                    if (expSign && MaxFpPow5!T >= -exponent && cast(ulong)c.coefficient < bound)
                    {
                        auto e = load(-exponent);
                        ret =  c.opCast!(T, true) / cast(T) (cast(ulong)e.coefficient >> e.exponent);
                        goto R;
                    }
                    ret = algoR!T(ret, view.coefficient, cast(int) exponent);
                    goto R;
                }
                ret = expSign ? 0 : T.infinity;
            }
        R:
            if (coefficient.sign)
                ret = -ret;
            return ret;
        }
        else
        {
            return view.opCast!(T, wordNormalized, nonZero);
        }
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
    assert(cast(double) decimal == double(PI) / 1e10);
    assert(key == DecimalExponentKey.e);
}


///
version(mir_bignum_test) 
@safe pure nothrow @nogc
unittest
{
    import mir.conv: to;
    Decimal!3 decimal;
    DecimalExponentKey key;

    assert(decimal.fromStringImpl("0", key));
    assert(key == DecimalExponentKey.none);
    assert(decimal.exponent == 0);
    assert(decimal.coefficient.length == 0);
    assert(!decimal.coefficient.sign);
    assert(cast(double) decimal.coefficient == 0);

    assert(decimal.fromStringImpl("-0.0", key));
    assert(key == DecimalExponentKey.dot);
    assert(decimal.exponent == -1);
    assert(decimal.coefficient.length == 0);
    assert(decimal.coefficient.sign);
    assert(cast(double) decimal.coefficient == 0);

    assert(decimal.fromStringImpl("0e0", key));
    assert(key == DecimalExponentKey.e);
    assert(decimal.exponent == 0);
    assert(decimal.coefficient.length == 0);
    assert(!decimal.coefficient.sign);
    assert(cast(double) decimal.coefficient == 0);
}

deprecated("use decimal.fromStringImpl insteade")
@trusted @nogc pure nothrow
bool parseDecimal(size_t maxSize64, C)(scope const(C)[] str, ref Decimal!maxSize64 decimal, out DecimalExponentKey key)
    if (isSomeChar!C)
{
    return decimal.fromStringImpl(str, key);
}


version(mir_bignum_test)
@safe pure @nogc unittest
{
    Decimal!4 i = "-0";
    
    assert(i.view.coefficient.coefficients.length == 0);
    assert(i.coefficient.view.unsigned.coefficients.length == 0);
    assert(i.coefficient.view == 0L);
    assert(cast(long) i.coefficient == 0);
}
