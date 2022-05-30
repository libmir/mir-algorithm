/++
Stack-allocated decimal type.

Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.decimal;

import mir.serde: serdeProxy, serdeScoped;
import std.traits: isSomeChar;
///
public import mir.bignum.low_level_view: DecimalExponentKey;
import mir.bignum.low_level_view: ceilLog10Exp2;

private enum expBufferLength = 2 + ceilLog10Exp2(ulong.sizeof * 8);
private static immutable C[9] zerosImpl(C) = "0.00000.0";

/++
Stack-allocated decimal type.
Params:
    maxSize64 = count of 64bit words in coefficient
+/
@serdeScoped @serdeProxy!(const(char)[])
struct Decimal(uint maxSize64)
    if (maxSize64 && maxSize64 <= ushort.max)
{
    import mir.format: NumericSpec;
    import mir.bignum.integer;
    import mir.bignum.low_level_view;
    import std.traits: isMutable, isFloatingPoint;

    ///
    long exponent;
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
    this(C)(scope const(C)[] str, int exponentShift = 0) @safe pure @nogc
        if (isSomeChar!C)
    {
        DecimalExponentKey key;
        if (fromStringImpl(str, key, exponentShift) || key == DecimalExponentKey.nan || key == DecimalExponentKey.infinity)
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

    /++
    Constructs Decimal from the floating point number using the $(HTTPS github.com/ulfjack/ryu, Ryu algorithm).

    The number is the shortest decimal representation that being converted back would result the same floating-point number.
    +/
    this(T)(const T x)
        if (isFloatingPoint!T && maxSize64 >= 1 + (T.mant_dig >= 64))
    {
        import mir.bignum.internal.ryu.generic_128: genericBinaryToDecimal;
        this = genericBinaryToDecimal(x);
    }

    ///
    ref opAssign(uint rhsMaxSize64)(auto ref scope const Decimal!rhsMaxSize64 rhs) return
        if (rhsMaxSize64 < maxSize64)
    {
        this.exponent = rhs.exponent;
        this.coefficient = rhs.coefficient;
        return this;
    }

    /++
    Handle thousand separators for non exponential numbers.

    Returns: false in case of overflow or incorrect string.
    +/
    bool fromStringWithThousandsSeparatorImpl(C,
        bool allowSpecialValues = true,
        bool allowStartingPlus = true,
        bool allowLeadingZeros = true,
    )(
        scope const(C)[] str,
        const C thousandsSeparator,
        const C fractionSeparator,
        out DecimalExponentKey key,
        int exponentShift = 0,
    ) @trusted
        if (isSomeChar!C)
    {
        import mir.algorithm.iteration: find;
        import mir.format: stringBuf;
        import mir.ndslice.chunks: chunks;
        import mir.ndslice.slice: sliced;
        import mir.ndslice.topology: retro;

        auto buffer = stringBuf;
        assert(thousandsSeparator != fractionSeparator);
        if (str.length && (str[0] == '+' || str[0] == '-'))
        {
            buffer.put(cast(char)str[0]);
            str = str[1 .. $];
        }
        auto integer = str[0 .. $ - str.find!(a => a == fractionSeparator)];
        if (integer.length % 4 == 0)
            return false;
        foreach_reverse (chunk; integer.sliced.retro.chunks(4))
        {
            auto s = chunk.retro.field;
            if (s.length == 4)
            {
                if (s[0] != thousandsSeparator)
                    return false;
                s = s[1 .. $];
            }
            do
            {
                if (s[0] < '0' || s[0] > '9')
                    return false;
                buffer.put(cast(char)s[0]);
                s = s[1 .. $];
            }
            while(s.length);
        }
        if (str.length > integer.length)
        {
            buffer.put('.');
            str = str[integer.length + 1 .. $];
            if (str.length == 0)
                return false;
            do
            {
                buffer.put(cast(char)str[0]);
                str = str[1 .. $];
            }
            while(str.length);
        }
        return fromStringImpl!(char,
            allowSpecialValues,
            false, // allowDotOnBounds
            false, // allowDExponent
            allowStartingPlus,
            false, // allowUnderscores
            allowLeadingZeros, // allowLeadingZeros
            false, // allowExponent
            false, // checkEmpty
        )(buffer.data, key, exponentShift);
    }

    /++
    Returns: false in case of overflow or incorrect string.
    +/
    bool fromStringImpl(C,
        bool allowSpecialValues = true,
        bool allowDotOnBounds = true,
        bool allowDExponent = true,
        bool allowStartingPlus = true,
        bool allowUnderscores = true,
        bool allowLeadingZeros = true,
        bool allowExponent = true,
        bool checkEmpty = true,
        )
        (scope const(C)[] str, out DecimalExponentKey key, int exponentShift = 0)
        scope @trusted pure @nogc nothrow
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

            if (_expect(d >= 10, false))
            {
                static if (allowDotOnBounds)
                {
                    if (d == '.' - '0')
                    {
                        if (str.length == 0)
                            return false;
                        key = DecimalExponentKey.dot;
                        d = str[0] - '0';
                        str = str[1 .. $];
                        if (_expect(d < 10, true))
                            goto FI;
                        return false;
                    }
                }
                static if (allowSpecialValues)
                    goto NI;
                else
                    return false;
            }

            static if (!allowLeadingZeros)
            {
                if (_expect(d == 0, false))
                {
                    if (str.length == 0)
                        goto R;
                    d = str[0] - '0';
                    str = str[1 .. $];
                    if (d < 10)
                        return false;
                    goto DOT;
                }
            }

            v = d;

        S:
            if (str.length == 0)
                goto R;
            d = str[0] - '0';
            str = str[1 .. $];

            if (d < 10)
            {
        F0:
                import mir.checkedint: mulu, addu;
                bool overflow;
                v = mulu(v, cast(uint)10, overflow);
                if (overflow)
                    return false;
                v = addu(v, d, overflow);
                if (overflow)
                    return false;
                goto S;
            }

            static if (allowUnderscores)
            {
                if (d == '_' - '0')
                {
                    if (str.length == 0)
                        return false;
                    d = str[0] - '0';
                    str = str[1 .. $];
                    if (_expect(d < 10, true))
                        goto F0;
                    return false;
                }
            }
        DOT:
            if (d == DecimalExponentKey.dot)
            {
                // The dot modifier CANNOT be preceded by any modifiers. 
                if (key != DecimalExponentKey.none)
                    return false;

                key = DecimalExponentKey.dot;

                if (str.length == 0)
                {
                    static if (allowDotOnBounds)
                        goto R;
                    else
                        return false;
                }

            IF:

                static if (is(C == char))
                {
                    import mir.bignum.internal.parse: isMadeOfEightDigits, parseEightDigits;
                    if (str.length >= 8 && isMadeOfEightDigits(str[0 .. 8]))
                    {
                        ulong multplier = 100000000;
                        ulong value = parseEightDigits(str[0 .. 8]);
                        str = str[8 .. $];
                        exponentShift -= 8;
                        if (str.length >= 8 && isMadeOfEightDigits(str[0 .. 8]))
                        {
                            multplier = 100000000 * 100000000;
                            value *= 100000000;
                            value += parseEightDigits(str[0 .. 8]);
                            str = str[8 .. $];
                            exponentShift -= 8;
                        }

                        {
                            import mir.checkedint: mulu, addu;
                            bool overflow;
                            v = mulu(v, multplier, overflow);
                            if (overflow)
                                return false;
                            v = addu(v, value, overflow);;
                            if (overflow)
                                return false;
                        }
                    }
                }

                d = str[0] - '0';
                str = str[1 .. $];
                if (_expect(d >= 10, false))
                    goto DOB;
            FI:
                {
                    import mir.checkedint: mulu, addu;
                    bool overflow;
                    v = mulu(v, cast(uint)10, overflow);
                    if (overflow)
                        return false;
                    v = addu(v, d, overflow);;
                    if (overflow)
                        return false;
                }
                exponentShift--;
                if (str.length == 0)
                    goto E;
                d = str[0] - '0';
                str = str[1 .. $];
                if (d < 10)
                    goto FI;

                static if (allowUnderscores)
                {
                    if (d == '_' - '0')
                    {
                        if (str.length == 0)
                            return false;
                        d = str[0] - '0';
                        str = str[1 .. $];
                        if (_expect(d < 10, true))
                            goto FI;
                        return false;
                    }
                }
            DOB:
                static if (!allowDotOnBounds)
                {
                    if (exponentShift == 0)
                        return false;
                }

            }

            static if (allowExponent)
            {
                if (d == DecimalExponentKey.e
                 || d == DecimalExponentKey.E
                 || d == DecimalExponentKey.d && allowDExponent
                 || d == DecimalExponentKey.D && allowDExponent
                )
                {
                    import mir.parse: parse;
                    key = cast(DecimalExponentKey)d;
                    if (parse(str, exponent) && str.length == 0)
                        goto E;
                }
            }
            return false;

        E:
            exponent += exponentShift;
        R:
            coefficient.data[0] = v;
            coefficient.length = v != 0;
            return true;

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
            auto ret = work.fromStringImpl!(C,
                allowSpecialValues,
                allowDotOnBounds,
                allowDExponent,
                allowStartingPlus,
                allowUnderscores,
                allowLeadingZeros,
                allowExponent,
                checkEmpty,
            )(str, key, exponentShift);
            coefficient.length = cast(uint) work.coefficient.coefficients.length;
            coefficient.sign = work.sign;
            exponent = work.exponent;
            return ret;
        }
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
                    data[i * 2 + 0] = l;
                    data[i * 2 + 1] = h;
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
        long s = this.exponent + coefficientLength;

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
                    w.put(zeros[0 .. cast(sizediff_t)(-s + 2)]);
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
                        w.put(zeros[($ - (cast(sizediff_t)this.exponent + 2)) .. $]);
                        return;
                    }
                }
                else
                {
                    if (s <= 12)
                    {
                        buffer0[$ - 16 .. $] = '0';
                        putL(buffer0[$ - coefficientLength - 16 .. $ - 16 + cast(sizediff_t)this.exponent]);
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
                        w.put(buffer[$ - coefficientLength  - addSign .. $ - coefficientLength + cast(sizediff_t)s]);
                    T2:
                        buffer[$ - coefficientLength + cast(sizediff_t)s - 1] = '.';
                        w.put(buffer[$ - coefficientLength + cast(sizediff_t)s - 1 .. $]);
                        return;
                    }
                }
                else
                {
                    if (s <= 12 || coefficientLength <= 12)
                    {
                        putL(buffer[$ - coefficientLength .. $ - coefficientLength + cast(sizediff_t)s]);
                        goto T2;
                    }
                }
            }
        }

        assert(coefficientLength);

        long exponent = s - 1;

        if (coefficientLength > 1)
        {
            auto c = buffer[$ - coefficientLength];
            buffer[$ - coefficientLength] = '.';
            buffer[$ - ++coefficientLength] = c;
        }

        buffer[$ - coefficientLength - 1] = sign[0];
        w.put(buffer[$ - coefficientLength - addSign .. $]);

        import mir.format_impl: printSignedToTail;

        static if (exponent.sizeof == 8)
            enum N = 21;
        else
            enum N = 11;

        // prints e+/-exponent
        auto expLength = printSignedToTail(exponent, buffer0[$ - N - 16 .. $ - 16], '+');
        buffer[$ - ++expLength] = spec.exponentChar;
        w.put(buffer[$ - expLength .. $]);
    }

    /++
    Mir parsing supports up-to quadruple precision. The conversion error is 0 ULP for normal numbers. 
    Subnormal numbers with an exponent greater than or equal to -512 have upper error bound equal to 1 ULP.    +/
    T opCast(T, bool wordNormalized = true)() const
        if (isFloatingPoint!T && isMutable!T)
    {
        return view.opCast!(T, wordNormalized);
    }

    ///
    bool isNaN() scope const @property
    {
        return exponent == exponent.max && coefficient.length;
    }

    ///
    bool isInfinity() scope const @property
    {
        return exponent == exponent.max && coefficient.length == 0;
    }

    ///
    bool isSpecial() scope const @property
    {
        return exponent == exponent.max;
    }

    ///
    ref opOpAssign(string op, size_t rhsMaxSize64)(ref const Decimal!rhsMaxSize64 rhs) @safe pure return
        if (op == "+" || op == "-")
    {
        import mir.utility: max;
        BigInt!(max(rhsMaxSize64, maxSize64, 256u)) rhsCopy = void;
        BigIntView!(const size_t) rhsView;
        auto expDiff = cast(sizediff_t) (exponent - rhs.exponent);
        if (expDiff >= 0)
        {
            exponent = rhs.exponent;
            coefficient.mulPow5(expDiff);
            coefficient.opOpAssign!"<<"(expDiff);
            rhsView = rhs.coefficient.view;
        }
        else
        {
            rhsCopy.copyFrom(rhs.coefficient.coefficients, rhs.coefficient.sign);
            rhsCopy.mulPow5(-expDiff);
            rhsCopy.opOpAssign!"<<"(-expDiff);
            rhsView = rhsCopy.view;
        }
        coefficient.opOpAssign!op(rhsView);
        return this;
    }
}

///
version(mir_bignum_test) 
@safe pure nothrow @nogc
unittest
{
    import mir.conv: to;
    Decimal!256 decimal = void;
    DecimalExponentKey key;

    assert(decimal.fromStringImpl("3.141592653589793378e-10", key));
    assert(cast(double) decimal == 0x1.596bf8ce7631ep-32);
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

///
version(mir_bignum_test) @safe pure @nogc unittest
{
    auto a = Decimal!1("777.7");
    auto b = Decimal!1("777");
    import mir.format;
    assert(stringBuf() << cast(double)a - cast(double)b << getData == "0.7000000000000455");
    a -= b;
    assert(stringBuf() << a << getData == "0.7");

    a = Decimal!1("-777.7");
    b = Decimal!1("777");
    a += b;
    assert(stringBuf() << a << getData == "-0.7");

    a = Decimal!1("777.7");
    b = Decimal!1("-777");
    a += b;
    assert(stringBuf() << a << getData == "0.7");

    a = Decimal!1("777");
    b = Decimal!1("777.7");
    a -= b;
    assert(stringBuf() << a << getData == "-0.7");
}

/// Check @nogc toString impl
version(mir_bignum_test) @safe pure @nogc unittest
{
    import mir.format: stringBuf;
    auto str = "5.28238923728e-876543210";
    auto decimal = Decimal!1(str);
    auto buffer = stringBuf;
    buffer << decimal;
    assert(buffer.data == str);
}

///
version(mir_bignum_test)
@safe pure @nogc unittest
{
    Decimal!4 i = "-0";
    
    assert(i.view.coefficient.coefficients.length == 0);
    assert(i.coefficient.view.unsigned.coefficients.length == 0);
    assert(i.coefficient.view == 0L);
    assert(cast(long) i.coefficient == 0);
    assert(i.coefficient.sign);
}

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
version(mir_bignum_test) 
@safe pure nothrow @nogc
unittest
{
    import mir.conv: to;
    Decimal!3 decimal;
    DecimalExponentKey key;

    // Check precise percentate parsing
    assert(decimal.fromStringImpl("71.7", key, -2));
    assert(key == DecimalExponentKey.dot);
    // The result is exact value instead of 0.7170000000000001 = 71.7 / 100
    assert(cast(double) decimal == 0.717);

    assert(decimal.fromStringImpl("+0.334e-5"w, key));
    assert(key == DecimalExponentKey.e);
    assert(cast(double) decimal == 0.334e-5);

    assert(decimal.fromStringImpl("100_000_000"w, key));
    assert(key == DecimalExponentKey.none);
    assert(cast(double) decimal == 1e8);

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
    assert(decimal.fromStringImpl("00", key));
    assert(!decimal.fromStringImpl("0d", key));
}

version(mir_bignum_test)
@safe pure nothrow @nogc
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

    /++ Test that Issue #365 is handled properly +/
    assert(decimal.fromStringImpl("123456.e0", key));
    assert(key == DecimalExponentKey.e);
    assert(cast(double) decimal == 123_456.0);

    assert(decimal.fromStringImpl("123_456.e0", key));
    assert(key == DecimalExponentKey.e);
    assert(cast(double) decimal == 123_456.0);

    assert(decimal.fromStringImpl("123456.E0", key));
    assert(key == DecimalExponentKey.E);
    assert(cast(double) decimal == 123_456.0);

    assert(decimal.fromStringImpl("123_456.E0", key));
    assert(key == DecimalExponentKey.E);
    assert(cast(double) decimal == 123_456.0);

    assert(decimal.fromStringImpl("123456.d0", key));
    assert(key == DecimalExponentKey.d);
    assert(cast(double) decimal == 123_456.0);

    assert(decimal.fromStringImpl("123_456.d0", key));
    assert(key == DecimalExponentKey.d);
    assert(cast(double) decimal == 123_456.0);

    assert(decimal.fromStringImpl("123456.D0", key));
    assert(key == DecimalExponentKey.D);
    assert(cast(double) decimal == 123_456.0);

    assert(decimal.fromStringImpl("123_456.D0", key));
    assert(key == DecimalExponentKey.D);
    assert(cast(double) decimal == 123_456.0);

    /++ Test invalid examples with the fix introduced for Issue #365 +/
    assert(!decimal.fromStringImpl("123_456_.D0", key));
    assert(!decimal.fromStringImpl("123_456.DD0", key));
    assert(!decimal.fromStringImpl("123_456_.E0", key));
    assert(!decimal.fromStringImpl("123_456.EE0", key));
    assert(!decimal.fromStringImpl("123456.ED0", key));
    assert(!decimal.fromStringImpl("123456E0D0", key));
    assert(!decimal.fromStringImpl("123456._D0", key));
    assert(!decimal.fromStringImpl("123456_.D0", key));
    assert(!decimal.fromStringImpl("123456.E0D0", key));
    assert(!decimal.fromStringImpl("123456.D0_", key));
    assert(!decimal.fromStringImpl("123456_", key));

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
    assert(decimal.fromStringImpl("00", key));
    assert(!decimal.fromStringImpl("0d", key));
}

///
version(mir_bignum_test)
@safe pure @nogc unittest
{
    import mir.math.constant: PI;
    Decimal!2 decimal = "3.141592653589793378e-40"; // constructor
    assert(cast(double) decimal == double(PI) / 1e40);
}


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
version(mir_bignum_test) 
@safe pure nothrow @nogc
unittest
{
    Decimal!3 decimal;
    DecimalExponentKey key;

    assert(decimal.fromStringWithThousandsSeparatorImpl("12,345.678", ',', '.', key));
    assert(cast(double) decimal == 12345.678);
    assert(key == DecimalExponentKey.dot);

    assert(decimal.fromStringWithThousandsSeparatorImpl("12,345,678", ',', '.', key, -3));
    assert(cast(double) decimal == 12345.678);
    assert(key == DecimalExponentKey.none);

    assert(decimal.fromStringWithThousandsSeparatorImpl("021 345,678", ' ', ',', key));
    assert(cast(double) decimal == 21345.678);
    assert(key == DecimalExponentKey.dot);
}
