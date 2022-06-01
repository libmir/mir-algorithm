module mir.bignum.internal.parse;

import std.traits: isSomeChar;
import mir.parse: DecimalExponentKey;

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

/++
+/
struct SmallDecimalParsingResult
{
    ///
    bool success;
    ///
    bool sign;
    ///
    DecimalExponentKey key;
    ///
    long exponent;
    ///
    ulong coefficient;
}

/++
+/
SmallDecimalParsingResult parseJsonNumberImpl(scope const(char)[] str)
    in (str.length)
{
    pragma(inline, false);

    alias W = ulong;
    enum bool allowSpecialValues = false;
    enum bool allowDotOnBounds = false;
    enum bool allowDExponent = false;
    enum bool allowStartingPlus = false;
    enum bool allowUnderscores = false;
    enum bool allowLeadingZeros = false;
    enum bool allowExponent = true;
    enum bool checkEmpty = false;

    typeof(return) result;

    bool mullAdd(ulong multplier, ulong carry)
    {
        import mir.checkedint: mulu, addu;
        bool overflow;
        result.coefficient = mulu(result.coefficient, multplier, overflow);
        if (overflow)
            return overflow;
        result.coefficient = addu(result.coefficient, carry, overflow);
        return overflow;
    }

    alias impl = decimalFromStringImpl!(mullAdd, ulong);
    alias specialization = impl!(char,
        allowSpecialValues,
        allowDotOnBounds,
        allowDExponent,
        allowStartingPlus,
        allowUnderscores,
        allowLeadingZeros,
        allowExponent,
        checkEmpty,
    );

    with(result)
        success = specialization(str, key, exponent, sign);
    return result;
}

/++
Returns: false in case of overflow or incorrect string.
+/
template decimalFromStringImpl(alias mullAdd, W = size_t)
{
    bool decimalFromStringImpl(C,
        bool allowSpecialValues,
        bool allowDotOnBounds,
        bool allowDExponent,
        bool allowStartingPlus,
        bool allowUnderscores,
        bool allowLeadingZeros,
        bool allowExponent,
        bool checkEmpty,
    )
        (scope const(C)[] str, out DecimalExponentKey key, scope ref long exponent, scope ref bool sign)
        scope @trusted pure @nogc nothrow
        if (isSomeChar!C)
    {
        version(LDC)
            pragma(inline, true);

        import mir.utility: _expect;
        static if (checkEmpty)
        {
            if (_expect(str.length == 0, false))
                return false;
        }

        sign = str[0] == '-';
        if (sign)
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

        ulong d = str[0] - C('0');
        str = str[1 .. $];

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
                    d = str[0] - C('0');
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
                    return true;
                d = str[0] - C('0');
                str = str[1 .. $];
                if (d < 10)
                    return false;
                goto DOT;
            }
        }

        goto F0;

    S:
        if (str.length == 0)
            return true;
        d = str[0] - C('0');
        str = str[1 .. $];

        if (d < 10)
        {
    F0:
            if (_expect(mullAdd(10u, cast(uint)d), false))
                return false;
            goto S;
        }

        static if (allowUnderscores)
        {
            if (d == '_' - '0')
            {
                if (str.length == 0)
                    return false;
                d = str[0] - C('0');
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
                return allowDotOnBounds;
            }

        IF:
            ulong multplier = 10;
            static if (is(C == char) && is(W == ulong))
            if (!__ctfe)
            {
                import mir.bignum.internal.parse: isMadeOfEightDigits, parseEightDigits;
                if (str.length >= 8 && isMadeOfEightDigits(str[0 .. 8]))
                {
                    multplier = 100000000;
                    d = parseEightDigits(str[0 .. 8]);
                    str = str[8 .. $];
                    exponent -= 8;
                    if (str.length >= 7)
                    {
                        if (isMadeOfEightDigits((str.ptr - 1)[0 .. 8]))
                        {
                            multplier = 100000000UL * 10000000;
                            d -= str.ptr[-1] - '0';
                            d *= 10000000;
                            d += parseEightDigits((str.ptr - 1)[0 .. 8]);
                            str = str[7 .. $];
                            exponent -= 7;
                            if (str.length)
                            {
                                auto md = str[0] - C('0');
                                if (md < 10)
                                {
                                    d *= 10;
                                    multplier = 100000000UL * 100000000;
                                    d += md;
                                    str = str[1 .. $];
                                    exponent -= 1;
                                }
                            }
                        }
                        else
                        {
                        TrySix:
                            if (isMadeOfEightDigits((str.ptr - 2)[0 .. 8]))
                            {
                                multplier = 100000000UL * 1000000;
                                d -= str.ptr[-1] - '0';
                                d -= (str.ptr[-2] - '0') * 10;
                                d *= 1000000;
                                d += parseEightDigits((str.ptr - 2)[0 .. 8]);
                                str = str[6 .. $];
                                exponent -= 6;
                            }
                        }

                    }
                    else
                    if (str.length == 6)
                        goto TrySix;
                    goto FIL;
                }
            }

            d = str[0] - C('0');
            str = str[1 .. $];
            if (_expect(d >= 10, false))
                goto DOB;
        FI:
            exponent--;
            multplier = 10;
        FIL:
            if (_expect(mullAdd(multplier, d), false))
                return false;
            import mir.stdio;
            // debug dump("str = ", str);
            if (str.length == 0)
                return true;
            d = str[0] - C('0');
            str = str[1 .. $];
            if (d < 10)
                goto FI;

            static if (allowUnderscores)
            {
                if (d == '_' - '0')
                {
                    if (str.length == 0)
                        return false;
                    d = str[0] - C('0');
                    str = str[1 .. $];
                    if (_expect(d < 10, true))
                        goto FI;
                    return false;
                }
            }
        DOB:
            static if (!allowDotOnBounds)
            {
                if (exponent == 0)
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
                long exponentPlus;
                if (parse(str, exponentPlus) && str.length == 0)
                {
                    import mir.stdio;
                    // debug dump("exponentPlus ", exponentPlus);
                    // debug dump("exponent ", exponent);
                    import mir.checkedint: adds;
                    bool overflow;
                    exponent = exponent.adds(exponentPlus, overflow);
                    // debug dump("overflow ", overflow);
                    return !overflow;
                }
            }
        }
        return false;

        static if (allowSpecialValues)
        {
        NI:
            if (str.length == 2)
            {
                auto stail = cast(C[2])str[0 .. 2];
                if (d == 'i' - '0' && stail == cast(C[2])"nf" || d == 'I' - '0' && (stail == cast(C[2])"nf" || stail == cast(C[2])"NF"))
                {
                    key = DecimalExponentKey.infinity;
                    return true;
                }
                if (d == 'n' - '0' && stail == cast(C[2])"an" || d == 'N' - '0' && (stail == cast(C[2])"aN" || stail == cast(C[2])"AN"))
                {
                    key = DecimalExponentKey.nan;
                    return true;
                }
            }
            return false;
        }
    }
}
