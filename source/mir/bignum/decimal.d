/++
Stack-allocated decimal type.

Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.decimal;

import mir.serde: serdeProxy, serdeScoped;
import std.traits: isSomeChar;

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
    int exponent;
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
        if (parseDecimal(str, this, key) || key == DecimalExponentKey.nan || key == DecimalExponentKey.infinity)
            return;
        static if (__traits(compiles, () @nogc { throw new Exception("Can't parse Decimal."); }))
        {
            import mir.exception: MirException;
            throw new MirException("Can't parse Decimal!" ~ (cast(int)maxSize64).stringof ~ " from string `", str , "`");
        }
        else
        {
            static immutable exception = new Exception("Can't parse Decimal!" ~ (cast(int)maxSize64).stringof ~ ".");
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
    Mir parsing supports up-to quadruple precision. The conversion error is 0 ULP for normal numbers. 
    Subnormal numbers with an exponent greater than or equal to -512 have upper error bound equal to 1 ULP.    +/
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() const
        if (isFloatingPoint!T && isMutable!T)
    {
        return view.opCast!(T, wordNormalized, nonZero);
    }
}

/++
Returns: false in case of integer overflow or incorrect input.
+/
@trusted @nogc pure nothrow
bool parseDecimal(size_t maxSize64, C)(scope const(C)[] str, ref Decimal!maxSize64 decimal, out DecimalExponentKey key)
    if (isSomeChar!C)
{
    import mir.bignum.low_level_view: MaxWordPow10;
    import mir.utility: _expect;
    decimal.exponent = 0;
    decimal.coefficient.sign = false;
    decimal.coefficient.length = 0;

    if (_expect(str.length == 0, false))
        return false;
    


    if (str[0] == '-')
    {
        decimal.coefficient.sign = true;
        str = str[1 .. $];
        if (_expect(str.length == 0, false))
            return false;
    }
    else
    if (_expect(str[0] == '+', false))
    {
        str = str[1 .. $];
        if (_expect(str.length == 0, false))
            return false;
    }

    uint d = str[0] - '0';
    str = str[1 .. $];

    size_t v;
    size_t t = 1;
    uint afterDot;
    bool dot;
    bool hasExponent;

    if (d == 0)
    {
        if (str.length == 0)
            return true;
        if (str[0] == '0')
            return false;
        goto S;
    }
    else
    if (d < 10)
    {
        goto S;
    }
    else
    if (d == '.' - '0')
    {
        goto D;
    }
    else
    {
        if (str.length == 2)
        {
            if ((d == 'i' - '0') & (cast(C[2])str[0 .. 2] == cast(C[2])"nf"))
            {
                key = DecimalExponentKey.infinity;
                return true;
            }
            if ((d == 'n' - '0') & (cast(C[2])str[0 .. 2] == cast(C[2])"an"))
            {
                key = DecimalExponentKey.nan;
                return true;
            }
        }
        return false;
    }

    for(;;)
    {
        enum mp10 = size_t(10) ^^ MaxWordPow10!size_t;
        d = str[0] - '0';
        str = str[1 .. $];

        if (_expect(d <= 10, true))
        {
            v *= 10;
    S:
            t *= 10;
            v += d;
            afterDot += dot;

            if (_expect(t == mp10 || str.length == 0, false))
            {
            L:
                auto overflow = decimal.coefficient.opOpAssign!"*"(t, v);
                if (_expect(overflow, 0))
                    return false;
                v = 0;
                t = 1;
                if (str.length == 0)
                {
                M:
                    decimal.exponent -= afterDot;
                    return true;
                }
            }

            continue;
        }
        else
        if (key != d) switch (d)
        {
            D:
            case DecimalExponentKey.dot:
                key = cast(DecimalExponentKey)d;
                if (_expect(!dot, true))
                {
                    dot = true;
                    if (str.length)
                        continue;
                }
                break;
            case DecimalExponentKey.e:
            case DecimalExponentKey.d:
            case DecimalExponentKey.E:
            case DecimalExponentKey.D:
                key = cast(DecimalExponentKey)d;
                hasExponent = true;
                import mir.parse: parse;
                if (parse(str, decimal.exponent) && str.length == 0)
                {
                    if (t != 1)
                       goto L;
                    goto M;
                }
                break;
            default:
        }
        break;
    }
    return false;
}

///
enum DecimalExponentKey
{
    ///
    none = 0,
    ///
    dot = '.' - '0',
    ///
    d = 'd' - '0',
    ///
    e = 'e' - '0',
    ///
    D = 'D' - '0',
    ///
    E = 'E' - '0',
    ///
    infinity,
    ///
    nan,
}

///
version(mir_bignum_test) 
@safe pure nothrow @nogc
unittest
{
    Decimal!3 decimal;
    DecimalExponentKey key;

    assert("1.334".parseDecimal(decimal, key));
    assert(cast(double) decimal.view == 1.334);
    assert(key == DecimalExponentKey.dot);

    assert("+0.334e-5"w.parseDecimal(decimal, key));
    assert(cast(double) decimal.view == 0.334e-5);
    assert(key == DecimalExponentKey.e);

    assert("-334D-5"d.parseDecimal(decimal, key));
    assert(cast(double) decimal.view == -334e-5);
    assert(key == DecimalExponentKey.D);

    assert("2482734692817364218734682973648217364981273648923423".parseDecimal(decimal, key));
    assert(cast(double) decimal.view == 2482734692817364218734682973648217364981273648923423.0);
    assert(key == DecimalExponentKey.none);

    assert(".023".parseDecimal(decimal, key));
    assert(cast(double) decimal.view == .023);
    assert(key == DecimalExponentKey.dot);

    assert("0E100".parseDecimal(decimal, key));
    assert(cast(double) decimal.view == 0);
    assert(key == DecimalExponentKey.E);

    assert("-nan".parseDecimal(decimal, key));
    assert(cast(double) decimal.view == 0);
    assert(decimal.coefficient.sign);
    assert(key == DecimalExponentKey.nan);

    assert("inf".parseDecimal(decimal, key));
    assert(cast(double) decimal.view == 0);
    assert(key == DecimalExponentKey.infinity);

    assert(!"3.3.4".parseDecimal(decimal, key));
    assert(!"3.4.".parseDecimal(decimal, key));
    assert(!"4.".parseDecimal(decimal, key));
    assert(!".".parseDecimal(decimal, key));
    assert(!"0.".parseDecimal(decimal, key));
    assert(!"00".parseDecimal(decimal, key));
    assert(!"0d".parseDecimal(decimal, key));

    import mir.math.constant: PI;
    assert("3.141592653589793378e-10".parseDecimal(decimal, key));
    assert(cast(double) decimal.view == double(PI) / 1e10);
    assert(key == DecimalExponentKey.e);
}
