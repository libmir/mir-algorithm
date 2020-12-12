/++
Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.fp;

import std.traits;
import mir.bitop;
import mir.utility;

package enum half(size_t hs) = (){
    import mir.bignum.fixed: UInt;
    UInt!hs ret; ret.signBit = true; return ret;
}();

/++
Software floating point number.

Params:
    coefficientSize = coefficient size in bits

Note: the implementation doesn't support NaN and Infinity values.
+/
struct Fp(size_t coefficientSize, Exp = sizediff_t)
    if ((is(Exp == int) || is(Exp == long)) && coefficientSize % (size_t.sizeof * 8) == 0 && coefficientSize >= (size_t.sizeof * 8))
{
    import mir.bignum.fixed: UInt;

    bool sign;
    Exp exponent;
    UInt!coefficientSize coefficient;

    /++
    +/
    nothrow
    this(bool sign, Exp exponent, UInt!coefficientSize normalizedCoefficient)
    {
        this.coefficient = normalizedCoefficient;
        this.exponent = exponent;
        this.sign = sign;
    }

    /++
    Params:
        value = Hardware floating point number. Special values `nan` and `inf` aren't allowed.
    Params:
        values = not a special floationg point-value
    +/
    this(T)(const T value)
        @safe pure nothrow @nogc
        if (isFloatingPoint!T && T.mant_dig <= coefficientSize)
    {
        import mir.math.common : fabs;
        import mir.math.ieee : frexp, signbit, ldexp;
        assert(value == value);
        assert(value.fabs < T.infinity);
        this.sign = value.signbit != 0;
        if (value == 0)
            return;
        T x = value.fabs;
        {
            int exp;
            x = frexp(x, exp);
            this.exponent = exp;
        }
        static if (T.mant_dig < 64)
        {
            this.coefficient = UInt!coefficientSize(cast(ulong)cast(long)x);
        }
        else
        static if (T.mant_dig == 64)
        {
            this.coefficient = UInt!coefficientSize(cast(ulong)x);
        }
        else
        {
            enum scale = T(2) ^^ -64;
            enum scaleInv = T(2) ^^ +64;
            x *= scale;
            long high = cast(long) x;
            if (high > x)
                --high;
            x -= high;
            x *= scaleInv;
            this.coefficient = (UInt!coefficientSize(ulong(high)) << 64) | cast(ulong)x;
        }
        auto shift = this.coefficient.ctlz;
        this.exponent -= cast(Exp) shift;
        import std.stdio;
        debug printf("shift = %ld\n", shift);
        this.coefficient <<= shift;
    }

    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    // @safe pure @nogc
    unittest
    {
        auto f = Fp!64(-33.0 * 2.0 ^^ -10);
        assert(f.sign);
        import std.stdio;
        writeln(f.exponent);
        assert(f.exponent == -10 - (64 - 6));
        assert(f.coefficient == 33UL << (64 - 6));
    }

    /++
    +/
    this(size_t size)(UInt!size integer, bool normalizedInteger = false)
        nothrow
    {
        import mir.bignum.fixed: UInt;
        static if (size < coefficientSize)
        {
            if (normalizedInteger)
            {
                this(false, Exp(size) - coefficientSize, integer.rightExtend!(coefficientSize - size));
            }
            else
            {
                this(integer.toSize!coefficientSize, false);
            }
        }
        else
        {
            this.exponent = size - coefficientSize;
            if (!normalizedInteger)
            {
                auto c = integer.ctlz;
                integer <<= c;
                this.exponent -= c;
            }
            static if (size == coefficientSize)
            {
                coefficient = integer;
            }
            else
            {
                enum N = coefficient.data.length;
                version (LittleEndian)
                    coefficient.data = integer.data[$ - N .. $];
                else
                    coefficient.data = integer.data[0 .. N];
                enum tailSize = size - coefficientSize;
                auto cr = integer.toSize!tailSize.opCmp(half!tailSize);
                if (cr > 0 || cr == 0 && coefficient.bt(0))
                {
                    if (auto overflow = coefficient += 1)
                    {
                        coefficient = half!coefficientSize;
                        exponent++;
                    }
                }
            }
        }
    }

    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto fp = Fp!128(UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));
        assert(fp.exponent == 0);
        assert(fp.coefficient == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));

        fp = Fp!128(UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"), true);
        assert(fp.exponent == 0);
        assert(fp.coefficient == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));

        fp = Fp!128(UInt!128.fromHexString("ae3cd0aff2714a1de7022b0029d"));
        assert(fp.exponent == -20);
        assert(fp.coefficient == UInt!128.fromHexString("ae3cd0aff2714a1de7022b0029d00000"));

        fp = Fp!128(UInt!128.fromHexString("e7022b0029d"));
        assert(fp.exponent == -84);
        assert(fp.coefficient == UInt!128.fromHexString("e7022b0029d000000000000000000000"));

        fp = Fp!128(UInt!64.fromHexString("e7022b0029d"));
        assert(fp.exponent == -84);
        assert(fp.coefficient == UInt!128.fromHexString("e7022b0029d000000000000000000000"));

        fp = Fp!128(UInt!64.fromHexString("e7022b0029dd0aff"), true);
        assert(fp.exponent == -64);
        assert(fp.coefficient == UInt!128.fromHexString("e7022b0029dd0aff0000000000000000"));

        fp = Fp!128(UInt!64.fromHexString("e7022b0029d"));
        assert(fp.exponent == -84);
        assert(fp.coefficient == UInt!128.fromHexString("e7022b0029d000000000000000000000"));
    
        fp = Fp!128(UInt!192.fromHexString("ffffffffffffffffffffffffffffffff1000000000000000"));
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!128.fromHexString("ffffffffffffffffffffffffffffffff"));

        fp = Fp!128(UInt!192.fromHexString("ffffffffffffffffffffffffffffffff8000000000000000"));
        assert(fp.exponent == 65);
        assert(fp.coefficient == UInt!128.fromHexString("80000000000000000000000000000000"));

        fp = Fp!128(UInt!192.fromHexString("fffffffffffffffffffffffffffffffe8000000000000000"));
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!128.fromHexString("fffffffffffffffffffffffffffffffe"));

        fp = Fp!128(UInt!192.fromHexString("fffffffffffffffffffffffffffffffe8000000000000001"));
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!128.fromHexString("ffffffffffffffffffffffffffffffff"));
    }

    ///
    ref Fp opOpAssign(string op : "*")(Fp rhs) nothrow return
    {
        this = this.opBinary!op(rhs);
        return this;
    }

    ///
    Fp opBinary(string op : "*")(Fp rhs) nothrow const
    {
        return cast(Fp) .extendedMul(this, rhs);
    }

    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = Fp!128(0, -13, UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d"));
        auto b = Fp!128(1, 100, UInt!128.fromHexString("e3251bacb112c88b71ad3f85a970a314"));
        auto fp = a * b;
        assert(fp.sign);
        assert(fp.exponent == 100 - 13 + 128);
        assert(fp.coefficient == UInt!128.fromHexString("c6841dd302415d785373ab6d93712988"));
    }

    ///
    T opCast(T)() nothrow const
        if (is(Unqual!T == bool))
    {
        return coefficient != 0;
    }
    
    ///
    T opCast(T, bool noHalf = false)() nothrow const
        if (isFloatingPoint!T)
    {
        import mir.math.ieee: ldexp;
        auto exp = cast()exponent;
        static if (coefficientSize == 32)
        {
            Unqual!T c = cast(uint) coefficient;
        }
        else
        static if (coefficientSize == 64)
        {
            Unqual!T c = cast(ulong) coefficient;
        }
        else
        {
            enum shift = coefficientSize - T.mant_dig;
            enum rMask = (UInt!coefficientSize(1) << shift) - UInt!coefficientSize(1);
            enum rHalf = UInt!coefficientSize(1) << (shift - 1);
            enum rInc = UInt!coefficientSize(1) << shift;
            UInt!coefficientSize adC = coefficient;
            static if (!noHalf)
            {
                auto cr = (coefficient & rMask).opCmp(rHalf);
                if ((cr > 0) | (cr == 0) & coefficient.bt(shift))
                {
                    if (auto overflow = adC += rInc)
                    {
                        adC = half!coefficientSize;
                        exp++;
                    }
                }
            }
            adC >>= shift;
            exp += shift;
            Unqual!T c = cast(ulong) adC;
            static if (T.mant_dig > 64) //
            {
                static assert (T.mant_dig <= 128);
                c += ldexp(cast(T) cast(ulong) (adC >> 64), 64);
            }
        }
        if (sign)
            c = -c;
        static if (exp.sizeof > int.sizeof)
        {
            import mir.utility: min, max;
            exp = exp.max(int.min).min(int.max);
        }
        return ldexp(c, cast(int)exp);
    }

    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto fp = Fp!128(1, 100, UInt!128.fromHexString("e3251bacb112cb8b71ad3f85a970a314"));
        assert(cast(double)fp == -0xE3251BACB112C8p+172);
    }

    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto fp = Fp!128(1, 100, UInt!128.fromHexString("e3251bacb112cb8b71ad3f85a970a314"));
        static if (real.mant_dig == 64)
            assert(cast(real)fp == -0xe3251bacb112cb8bp+164L);
    }

    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto fp = Fp!64(1, 100, UInt!64(0xe3251bacb112cb8b));
        version (DigitalMars)
        {
            // https://issues.dlang.org/show_bug.cgi?id=20963
            assert(cast(double)fp == -0xE3251BACB112C8p+108
                || cast(double)fp == -0xE3251BACB112D0p+108);
        }
        else
        {
            assert(cast(double)fp == -0xE3251BACB112C8p+108);
        }
    }
// -0x1.c64a375962259p+163 = 
// -0xe.3251bacb112cb8bp+160 = 
// -0x1.c64a37596225ap+163 = 
// -0xe.3251bacb112cb8bp+160 = 
    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto fp = Fp!64(1, 100, UInt!64(0xe3251bacb112cb8b));
        static if (real.mant_dig == 64)
            assert(cast(real)fp == -0xe3251bacb112cb8bp+100L);
    }

    ///
    T opCast(T : Fp!newCoefficientSize, size_t newCoefficientSize)() nothrow const
    {
        auto ret = Fp!newCoefficientSize(coefficient, true);
        ret.exponent += exponent;
        ret.sign = sign;
        return ret;
    }

    static if (coefficientSize == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto fp = cast(Fp!64) Fp!128(UInt!128.fromHexString("afbbfae3cd0aff2784a1de7022b0029d"));
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!64.fromHexString("afbbfae3cd0aff28"));
    }
}

///
Fp!(coefficientizeA + coefficientizeB) extendedMul(size_t coefficientizeA, size_t coefficientizeB)(Fp!coefficientizeA a, Fp!coefficientizeB b)
    @safe pure nothrow @nogc
{
    import mir.bignum.fixed: extendedMul;
    auto coefficient = extendedMul(a.coefficient, b.coefficient);
    auto exponent = a.exponent + b.exponent;
    auto sign = a.sign ^ b.sign;
    if (!coefficient.signBit)
    {
        --exponent;
        coefficient = coefficient.smallLeftShift(1);
    }
    return typeof(return)(sign, exponent, coefficient);
}
