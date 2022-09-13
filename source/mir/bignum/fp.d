/++
Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.fp;

import mir.bitop;
import mir.utility;
import std.traits;

package enum half(uint hs) = (){
    import mir.bignum.fixed: UInt;
    UInt!hs ret; ret.signBit = true; return ret;
}();

/++
Software floating point number.

Params:
    size = coefficient size in bits
+/
struct Fp(uint size)
    if (size % (uint.sizeof * 8) == 0 && size >= (uint.sizeof * 8))
{
    import mir.bignum.fixed: UInt;

    bool sign;
    long exponent;
    UInt!size coefficient;

    /++
    +/
    nothrow
    this(bool sign, long exponent, UInt!size normalizedCoefficient)
    {
        this.coefficient = normalizedCoefficient;
        this.exponent = exponent;
        this.sign = sign;
    }

    /++
    Constructs $(LREF Fp) from hardaware floating  point number.
    Params:
        value = Hardware floating point number. Special values `nan` and `inf` aren't allowed.
        normalize = flag to indicate if the normalization should be performed.
    +/
    this(T)(const T value, bool normalize = true)
        @safe pure nothrow @nogc
        if (isFloatingPoint!T && T.mant_dig <= size)
    {
        import mir.math.common : fabs;
        import mir.math.ieee : frexp, signbit, ldexp;
        this.sign = value.signbit != 0;
        if (value == 0)
            return;
        T x = value.fabs;
        if (_expect(!(x < T.infinity), false))
        {
            this.exponent = this.exponent.max;
            this.coefficient = x != T.infinity;
            return;
        }
        int exp;
        {
            enum scale = T(2) ^^ T.mant_dig;
            x = frexp(x, exp) * scale;
        }

        static if (T.mant_dig < 64)
        {
            auto xx = cast(ulong)cast(long)x;
            if (normalize)
            {
                auto shift = ctlz(xx);
                exp -= shift + T.mant_dig + size - 64;
                xx <<= shift;
                this.coefficient = UInt!64(xx).rightExtend!(size - 64);
            }
            else
            {
                this.coefficient = xx;
            }
        }
        else
        static if (T.mant_dig == 64)
        {
            auto xx = cast(ulong)x;
            if (normalize)
            {
                auto shift = ctlz(xx);
                exp -= shift + T.mant_dig + size - 64;
                xx <<= shift;
                this.coefficient = UInt!64(xx).rightExtend!(size - 64);
            }
            else
            {
                this.coefficient = xx;
            }
        }
        else
        {
            enum scale = T(2) ^^ 64;
            enum scaleInv = 1 / scale;
            x *= scaleInv;
            long high = cast(long) x;
            if (high > x)
                --high;
            x -= high;
            x *= scale;
            auto most = ulong(high);
            auto least = cast(ulong)x;
            version(LittleEndian)
                ulong[2] pair = [least, most];
            else
                ulong[2] pair = [most, least];

            if (normalize)
            {
                this.coefficient = UInt!128(pair).rightExtend!(size - 128);
                auto shift = most ? ctlz(most) : ctlz(least) + 64;
                exp -= shift + T.mant_dig + size - 64 * (1 + (T.mant_dig > 64));
                this.coefficient <<= shift;
            }
            else
            {
                this.coefficient = pair;
            }
        }
        if (!normalize)
        {
            exp -= T.mant_dig;
            int shift = T.min_exp - T.mant_dig - exp;
            if (shift > 0)
            {
                this.coefficient >>= shift;
                exp = T.min_exp - T.mant_dig;
            }
        }
        this.exponent = exp;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc nothrow
    unittest
    {
        enum h = -33.0 * 2.0 ^^ -10;
        auto f = Fp!64(h);
        assert(f.sign);
        assert(f.exponent == -10 - (64 - 6));
        assert(f.coefficient == 33UL << (64 - 6));
        assert(cast(double) f == h);

        // CTFE
        static assert(cast(double) Fp!64(h) == h);

        f = Fp!64(-0.0);
        assert(f.sign);
        assert(f.exponent == 0);
        assert(f.coefficient == 0);

        // subnormals
        static assert(cast(float) Fp!64(float.min_normal / 2) == float.min_normal / 2);
        static assert(cast(float) Fp!64(float.min_normal * float.epsilon) == float.min_normal * float.epsilon);
        // subnormals
        static assert(cast(double) Fp!64(double.min_normal / 2) == double.min_normal / 2);
        static assert(cast(double) Fp!64(double.min_normal * double.epsilon) == double.min_normal * double.epsilon);
        // subnormals
        static if (real.mant_dig <= 64)
        {
            static assert(cast(real) Fp!128(real.min_normal / 2) == real.min_normal / 2);
            static assert(cast(real) Fp!128(real.min_normal * real.epsilon) == real.min_normal * real.epsilon);
        }

        enum d = cast(float) Fp!64(float.min_normal / 2, false);

        // subnormals
        static assert(cast(float) Fp!64(float.min_normal / 2, false) == float.min_normal / 2, d.stringof);
        static assert(cast(float) Fp!64(float.min_normal * float.epsilon, false) == float.min_normal * float.epsilon);
        // subnormals
        static assert(cast(double) Fp!64(double.min_normal / 2, false) == double.min_normal / 2);
        static assert(cast(double) Fp!64(double.min_normal * double.epsilon, false) == double.min_normal * double.epsilon);
        // subnormals
        static if (real.mant_dig <= 64)
        {
            static assert(cast(real) Fp!64(real.min_normal / 2, false) == real.min_normal / 2);
            static assert(cast(real) Fp!64(real.min_normal * real.epsilon, false) == real.min_normal * real.epsilon);
        }

        import mir.bignum.fixed: UInt;

        assert(cast(double)Fp!128(+double.infinity) == +double.infinity);
        assert(cast(double)Fp!128(-double.infinity) == -double.infinity);

        import mir.math.ieee : signbit;
        auto r = cast(double)Fp!128(-double.nan);
        assert(r != r && r.signbit);
    }

    // static if (size == 128)
    // /// Without normalization
    // version(mir_bignum_test)
    // @safe pure @nogc nothrow
    // unittest
    // {
    //     auto f = Fp!64(-33.0 * 2.0 ^^ -10, false);
    //     assert(f.sign);
    //     assert(f.exponent == -10 - (double.mant_dig - 6));
    //     assert(f.coefficient == 33UL << (double.mant_dig - 6));
    // }

    /++
    +/
    this(uint isize)(UInt!isize integer, bool normalizedInteger = false)
        nothrow
    {
        import mir.bignum.fixed: UInt;
        static if (isize < size)
        {
            if (normalizedInteger)
            {
                this(false, long(isize) - size, integer.rightExtend!(size - isize));
            }
            else
            {
                this(integer.toSize!size, false);
            }
        }
        else
        {
            if (!integer)
                return;
            this.exponent = isize - size;
            if (!normalizedInteger)
            {
                auto c = integer.ctlz;
                integer <<= c;
                this.exponent -= c;
            }
            static if (isize == size)
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
                enum tailSize = isize - size;
                auto cr = integer.toSize!tailSize.opCmp(half!tailSize);
                if (cr > 0 || cr == 0 && coefficient.bt(0))
                {
                    if (auto overflow = coefficient += 1)
                    {
                        coefficient = half!size;
                        exponent++;
                    }
                }
            }
        }
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.fixed: UInt;

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

    /// ditto
    this(ulong value)
    {
        this(UInt!64(value));
    }

    ///
    this(long value)
    {
        this(ulong(value >= 0 ? value : -value));
        this.sign = !(value >= 0);
    }

    ///
    this(int value)
    {
        this(long(value));
    }

    ///
    this(uint value)
    {
        this(ulong(value));
    }

    ///
    bool isNaN() scope const @property
    {
        return this.exponent == this.exponent.max && this.coefficient != this.coefficient.init;
    }

    ///
    bool isInfinity() scope const @property
    {
        return this.exponent == this.exponent.max && this.coefficient == coefficient.init;
    }

    ///
    bool isSpecial() scope const @property
    {
        return this.exponent == this.exponent.max;
    }

    ///
    bool opEquals(const Fp rhs) scope const
    {
        if (this.exponent != rhs.exponent)
            return false;
        if (this.coefficient != rhs.coefficient)
            return false;
        if (this.coefficient == 0)
            return !this.isSpecial || this.sign == rhs.sign;
        if (this.sign != rhs.sign)
            return false;
        return !this.isSpecial;
    }

    ///
    ref Fp opOpAssign(string op)(Fp rhs) nothrow scope return
        if (op == "*" || op == "/")
    {
        this = this.opBinary!op(rhs);
        return this;
    }

    ///
    Fp!(max(size, rhsSize)) opBinary(string op : "*", uint rhsSize)(Fp!rhsSize rhs) nothrow const
    {
        return cast(Fp) .extendedMul(cast()this, rhs);
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.fixed: UInt;

        auto a = Fp!128(0, -13, UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d"));
        auto b = Fp!128(1, 100, UInt!128.fromHexString("e3251bacb112c88b71ad3f85a970a314"));
        auto fp = a.opBinary!"*"(b);
        assert(fp.sign);
        assert(fp.exponent == 100 - 13 + 128);
        assert(fp.coefficient == UInt!128.fromHexString("c6841dd302415d785373ab6d93712988"));
    }

    /// Uses approximate division for now
    /// TODO: use full precision division for void when Fp division is ready
    Fp!(max(size, rhsSize)) opBinary(string op : "/", uint rhsSize)(Fp!rhsSize rhs) nothrow const
    {
        Fp a = this;
        alias b = rhs;
        auto exponent = a.exponent - b.exponent;
        a.exponent = b.exponent = -long(size);
        auto ret = typeof(return)(cast(real) a / cast(real) b);
        ret.exponent += exponent;
        return ret;
    }

    ///
    T opCast(T)() nothrow const
        if (is(Unqual!T == bool))
    {
        return exponent || coefficient;
    }
    
    ///
    T opCast(T, bool noSpecial = false, bool noHalf = false)() nothrow const
        if (is(T == float) || is(T == double) || is(T == real))
    {
        import mir.math.ieee: ldexp;
        static if (!noSpecial)
        {
            if (_expect(this.isSpecial, false))
            {
                T ret = this.coefficient ? T.nan : T.infinity;
                if (this.sign)
                    ret = -ret;
                return ret;
            }
        }
        auto exp = cast()this.exponent;
        static if (size == 32)
        {
            T c = cast(uint) coefficient;
        }
        else
        static if (size == 64)
        {
            T c = cast(ulong) coefficient;
        }
        else
        {
            enum shift = size - T.mant_dig;
            enum rMask = (UInt!size(1) << shift) - UInt!size(1);
            enum rHalf = UInt!size(1) << (shift - 1);
            enum rInc = UInt!size(1) << shift;
            UInt!size adC = this.coefficient;
            static if (!noHalf)
            {
                auto cr = (this.coefficient & rMask).opCmp(rHalf);
                if ((cr > 0) | (cr == 0) & this.coefficient.bt(shift))
                {
                    if (auto overflow = adC += rInc)
                    {
                        adC = half!size;
                        exp++;
                    }
                }
            }
            adC >>= shift;
            exp += shift;
            T c = cast(ulong) adC;
            static if (T.mant_dig > 64) //
            {
                static assert (T.mant_dig <= 128);
                c += ldexp(cast(T) cast(ulong) (adC >> 64), 64);
            }
        }
        if (this.sign)
            c = -c;
        static if (exp.sizeof > int.sizeof)
        {
            import mir.utility: min, max;
            exp = exp.max(int.min).min(int.max);
        }
        return ldexp(c, cast(int)exp);
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.fixed: UInt;
        auto fp = Fp!128(1, 100, UInt!128.fromHexString("e3251bacb112cb8b71ad3f85a970a314"));
        assert(cast(double)fp == -0xE3251BACB112C8p+172);

        fp = Fp!128(1, long.max, UInt!128.init);
        assert(cast(double)fp == -double.infinity);

        import mir.math.ieee : signbit;
        fp = Fp!128(1, long.max, UInt!128(123));
        auto r = cast(double)fp;
        assert(r != r && r.signbit);
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.fixed: UInt;
        auto fp = Fp!128(1, 100, UInt!128.fromHexString("e3251bacb112cb8b71ad3f85a970a314"));
        static if (real.mant_dig == 64)
            assert(cast(real)fp == -0xe3251bacb112cb8bp+164L);
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.fixed: UInt;
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
    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.fixed: UInt;
        auto fp = Fp!64(1, 100, UInt!64(0xe3251bacb112cb8b));
        static if (real.mant_dig == 64)
            assert(cast(real)fp == -0xe3251bacb112cb8bp+100L);
    }

    ///
    T opCast(T : Fp!newSize, bool noSpecial = false, size_t newSize)() nothrow const
        if (newSize != size)
    {
        Fp!newSize ret;
        ret.sign = this.sign;

        static if (!noSpecial)
        {
            if (_expect(this.isSpecial, false))
            {
                ret.exponent = ret.exponent.max;
                ret.coefficient = !!this.coefficient;
                return ret;
            }
            if (!this)
            {
                return ret;
            }
        }

        UInt!size coefficient = this.coefficient;
        int shift;
        // subnormal

        static if (!noSpecial)
        {
            if (this.exponent == this.exponent.min)
            {
                shift = cast(int)coefficient.ctlz;
                coefficient <<= shift;
            }
        }

        ret = Fp!newSize(coefficient, true);
        ret.exponent -= shift;
        ret.sign = this.sign;

        import mir.checkedint: adds;
        /// overflow

        static if (!noSpecial)
        {
            bool overflow;
            ret.exponent = adds(ret.exponent, this.exponent, overflow);
            if (_expect(overflow, false))
            {
                // overflow
                if (this.exponent > 0)
                {
                    ret.exponent = ret.exponent.max;
                    ret.coefficient = 0u;
                }
                // underflow
                else
                {
                    ret.coefficient >>= cast(uint)(ret.exponent - exponent.min);
                    ret.exponent = ret.coefficient ? ret.exponent.min : 0;
                }
            }
        }
        else
        {
            ret.exponent += this.exponent;
        }
        return ret;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.fixed: UInt;
        auto fp = cast(Fp!64) Fp!128(UInt!128.fromHexString("afbbfae3cd0aff2784a1de7022b0029d"));
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!64.fromHexString("afbbfae3cd0aff28"));

        assert(Fp!128(-double.infinity) * Fp!128(1) == Fp!128(-double.infinity));
    }
}

///
Fp!(coefficientizeA + coefficientizeB) extendedMul(bool noSpecial = false, uint coefficientizeA, uint coefficientizeB)(Fp!coefficientizeA a, Fp!coefficientizeB b)
    @safe pure nothrow @nogc
{
    import mir.bignum.fixed: extendedMul;
    import mir.checkedint: adds;

    typeof(return) ret = void;
    ret.coefficient = extendedMul(a.coefficient, b.coefficient);
    static if (noSpecial)
    {
        ret.exponent = a.exponent + b.exponent;
        if (!ret.coefficient.signBit)
        {
            ret.exponent -= 1; // check overflow
            ret.coefficient = ret.coefficient.smallLeftShift(1);
        }
    }
    else
    {
        // nan * any -> nan
        // inf * fin -> inf
        if (_expect(a.isSpecial | b.isSpecial, false))
        {   // set nan
            ret.exponent = ret.exponent.max;
            // nan inf case
            if (a.isSpecial & b.isSpecial)
                ret.coefficient = a.coefficient | b.coefficient;
        }
        else
        {
            bool overflow;
            ret.exponent = adds(a.exponent, b.exponent, overflow);
            // exponent underflow -> 0 or subnormal
            // overflow -> inf
            if (_expect(overflow, false))
            {
                // overflow
                if (a.exponent > 0) //  && b.exponent > 0 is always true
                {
                    ret.exponent = ret.exponent.max;
                    ret.coefficient = 0;
                }
                //  underflow
                else // a.exponent < 0 and b.exponent < 0
                {
                    // TODO: subnormal
                    ret.exponent = 0;
                    ret.coefficient = 0;
                }
            }
            else
            if (!ret.coefficient.signBit)
            {
                auto normal = ret.exponent != ret.exponent.min;
                ret.exponent -= normal; // check overflow
                ret.coefficient = ret.coefficient.smallLeftShift(normal);
            }
        }
    }
    ret.sign = a.sign ^ b.sign;
    return ret;
}

///
template fp_log2(T)
    if (is(T == float) || is(T == double) || is(T == real))
{
    ///
    T fp_log2(uint size)(Fp!size x)
    {
        import mir.math.common: log2;
        auto exponent = x.exponent + size;
        if (!x.isSpecial)
            x.exponent = -long(size);
        return log2(cast(T)x) + exponent;
    }
}

///
version(mir_bignum_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: log2, approxEqual;
    import mir.bignum.fp: fp_log2;

    double x = 123456789.0e+123;
    assert(approxEqual(x.Fp!128.fp_log2!double, x.log2));
}

///
template fp_log(T)
    if (is(T == float) || is(T == double) || is(T == real))
{
    ///
    T fp_log(uint size)(Fp!size x)
    {
        import mir.math.constant: LN2;
        return T(LN2) * fp_log2!T(x);
    }
}

///
version(mir_bignum_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: log, approxEqual;
    import mir.bignum.fp: fp_log;

    double x = 123456789.0e+123;
    assert(approxEqual(x.Fp!128.fp_log!double, x.log));
}
