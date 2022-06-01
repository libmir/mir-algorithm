module mir.bignum.internal.dec2float;

version (LDC) import ldc.attributes: optStrategy;
else struct optStrategy { string opt; }

template MaxWordPow5(T)
{
    static if (is(T == ubyte))
        enum MaxWordPow5 = 3;
    else
    static if (is(T == ushort))
        enum MaxWordPow5 = 6;
    else
    static if (is(T == uint))
        enum MaxWordPow5 = 13;
    else
    static if (is(T == ulong))
        enum MaxWordPow5 = 27;
    else
        static assert(0);
}

template MaxFpPow5(T)
{
    static if (T.mant_dig == 24)
        enum MaxFpPow5 = 6;
    else
    static if (T.mant_dig == 53)
        enum MaxFpPow5 = 10;
    else
    static if (T.mant_dig == 64)
        enum MaxFpPow5 = 27;
    else
    static if (T.mant_dig == 113)
        enum MaxFpPow5 = 48;
    else
        static assert(0, "floating point format isn't supported");
}

@safe pure nothrow @nogc:

alias decimalTo(T : float) = decimalToFloat32;
alias decimalTo(T : double) = decimalToFloat64;
alias decimalTo(T : real) = decimalToReal;

alias binaryTo(T : float) = binaryToFloat32;
alias binaryTo(T : double) = binaryToFloat64;
alias binaryTo(T : real) = binaryToReal;

private float binaryToFloat32(scope const size_t[] coefficients, long exponent = 0)
{
    pragma(inline, false);
    return binaryToFloatImpl!float(coefficients, exponent);
}

private double binaryToFloat64(scope const size_t[] coefficients, long exponent = 0)
{
    pragma(inline, false);
    return binaryToFloatImpl!double(coefficients, exponent);
}

private real binaryToReal(scope const size_t[] coefficients, long exponent = 0)
{
    pragma(inline, real.mant_dig == double.mant_dig);
    static if (real.mant_dig == double.mant_dig)
        return binaryToFloat64(coefficients, exponent);
    else
        return binaryToFloatImpl!real(coefficients, exponent);
}

private float decimalToFloat32(scope const ulong coefficient, long exponent)
{
    pragma(inline, false);
    return decimalToFloatImpl!float(coefficient, exponent);
}

private double decimalToFloat64(scope const ulong coefficient, long exponent)
{
    pragma(inline, false);
    return decimalToFloatImpl!double(coefficient, exponent);
}

private real decimalToReal(scope const ulong coefficient, long exponent)
{
    pragma(inline, real.mant_dig == double.mant_dig);
    static if (real.mant_dig == double.mant_dig)
        return decimalToFloat64(coefficient, exponent);
    else
        return decimalToFloatImpl!real(coefficient, exponent);
}

private float decimalToFloat32(scope const size_t[] coefficients, long exponent)
{
    pragma(inline, false);
    return decimalToFloatImpl!float(coefficients, exponent);
}

private double decimalToFloat64(scope const size_t[] coefficients, long exponent)
{
    pragma(inline, false);
    return decimalToFloatImpl!double(coefficients, exponent);
}

private real decimalToReal(scope const size_t[] coefficients, long exponent)
{
    pragma(inline, real.mant_dig == double.mant_dig);
    static if (real.mant_dig == double.mant_dig)
        return decimalToFloat64(coefficients, exponent);
    else
        return decimalToFloatImpl!real(coefficients, exponent);
}

T decimalToFloatImpl(T)(ulong coefficient, long exponent)
    if (is(T == float) || is(T == double) || is(T == real))
{
    version (LDC)
        pragma(inline, true);

    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp, extendedMul;
    import mir.utility: _expect;

    enum wordBits = T.mant_dig < 64 ? 64 : 128;
    enum ulong half = (1UL << (wordBits - T.mant_dig - 1));
    enum bigHalf = UInt!128([0UL, half]);
    enum bigMask = (1UL << (64 - T.mant_dig)) - 1;

    static if (T.mant_dig > 64)
        enum ulong mask = (1UL << (128 - T.mant_dig)) - 1;
    else
    static if (T.mant_dig == 64)
        enum ulong mask = ulong.max;
    else
        enum ulong mask = bigMask;
    
    if (coefficient == 0)
        return 0;

    version (TeslAlgoM) {} else
    if (_expect(-ExponentM <= exponent && exponent <= ExponentM, true))
    {
        auto c = coefficient.Fp!64;
        version (all)
        {{
            auto z = c.extendedMul!true(_load!wordBits(exponent));
            auto approx = z.opCast!(T, true);
            long bitsDiff = (cast(ulong) z.opCast!(Fp!wordBits).coefficient & mask) - half;
            uint slop = 3 * (exponent < 0);
            if (_expect(approx > T.min_normal && (bitsDiff < 0 ? -bitsDiff : bitsDiff) > slop, true))
                return approx;
        }}
        static if (T.mant_dig < 64)
        {
            auto z = c.extendedMul!true(_load!128(exponent));
            auto approx = z.opCast!(T, true);
            auto bitsDiff = (z.opCast!(Fp!128).coefficient & bigMask) - bigHalf;
            if (bitsDiff.signBit)
                bitsDiff = UInt!128.init - bitsDiff;
            uint slop = 3 * (exponent < 0);
            if (_expect(approx > T.min_normal && bitsDiff > slop, true))
                return approx;
        }

        if (0 <= exponent)
        {
            if (exponent <= 55) // exact exponent
                return approx;
        }
        else
        {
            if (-exponent <= MaxFpPow5!T)
            {
                auto e = _load!wordBits(-exponent);
                return coefficient / e.opCast!(T, true);
            }
        }
    }
    size_t[ulong.sizeof / size_t.sizeof] coefficients;
    coefficients[0] = cast(size_t) coefficient;
    static if (coefficients.length == 2)
        coefficients[1] = cast(size_t) (coefficient >> 32);
    static if (coefficients.length == 1)
        return algorithmM!T(coefficients, exponent);
    else
        return algorithmM!T(coefficients[0 .. 1 + (coefficient > uint.max)], exponent);
}

private T decimalToFloatImpl(T)(scope const size_t[] coefficients, long exponent)
    @safe
    if ((is(T == float) || is(T == double) || is(T == real)))
    in (coefficients.length == 0 || coefficients[$ - 1])
{
    version (LDC)
        pragma(inline, true);

    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp, extendedMul;
    import mir.utility: _expect;

    enum wordBits = T.mant_dig < 64 ? 64 : 128;
    enum ulong half = (1UL << (wordBits - T.mant_dig - 1));
    static if (T.mant_dig > 64)
        enum ulong mask = (1UL << (128 - T.mant_dig)) - 1;
    else
    static if (T.mant_dig == 64)
        enum ulong mask = ulong.max;
    else
        enum ulong mask = (1UL << (64 - T.mant_dig)) - 1;

    if (coefficients.length < 1)
        return 0;

    if (coefficients.length == 1)
        return decimalTo!T(coefficients[0], exponent);

    static if (size_t.sizeof == uint.sizeof)
    {
        if (coefficients.length == 2)
            return decimalTo!T(coefficients[0] | (ulong(coefficients[1]) << 32), exponent);
    }

    version (TeslAlgoM) {} else
    if (_expect(-ExponentM <= exponent && exponent <= ExponentM, true))
    {
        auto c = coefficients.binaryToFp!wordBits;
        auto z = c.extendedMul!true(_load!wordBits(exponent));
        auto approx = z.opCast!(T, true);
        auto slop = 1 + 3 * (exponent < 0);
        long bitsDiff = (cast(ulong) z.opCast!(Fp!wordBits).coefficient & mask) - half;

        if (_expect(approx > T.min_normal && (bitsDiff < 0 ? -bitsDiff : bitsDiff) > slop, true))
            return approx;
    }
    return algorithmM!T(coefficients, exponent);
}

private enum LOG2_10 = 0x3.5269e12f346e2bf924afdbfd36bf6p0;

private template bigSize(T)
    if ((is(T == float) || is(T == double) || is(T == real)))
{
    static if (T.mant_dig < 64)
    {
        enum size_t bigSize = 83;
    }
    else
    {
        enum size_t bits = T.max_exp - T.min_exp + T.mant_dig;
        enum size_t bigSize = bits / 64 + bits % 64 + 1;
        pragma(msg, "bigSize = ", bigSize);
    }
}

@optStrategy("minsize")
private T algorithmM(T)(scope const size_t[] coefficients, long exponent)
    if ((is(T == float) || is(T == double) || is(T == real)))
    in (coefficients.length)
{
    pragma(inline, false);

    // import mir.stdio;
    // debug dump("algorithmM", coefficients, exponent);

    import mir.bitop: ctlz;
    import mir.bignum.fp: Fp;
    import mir.bignum.integer: BigInt;
    import mir.math.common: log2, ceil;
    import mir.math.ieee: ldexp, nextUp;

    BigInt!(bigSize!T) u = void;
    BigInt!(bigSize!T) v = void;
    BigInt!(bigSize!T) q = void;
    BigInt!(bigSize!T) r = void;

    if (coefficients.length == 0)
        return 0;

    // if no overflow
    if (exponent >= 0)
    {
        if (3 * exponent + coefficients.length * size_t.sizeof * 8 - ctlz(coefficients[$ - 1]) - 1 > T.max_exp)
            return T.infinity;
        if (exponent == 0)
            return coefficients.binaryTo!T;
        u.copyFrom(coefficients);
        u.mulPow5(exponent);
        return u.coefficients.binaryTo!T(exponent);
    }

    auto log2_u = coefficients.binaryTo!T.log2;
    auto log2_v = cast(T)(-LOG2_10) * exponent;
    sizediff_t k = cast(sizediff_t) ceil(log2_u - log2_v);

    k -= T.mant_dig;

    if (k < T.min_exp - T.mant_dig)
    {
        if (k + T.mant_dig + 1 < T.min_exp - T.mant_dig)
            return 0;
        k = T.min_exp - T.mant_dig;
    }
    else
    if (k > T.max_exp)
    {
        if (k - 2 > T.max_exp)
            return T.infinity;
        k = T.max_exp;
    }

    if(u.copyFrom(coefficients))
        return T.nan;
    if (k < 0)
    {
        if (u.ctlz < -k)
            return T.nan;
        u <<= -k;
    }

    if (log2_v >= bigSize!T * 64)
            return T.nan;

    v = 1;
    v.mulPow5(-exponent);
    v <<= cast(int)-exponent + (k > 0 ? k : 0);

    sizediff_t s;
    for(;;)
    {
        u.divMod(v, q, r);

        s = cast(int) q.bitLength - T.mant_dig;
        assert(k >= T.min_exp - T.mant_dig);
        if (s == 0)
            break;

        if (s < 0)
        {
            if (k == T.min_exp - T.mant_dig)
                break;
            k--;
        }
        else
        {
            if (k == T.max_exp)
                return T.infinity;
            k++;
        }

        if ((s < 0 ? u : v).ctlz == 0)
            return T.nan;
        (s < 0 ? u : v) <<= 1;
    }

    sizediff_t cmp;
    if (s <= 0)
    {
        u = v;
        u -= r;
        cmp = r.opCmp(u);
    }
    else
    {
        cmp = s - 1 - q.view.unsigned.cttz;
        if (cmp == 0) // half
            cmp += r != 0;
        q >>= s;
        k += s;
    }
    auto z = q.coefficients.binaryTo!T.ldexp(cast(int)k);
    return cmp < 0 || cmp == 0 && !q.view.unsigned.bt(0) ? z : nextUp(z);
}

private T binaryToFloatImpl(T)(scope const size_t[] coefficients, long exponent)
    @safe
    if ((is(T == float) || is(T == double) || is(T == real)))
    in (coefficients.length == 0 || coefficients[$ - 1])
{
    version (LDC)
        pragma(inline, true);

    enum md = T.mant_dig;
    enum b = size_t.sizeof * 8;
    enum n = md / b + (md % b != 0);
    enum s = n * b;

    if (coefficients.length == 0)
        return 0;
    
    if (exponent > T.max_exp)
        return T.infinity;

    auto fp = coefficients.binaryToFp!(s, s - md);
    fp.exponent += exponent;
    return fp.opCast!(T, true, true);
}


package(mir.bignum) auto binaryToFp(uint coefficientSize, uint internalRoundLastBits = 0)
    (scope const(size_t)[] coefficients)
    if (internalRoundLastBits < size_t.sizeof * 8)
    in (coefficients.length)
    in (coefficients[$ - 1])
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp;
    import mir.bitop: ctlz;
    import mir.utility: _expect;

    version (LDC)
        pragma(inline, true);

    Fp!coefficientSize ret;

    enum N = ret.coefficient.data.length;
    sizediff_t size = coefficients.length * (size_t.sizeof * 8);
    sizediff_t expShift = size - coefficientSize;
    ret.exponent = expShift;
    if (_expect(expShift <= 0, true))
    {
        static if (N == 1)
        {
            ret.coefficient.data[0] = coefficients[$ - 1];
        }
        else
        {
            ret.coefficient.data[$ - coefficients.length .. $] = coefficients;
        }
        auto c = cast(uint) ctlz(ret.coefficient.view.coefficients[$ - 1]);
        ret.exponent -= c;
        ret.coefficient = ret.coefficient.smallLeftShift(c);
    }
    else
    {
        UInt!(coefficientSize + size_t.sizeof * 8) holder;

        static if (N == 1)
        {
            holder.data[0] = coefficients[$ - 2];
            holder.data[1] = coefficients[$ - 1];
        }
        else
        {
            import mir.utility: min;
            auto minLength = min(coefficients.length, holder.data.length);
            holder.data[$ - minLength .. $] = coefficients[$ - minLength .. $];
        }

        auto c = cast(uint) ctlz(holder.data[$ - 1]);
        ret.exponent -= c;
        holder = holder.smallLeftShift(c);
        ret.coefficient = holder.toSize!(coefficientSize, false);
        auto tail = holder.data[0];

        bool nonZeroTail()
        {
            while(_expect(coefficients[0] == 0, false))
            {
                coefficients = coefficients[1 .. $];
                assert(coefficients.length);
            }
            return coefficients.length > N + 1;
        }

        static if (internalRoundLastBits)
        {
            enum half = size_t(1) << (internalRoundLastBits - 1);
            enum mask0 = (size_t(1) << internalRoundLastBits) - 1;
            auto tail0 = ret.coefficient.data[0] & mask0;
            ret.coefficient.data[0] &= ~mask0;
            auto condInc = tail0 >= half
                && (   tail0 > half
                    || tail
                    || (ret.coefficient.data[0] & 1)
                    || nonZeroTail);
        }
        else
        {
            enum half = cast(size_t)sizediff_t.min;
            auto condInc = tail >= half
                && (    tail > half
                    || (ret.coefficient.data[0] & 1)
                    || nonZeroTail);
        }

        if (condInc)
        {
            enum inc = size_t(1) << internalRoundLastBits;
            if (auto overflow = ret.coefficient += inc)
            {
                import mir.bignum.fp: half;
                ret.coefficient = half!coefficientSize;
                ret.exponent++;
            }
        }
    }
    return ret;
}

private enum ExponentM = 512;

private auto _load(uint size : 64)(long e) @trusted
    in (-ExponentM < e && e < ExponentM)
{
    version (LDC)
        pragma(inline, true);

    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp;
    import mir.bignum.internal.dec2float_table;

    auto idx = cast(sizediff_t)e - min_p10_e;
    auto p10coeff = p10_coefficients_h[idx];
    auto p10exp = p10_exponents[idx];
    return Fp!64(false, p10exp, UInt!64(p10coeff));
}

private auto _load(uint size : 128)(long e) @trusted
    in (-ExponentM < e && e < ExponentM)
{
    version (LDC)
        pragma(inline, true);

    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp;
    import mir.bignum.internal.dec2float_table;

    static assert(min_p10_e <= -ExponentM);
    static assert(max_p10_e >= ExponentM);
    auto idx = cast(sizediff_t)e - min_p10_e;
    ulong h = p10_coefficients_h[idx];
    ulong l = p10_coefficients_l[idx];
    if (l >= cast(ulong)long.min)
        h--;
    auto p10coeff = UInt!128(cast(ulong[2])[l, h]);
    auto p10exp = p10_exponents[idx] - 64;
    return Fp!128(false, p10exp, p10coeff);
}

unittest
{
    import mir.bignum.fp;
    import mir.bignum.fixed;
    import mir.test;
    ulong[2] data = [ulong.max - 2, 1];
    auto coefficients = cast(size_t[])data[];
    if (coefficients[$ - 1] == 0)
        coefficients = coefficients[0 .. $ - 1];
    coefficients.binaryToFp!64.should == Fp!64(false, 1, UInt!64(0xFFFFFFFFFFFFFFFE));
    coefficients.binaryToFp!128.should == Fp!128(false, -63, UInt!128([0x8000000000000000, 0xFFFFFFFFFFFFFFFE]));
}
