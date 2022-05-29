module mir.bignum.internal.dec2float;

version(LDC) import ldc.attributes: optStrategy;
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

private float decimalToFloat32(scope const size_t[] coefficients)
{
    pragma(inline, false);
    return decimalToFloatImpl!float(coefficients);
}

private double decimalToFloat64(scope const size_t[] coefficients)
{
    pragma(inline, false);
    return decimalToFloatImpl!double(coefficients);
}

private real decimalToReal(scope const size_t[] coefficients)
{
    pragma(inline, real.mant_dig == double.mant_dig);
    static if (real.mant_dig == double.mant_dig)
        return decimalToFloat64(coefficients);
    else
        return decimalToFloatImpl!real(coefficients);
}

T decimalToFloat(T)(ulong coefficient, long exponent)
    if (is(T == real))
{
    version(LDC)
        pragma(inline, true);
    static if (T.mant_dig < 64)
    {
        return decimalToFloat!double(coefficient, exponent);
    }
    else
    {
        auto coefficients = cast(size_t[ulong.sizeof / size_t.sizeof]) cast(ulong[1])[coefficient];
        static if (coefficients.length == 1)
            return decimalTo!real(approx, coefficients[0 .. !!coefficient], exponent);
        else
            return decimalTo!real(approx, coefficients[0 .. !!coefficient + (coefficient > uint.max)], exponent);
    }
}

T decimalToFloat(T)(ulong coefficient, long exponent)
    if (is(T == float) || is(T == double))
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp, extendedMul;
    import mir.utility: _expect;

    version(LDC)
        pragma(inline, true);

    enum ulong mask = (1UL << (64 - T.mant_dig)) - 1;
    enum ulong half = (1UL << (64 - T.mant_dig - 1));
    enum ulong bound = ulong(1) << T.mant_dig;

    auto expSign = exponent < 0;
    if (_expect((expSign ? -exponent : exponent) >>> dec_S == 0, true))
    {
        auto c = Fp!64(UInt!64(coefficient));
        auto z = c.extendedMul(load64(exponent));
        auto approx = cast(T) z;
        long bitsDiff = (cast(ulong) z.opCast!(Fp!64).coefficient & mask) - half;
        if (_expect((bitsDiff < 0 ? -bitsDiff : bitsDiff) > 3 * expSign, true))
            return approx;
        assert(coefficient);
        if (!expSign && exponent <= MaxWordPow5!ulong || exponent == 0)
            return approx;
        if (expSign && MaxFpPow5!T >= -exponent && cast(ulong)c.coefficient < bound)
        {
            auto e = load64(-exponent);
            return c.opCast!(T, true) / cast(T) (cast(ulong)e.coefficient >> e.exponent);
        }
        auto coefficients = cast(size_t[ulong.sizeof / size_t.sizeof]) cast(ulong[1])[coefficient];
        static if (coefficients.length == 1)
            return decimalToFloatFallback(approx, coefficients, cast(int) exponent);
        else
            return decimalToFloatFallback(approx, coefficients[0 .. 1 + (coefficient > uint.max)], cast(int) exponent);
    }
    return expSign ? 0 : exponent != exponent.max ? T.infinity : coefficient ? T.nan : T.infinity;
}

private T decimalToFloatImpl(T)(scope const size_t[] coefficients)
    @safe
    if ((is(T == float) || is(T == double) || is(T == real)))
    in (coefficients.length == 0 || coefficients[$ - 1])
{
    version(LDC)
        pragma(inline, true);

    enum md = T.mant_dig;
    enum b = size_t.sizeof * 8;
    enum n = md / b + (md % b != 0);
    enum s = n * b;

    return coefficients.length ? coefficients.decimalToFp!(s, s - md).opCast!(T, true) : 0;
}

private T decimalToFloatImpl(T)(scope const size_t[] coefficients, long exponent)
    @safe
    if ((is(T == float) || is(T == double) || is(T == real)))
    in (coefficients.length == 0 || coefficients[$ - 1])
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp, extendedMul;
    import mir.math.common: floor;
    import mir.utility: _expect;

    static if (T.mant_dig < 64)
    {
        enum ulong mask = (1UL << (64 - T.mant_dig)) - 1;
        enum ulong half = (1UL << (64 - T.mant_dig - 1));
        enum ulong bound = ulong(1) << T.mant_dig;

        if (coefficients.length == 1)
            return decimalToFloat!T(coefficients[0], exponent);
        if (coefficients.length < 1)
            return exponent == exponent.max ? T.infinity : 0;
        auto expSign = exponent < 0;
        if (_expect((expSign ? -exponent : exponent) >>> dec_S == 0, true))
        {
            auto c = coefficients.decimalToFp!64;
            auto z = c.extendedMul(load64(exponent));
            auto approx = cast(T) z;
            auto slop = (coefficients.length > (ulong.sizeof / size_t.sizeof)) + 3 * expSign;
            long bitsDiff = (cast(ulong) z.opCast!(Fp!64).coefficient & mask) - half;
            if (_expect((bitsDiff < 0 ? -bitsDiff : bitsDiff) > slop, true))
                return approx;
            if (slop == 0 && exponent <= MaxWordPow5!ulong || exponent == 0)
                return approx;
            if (slop == 3 && MaxFpPow5!T >= -exponent && cast(ulong)c.coefficient < bound)
            {
                auto e = load64(-exponent);
                approx =  c.opCast!(T, true) / cast(T) (cast(ulong)e.coefficient >> e.exponent);
                return approx;
            }
            return decimalToFloatFallback(approx, coefficients, cast(int) exponent);
        }
        return expSign ? 0 : exponent != exponent.max ? T.infinity : T.nan;
    }
    else
    {
        if (exponent == 0)
            return decimalTo!T(coefficients);

        if (coefficients.length == 0)
            return exponent == exponent.max ? T.infinity : 0;

        auto expSign = exponent < 0;
        ulong exp = exponent;
        exp = expSign ? -exp : exp;
        if (exp >= 5000)
        {
            return expSign ? 0 : exponent != exponent.max ? T.infinity : T.nan;
        }
        long index = exp & 0x1FF;
        bool gotoAlgoR;
        auto c = load128(expSign ? -index : index);
        {
            exp >>= dec_S;
            gotoAlgoR = exp != 0;
            if (_expect(gotoAlgoR, false))
            {
                auto v = load128(expSign ? -dec_P : dec_P);
                do
                {
                    if (exp & 1)
                        c *= v;
                    exp >>>= 1;
                    if (exp == 0)
                        break;
                    v *= v;
                }
                while(true);
            }
        }
        auto z = coefficients.decimalToFp!128.extendedMul(c);
        auto ret = cast(T) z;
        if (!gotoAlgoR)
        {
            static if (T.mant_dig > 64)
                enum ulong mask = (1UL << (128 - T.mant_dig)) - 1;
            else
                enum ulong mask = ulong.max;
            enum ulong half = (1UL << (128 - T.mant_dig - 1));
            enum UInt!128 bound = UInt!128(1) << T.mant_dig;

            auto slop = (coefficients.length > (ulong.sizeof * 2 / size_t.sizeof)) + 3 * expSign;
            long bitsDiff = (cast(ulong) z.opCast!(Fp!128).coefficient & mask) - half;
            if (_expect((bitsDiff < 0 ? -bitsDiff : bitsDiff) > slop, true))
                return ret;
            if (slop == 0 && exponent <= 55 || exponent == 0)
                return ret;
            if (slop == 3 && MaxFpPow5!T >= -exponent && c.coefficient < bound)
            {
                auto e = load128(-exponent);
                return c.opCast!(T, true) / cast(T) e;
            }
        }
        return decimalToFloatFallback(ret, coefficients, cast(int) exponent);
    }
}

@optStrategy("minsize")
private T decimalToFloatFallback(T)(T ret, scope const size_t[] coeff, int exponent)
    if ((is(T == float) || is(T == double) || is(T == real)))
    in (0 <= ret && ret <= T.infinity)
{
    pragma(inline, false);

    import mir.bignum.fixed: UInt;
    import mir.bignum.integer: BigInt;
    import mir.math.common: floor;
    import mir.math.ieee: ldexp, frexp, nextDown, nextUp;
    import mir.utility: _expect;

    BigInt!256 x = void, y = void; // max value is 2^(2^14)-1

    if (exponent == 0)
        return decimalTo!T(coeff);

    // if no overflow
    if (exponent > 0 && !x.copyFrom(coeff) && !x.mulPow5(exponent))
        return x.coefficients.decimalTo!T.ldexp(exponent);

    do
    {
        if (ret < ret.min_normal)
            break;
        int k;
        auto m0 = frexp(ret, k);
        k -= T.mant_dig;
        static if (T.mant_dig <= 64)
        {
            enum p2 = T(2) ^^ T.mant_dig;
            auto m = UInt!64(cast(ulong) (m0 * p2));
        }
        else
        {
            enum p2h = T(2) ^^ (T.mant_dig - 64);
            enum p2l = T(2) ^^ 64;
            m0 *= p2h;
            auto mhf = floor(m0);
            auto mh = cast(ulong) mhf;
            m0 -= mhf;
            m0 *= p2l;
            auto ml = cast(ulong) m0;
            auto m = UInt!128(mh);
            m <<= 64;
            m |= UInt!128(ml);
        }
        auto mtz = m.cttz;
        if (mtz != m.sizeof * 8)
        {
            m >>= mtz;
            k += mtz;
        }

        if (x.copyFrom(coeff)) // if overflow
            break;
        y = m;
        y.mulPow5(-exponent);
        auto shift = k - exponent;
        (shift >= 0  ? y : x) <<= shift >= 0 ? shift : -shift;
        x -= y;
        if (x.length == 0)
            break;
        x <<= 1;
        x *= m;
        auto cond = mtz == T.mant_dig - 1 && x.sign;
        auto cmp = x.view.unsigned.opCmp(y.view.unsigned);
        if (cmp < 0)
        {
            if (!cond)
                break;
            x <<= 1;
            if (x.view.unsigned <= y.view.unsigned)
                break;
        }
        else
        if (!cmp && !cond && !mtz)
            break;
        ret = x.sign ? nextDown(ret) : nextUp(ret);
        if (ret == 0)
            break;
    }
    while (T.mant_dig >= 64 && exponent < -512);
    return ret;
}

auto decimalToFp(uint coefficientSize, uint internalRoundLastBits = 0)
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
        pragma(inline, internalRoundLastBits != 0);

    Fp!coefficientSize ret;

    assert(coefficients.length);
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
            return coefficients.length > (N + 1);
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

private enum dec_S = 9;
private enum dec_P = 1 << dec_S;

private auto load64()(long e)
{
    version(LDC)
        pragma(inline, true);

    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp;
    import mir.bignum.internal.dec2float_table;

    auto p10coeff = p10_coefficients[cast(sizediff_t)e - min_p10_e][0];
    auto p10exp = p10_exponents[cast(sizediff_t)e - min_p10_e];
    return Fp!64(false, p10exp, UInt!64(p10coeff));
}

private auto load128()(long e)
{
    version(LDC)
        pragma(inline, true);

    import mir.bignum.fixed: UInt;
    import mir.bignum.fp: Fp;
    import mir.bignum.internal.dec2float_table;

    static assert(min_p10_e <= -dec_P);
    static assert(max_p10_e >= dec_P);
    auto idx = cast(sizediff_t)e - min_p10_e;
    ulong h = p10_coefficients[idx][0];
    ulong l = p10_coefficients[idx][1];
    if (l >= cast(ulong)long.min)
        h--;
    auto p10coeff = UInt!128(cast(ulong[2])[l, h]);
    auto p10exp = p10_exponents[idx] - 64;
    return Fp!128(false, p10exp, p10coeff);
}
