/++
Low-level betterC utilities for big integer arithmetic libraries.

The module provides $(REF BigUIntAccumulator), $(REF BigUIntView), and $(LREF BigIntView),  $(REF DecimalView).

Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.low_level_view;

import mir.checkedint;
import std.traits;

version(LDC) import ldc.attributes: optStrategy;
else struct optStrategy { string opt; }

private alias cop(string op : "-") = subu;
private alias cop(string op : "+") = addu;
private enum inverseSign(string op) = op == "+" ? "-" : "+";

package immutable hexStringErrorMsg = "Incorrect hex string for BigUIntView.fromHexString";
package immutable binaryStringErrorMsg = "Incorrect binary string for BigUIntView.fromBinaryString";
version (D_Exceptions)
{
    package immutable hexStringException = new Exception(hexStringErrorMsg);
    package immutable binaryStringException = new Exception(binaryStringErrorMsg);
}

/++
+/
enum WordEndian
{
    ///
    little,
    ///
    big,
}

version(LittleEndian)
{
    /++
    +/
    enum TargetEndian = WordEndian.little;
}
else
{
    /++
    +/
    enum TargetEndian = WordEndian.big;
}

package template MaxWordPow10(T)
{
    static if (is(T == ubyte))
        enum MaxWordPow10 = 2;
    else
    static if (is(T == ushort))
        enum MaxWordPow10 = 4;
    else
    static if (is(T == uint))
        enum MaxWordPow10 = 9;
    else
    static if (is(T == ulong))
        enum MaxWordPow10 = 19;
    else
        static assert(0);
}

package template MaxWordPow5(T)
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

package template MaxFpPow5(T)
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

/++
Fast integer computation of `ceil(log10(exp2(e)))` with 64-bit mantissa precision.
The result is guaranted to be greater then `log10(exp2(e))`, which is irrational number.
+/
T ceilLog10Exp2(T)(const T e)
    @safe pure nothrow @nogc
    if (is(T == ubyte) || is(T == ushort) || is(T == uint) || is(T == ulong))
{
    import mir.utility: extMul;
    auto result = extMul(0x9a209a84fbcff799UL, e);
    return  cast(T) ((result.high >> 1) + ((result.low != 0) | (result.high & 1)));
}

///
version(mir_bignum_test)
@safe pure nothrow @nogc unittest
{
    assert(ceilLog10Exp2(ubyte(10)) == 4); // ubyte
    assert(ceilLog10Exp2(10U) == 4); // uint
    assert(ceilLog10Exp2(10UL) == 4); // ulong
}

/++
Performs `q = u / v, u = u % v` (unsigned)
Params:
    _u = The dividend (which will contain the remainder after the algorithm has run)
    _v = The divisor
    _q = The quotient
Preconditions:
    * non-empty coefficients
    * little-endian order
    * _u.coefficients.length >= _u.normalized.coefficients.length + 1
    * _v.coefficients.length >= _v.normalized.coefficients.length
    * _q.coefficients.length >= (_u.normalized.coefficients.length - _v.normalized.coefficients.length) + 1
+/
void divm(scope ref BigUIntView!uint _u, scope BigUIntView!uint _v, scope ref BigUIntView!uint _q)
    @trusted pure nothrow @nogc
{
    // Adopted from Hacker's Delight (2nd Edition), 4-2
    // License permits inclusion:
    // You are free to use, copy, and distribute any of the code on this web site, whether modified by you or not.
    // You need not give attribution. This includes the algorithms (some of which appear in Hacker's Delight), the Hacker's Assistant, and any code submitted by readers. Submitters implicitly agree to this.
    // The textural material and pictures are copyright by the author, and the usual copyright rules apply. E.g., you may store the material on your computer and make hard or soft copies for your own use.
    // However, you may not incorporate this material into another publication without written permission from the author (which the author may give by email).
    // The author has taken care in the preparation of this material, but makes no expressed or implied warranty of any kind and assumes no responsibility for errors or omissions.
    // No liability is assumed for incidental or consequential damages in connection with or arising out of the use of the information or programs contained herein. 
    import mir.bitop: ctlz;
    import mir.utility: _expect;

    enum shift = (uint.sizeof * 8);

    // Convert all of our input arguments to little-endian
    auto u = _u.leastSignificantFirst();
    auto v = _v.leastSignificantFirst();
    auto q = _q.leastSignificantFirst();
    size_t m = _u.normalized.coefficients.length, n = _v.normalized.coefficients.length;

    assert(m != 0 && n != 0);
    assert(_u.coefficients.length >= m + 1, "Dividend array is too small (should be m+1)");
    assert(_v.coefficients.length >= n, "Divisor array is too small");
    assert(v[n - 1] != 0);

    // Handle a common edge case with division (where the dividend is smaller then the divisor)
    // We don't care about how big the quotient array is here (and in fact, our math will fail)
    // since we just dump the dividend into the remainder 
    if (_expect(m < n, false))
    {
        _u.coefficients = _u.normalized.coefficients;
        return;
    }

    // From this point on, now we care if the quotient array is appropriately sized
    assert(_q.coefficients.length >= (m - n) + 1, "Quotient array is too small");

    // According to Knuth, when the divisor length is equal to one,
    // we should fall back to a simplified algorithm
    if (_expect(n == 1, false))
    {
        uint k = 0;
        foreach_reverse(j; 0 .. m)
        {
            // Same optimization as down below (left-shifting / ORing in place of multiplication / addition)
            auto ut = ((cast(ulong)(k) << shift) | u[j]); 
            q[j] = cast(uint)(ut / v[0]);
            k = cast(uint)(ut % v[0]);
            u[j] = 0;
        }
        _u.leastSignificant = k;
    }
    else
    {
        // pre-condition for this algorithm to succeed.
        // assert(m >= n, "failed algorithm pre-condition");

        // D1: Normalize
        // In TAOCP, this is specified as b/(v[n - 1] + 1)
        auto s = cast(uint)ctlz(v[n - 1]);
        assert(s <= 31 && s >= 0);

        // This normally uses a for loop, but we just use
        // a LLV primitive here instead.
        _v.smallLeftShiftInPlace(s);
        _u.smallLeftShiftInPlace(s);

        foreach_reverse(j; 0 .. (m - n) + 1)
        {
            // D3: Calculate qhat, rhat == remainder
            // In TOACP, this is specified as u[j+n]*b + u[j+n-1] / v[n - 1]
            // but, since we assume b is a power of 2, we can rewrite it to just
            // use left-shifting (as left-shifting effectively multiples by powers of 2)
            // and use an OR in place of the addition (as we've cleared the bottom 32 bits)
            auto ut = ((cast(ulong)(u[j+n]) << shift) | u[j + n - 1]); 
            ulong qhat = ut / v[n - 1];
            ulong rhat = ut % v[n - 1];

            // Similarly here, this is specified as qhat*v[n-2] > rhat*b + u[j+n-2]
            // but we can just get away with a shift instead.
            while (qhat >= uint.max || qhat*v[n-2] > (rhat << shift) + u[j+n-2])
            {
                qhat -= 1;
                rhat += v[n - 1];

                if (rhat > uint.max)
                {
                    break;
                }
            }

            long t = 0, k = 0;
            // D4: Multiply and subtract
            foreach(i; 0 .. n)
            {
                ulong p = qhat * v[i];
                // t = u[i + j] - k - (p & cast(uint)((ulong(1) << shift) - 1));
                t = u[i + j] - k - (cast(uint)p);
                u[i + j] = cast(uint)t;
                k = (p >> shift) - (t >> shift);
            }
            
            t = u[j + n] - k;
            // These are admittedly super sketchy casts, but
            // we really are only interested in the bottom 32-bits here.
            u[j + n] = cast(uint)t;
            q[j] = cast(uint)(qhat);
            // D5: Test remainder
            if (_expect(t < 0, false))
            {
                q[j] -= 1;
                k = 0;
                foreach(i; 0 .. n)
                {
                    t = cast(ulong)(u[i + j]) + v[i] + k;
                    u[i + j] = cast(uint)t;
                    k = t >> shift;
                }
                u[j + n] = cast(uint)(u[j + n] + k);
            }
        }

        // D8: Un-normalize (obtain the remainder)
        _u.smallRightShiftInPlace(s);
        _v.smallRightShiftInPlace(s);
    }

    // Finally, normalize these when they're "headed out the door"
    _u.coefficients = _u.normalized.coefficients;
    _q.coefficients = _q.normalized.coefficients;
}

///
version(mir_bignum_test)
unittest
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.low_level_view: BigUIntView;

    {
        // Test division by a single-digit divisor here.
        auto dividend = BigUIntView!uint.fromHexString("000000005");
        auto divisor = BigUIntView!uint.fromHexString("5");
        auto quotient = BigUIntView!uint.fromHexString("0");
        // auto remainder = BigUIntView!uint.fromHexString("0");

        divm(dividend, divisor, quotient);
        assert(quotient == BigUIntView!uint.fromHexString("1"));
        assert(dividend.coefficients.length == 0);
    }

    {
        // Test division by a single-digit divisor here.
        auto dividend = BigUIntView!uint.fromHexString("055a325ad18b2a77120d870d987d5237473790532acab45da44bc07c92c92babf");
        auto divisor = BigUIntView!uint.fromHexString("5");
        auto quotient = BigUIntView!uint.fromHexString("0000000000000000000000000000000000000000000000000000000000000000");
        divm(dividend, divisor, quotient);
        assert(dividend.normalized == BigUIntView!uint.fromHexString("3"));
        assert(quotient == BigUIntView!uint.fromHexString("1120a1229e8a217d0691b02b819107174a4b677088ef0df874259b283c1d588c"));
    }

    // Test big number division
    {
        auto dividend = BigUIntView!uint.fromHexString("055a325ad18b2a77120d870d987d5237473790532acab45da44bc07c92c92babf0b5e2e2c7771cd472ae5d7acdb159a56fbf74f851a058ae341f69d1eb750d7e3");
        auto divisor = BigUIntView!uint.fromHexString("55e5669576d31726f4a9b58a90159de5923adc6c762ebd3c4ba518d495229072");
        auto quotient = BigUIntView!uint.fromHexString("00000000000000000000000000000000000000000000000000000000000000000");
        // auto remainder = BigUIntView!uint.fromHexString("00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");

        divm(dividend, divisor, quotient);
        assert(quotient.normalized == BigUIntView!uint.fromHexString("ff3a8aa4da35237811a0ffbf007fe938630dee8a810f2f82ae01f80c033291f6"));
        assert(dividend.normalized == BigUIntView!uint.fromHexString("27926263cf248bef1c2cd63ea004d9f7041bffc8568560ec30fc9a9548057857"));
    }

    // Trigger the adding back sequence
    {
        auto dividend = BigUIntView!uint.fromHexString("0800000000000000000000003");
        auto divisor = BigUIntView!uint.fromHexString("200000000000000000000001");
        auto quotient = BigUIntView!uint.fromHexString("0");
        // auto remainder = BigUIntView!uint.fromHexString("000000000000000000000000");
        divm(dividend, divisor, quotient);
        assert(quotient == BigUIntView!uint.fromHexString("3"));
        assert(dividend == BigUIntView!uint.fromHexString("200000000000000000000000"));
    }
    
}

/++
Arbitrary length unsigned integer view.
+/
struct BigUIntView(W, WordEndian endian = TargetEndian)
    if (__traits(isUnsigned, W))
{
    import mir.bignum.fp: Fp, half;
    import mir.bignum.fixed: UInt;

    /++
    A group of coefficients for a radix `W.max + 1`.

    The order corresponds to endianness.
    +/
    W[] coefficients;

    /++
    Retrurns: signed integer view using the same data payload
    +/
    BigIntView!(W, endian) signed()() @safe pure nothrow @nogc scope @property
    {
        return typeof(return)(this);
    }

    ///
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() scope const
        if (isFloatingPoint!T && isMutable!T)
    {
        import mir.bignum.fp;
        enum md = T.mant_dig;
        enum b = size_t.sizeof * 8;
        enum n = md / b + (md % b != 0);
        enum s = n * b;
        return this.opCast!(Fp!s, s - md, wordNormalized, nonZero).opCast!(T, true);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    unittest
    {
        auto a = cast(double) BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a == 0xa.fbbfae3cd0bp+124);
        assert(cast(double) BigUIntView!size_t.init == 0);
        assert(cast(double) BigUIntView!size_t([0]) == 0);
    }

    ///
    @safe
    T opCast(T : Fp!coefficientSize, size_t internalRoundLastBits = 0, bool wordNormalized = false, bool nonZero = false, size_t coefficientSize)() scope const
        if (internalRoundLastBits < size_t.sizeof * 8 && (size_t.sizeof >= W.sizeof || endian == TargetEndian))
    {
        static if (isMutable!W)
        {
            return lightConst.opCast!(T, internalRoundLastBits, wordNormalized, nonZero);
        }
        else
        static if (W.sizeof > size_t.sizeof)
        {
            return lightConst.opCast!(BigUIntView!size_t).opCast!(T, internalRoundLastBits, false, nonZero);
        }
        else
        {
            import mir.utility: _expect;
            import mir.bitop: ctlz;
            Fp!coefficientSize ret;
            auto integer = lightConst;
            static if (!wordNormalized)
                integer = integer.normalized;
            static if (!nonZero)
                if (integer.coefficients.length == 0)
                    goto R;
            {
                assert(integer.coefficients.length);
                enum N = ret.coefficient.data.length;
                sizediff_t size = integer.coefficients.length * (W.sizeof * 8);
                sizediff_t expShift = size - coefficientSize;
                ret.exponent = expShift;
                if (_expect(expShift <= 0, true))
                {
                    static if (N == 1 && W.sizeof == size_t.sizeof)
                    {
                        ret.coefficient.data[0] = integer.mostSignificant;
                    }
                    else
                    {
                        BigUIntView!size_t(ret.coefficient.data)
                            .opCast!(BigUIntView!(Unqual!W))
                            .leastSignificantFirst
                                [$ - integer.coefficients.length .. $] = integer.leastSignificantFirst;
                    }
                    auto c = cast(uint) ctlz(ret.coefficient.view.mostSignificant);
                    ret.exponent -= c;
                    ret.coefficient = ret.coefficient.smallLeftShift(c);
                }
                else
                {
                    UInt!(coefficientSize + size_t.sizeof * 8) holder;


                    static if (N == 1 && W.sizeof == size_t.sizeof)
                    {
                        version (BigEndian)
                        {
                            holder.data[0] = integer.mostSignificantFirst[0];
                            holder.data[1] = integer.mostSignificantFirst[1];
                        }
                        else
                        {
                            holder.data[0] = integer.mostSignificantFirst[1];
                            holder.data[1] = integer.mostSignificantFirst[0];
                        }
                    }
                    else
                    {
                        auto holderView = holder
                            .view
                            .opCast!(BigUIntView!(Unqual!W))
                            .leastSignificantFirst;
                        import mir.utility: min;
                        auto minLength = min(integer.coefficients.length, holderView.length);
                        holderView[$ - minLength .. $] = integer.leastSignificantFirst[$ - minLength .. $];
                    }

                    auto c = cast(uint) ctlz(holder.view.mostSignificant);
                    ret.exponent -= c;
                    holder = holder.smallLeftShift(c);
                    ret.coefficient = holder.toSize!(coefficientSize, false);
                    auto tail = BigUIntView!size_t(holder.data).leastSignificant;

                    bool nonZeroTail()
                    {
                        while(_expect(integer.leastSignificant == 0, false))
                        {
                            integer.popLeastSignificant;
                            assert(integer.coefficients.length);
                        }
                        return integer.coefficients.length > (N + 1) * (size_t.sizeof / W.sizeof);
                    }

                    static if (internalRoundLastBits)
                    {
                        enum half = size_t(1) << (internalRoundLastBits - 1);
                        enum mask0 = (size_t(1) << internalRoundLastBits) - 1;
                        auto tail0 = BigUIntView!size_t(ret.coefficient.data).leastSignificant & mask0;
                        BigUIntView!size_t(ret.coefficient.data).leastSignificant &= ~mask0;
                        auto condInc = tail0 >= half
                            && (   tail0 > half
                                || tail
                                || (BigUIntView!size_t(ret.coefficient.data).leastSignificant & 1)
                                || nonZeroTail);
                    }
                    else
                    {
                        enum half = cast(size_t)Signed!size_t.min;
                        auto condInc = tail >= half
                            && (    tail > half
                                || (BigUIntView!size_t(ret.coefficient.data).leastSignificant & 1)
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
            }
        R:
            return ret;
        }
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        import mir.bignum.fp: Fp;
        import mir.bignum.fixed: UInt;

        auto fp = cast(Fp!128) BigUIntView!ulong.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(fp.exponent == 0);
        assert(fp.coefficient == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));

        fp = cast(Fp!128) BigUIntView!uint.fromHexString("ae3cd0aff2714a1de7022b0029d");
        assert(fp.exponent == -20);
        assert(fp.coefficient == UInt!128.fromHexString("ae3cd0aff2714a1de7022b0029d00000"));

        fp = cast(Fp!128) BigUIntView!ushort.fromHexString("e7022b0029d");
        assert(fp.exponent == -84);
        assert(fp.coefficient == UInt!128.fromHexString("e7022b0029d000000000000000000000"));

        fp = cast(Fp!128) BigUIntView!ubyte.fromHexString("e7022b0029d");
        assert(fp.exponent == -84);
        assert(fp.coefficient == UInt!128.fromHexString("e7022b0029d000000000000000000000"));

        fp = cast(Fp!128) BigUIntView!size_t.fromHexString("e7022b0029d");
        assert(fp.exponent == -84);
        assert(fp.coefficient == UInt!128.fromHexString("e7022b0029d000000000000000000000"));
    
        fp = cast(Fp!128) BigUIntView!size_t.fromHexString("ffffffffffffffffffffffffffffffff1000000000000000");
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!128.fromHexString("ffffffffffffffffffffffffffffffff"));

        fp = cast(Fp!128) BigUIntView!size_t.fromHexString("ffffffffffffffffffffffffffffffff8000000000000000");
        assert(fp.exponent == 65);
        assert(fp.coefficient == UInt!128.fromHexString("80000000000000000000000000000000"));

        fp = cast(Fp!128) BigUIntView!size_t.fromHexString("fffffffffffffffffffffffffffffffe8000000000000000");
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!128.fromHexString("fffffffffffffffffffffffffffffffe"));

        fp = cast(Fp!128) BigUIntView!size_t.fromHexString("fffffffffffffffffffffffffffffffe8000000000000001");
        assert(fp.exponent == 64);
        assert(fp.coefficient == UInt!128.fromHexString("ffffffffffffffffffffffffffffffff"));
    }


    ///
    T opCast(T, bool nonZero = false)() const scope
        if (isIntegral!T && isUnsigned!T && isMutable!T)
    {
        auto work = lightConst;
        static if (!nonZero)
        {
            if (coefficients.length == 0)
            {
                return 0;
            }
        }
        static if (T.sizeof <= W.sizeof)
        {
            return cast(T) work.leastSignificant;
        }
        else
        {
            T ret;
            do
            {
                ret <<= W.sizeof * 8;
                ret |= work.mostSignificant;
                work.popMostSignificant;
            }
            while(work.coefficients.length);
            return ret;
        }
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigUIntView!ulong.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(cast(ulong) view == 0x14a1de7022b0029d);
        assert(cast(uint) view == 0x22b0029d);
        assert(cast(ubyte) view == 0x9d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigUIntView!ushort.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(cast(ulong) view == 0x14a1de7022b0029d);
        assert(cast(uint) view == 0x22b0029d);
        assert(cast(ubyte) view == 0x9d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigUIntView!uint.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(cast(ulong) view == 0x14a1de7022b0029d);
        assert(cast(uint) view == 0x22b0029d);
        assert(cast(ubyte) view == 0x9d);
    }

    static if (endian == TargetEndian)
    ///
    @trusted pure nothrow @nogc
    BigUIntView!V opCast(T : BigUIntView!V, V)() return scope
        if (V.sizeof <= W.sizeof)
    {
        return typeof(return)(cast(V[])this.coefficients);
    }

    ///
    BigUIntView!(const W, endian) lightConst()()
        const @safe pure nothrow @nogc @property return scope
    {
        return typeof(return)(coefficients);
    }
    ///ditto
    alias lightConst this;

    /++
    +/
    sizediff_t opCmp(scope BigUIntView!(const W, endian) rhs)
        const @safe pure nothrow @nogc scope
    {
        import mir.algorithm.iteration: cmp;
        auto l = this.lightConst.normalized;
        auto r = rhs.lightConst.normalized;
        if (sizediff_t d = l.coefficients.length - r.coefficients.length)
            return d;
        return cmp(l.mostSignificantFirst, r.mostSignificantFirst);
    }

    ///
    bool opEquals(scope BigUIntView!(const W, endian) rhs)
        const @safe pure nothrow @nogc scope
    {
        return this.coefficients == rhs.coefficients;
    }

    /++
    +/
    ref inout(W) mostSignificant() inout @property return scope
    {
        static if (endian == WordEndian.big)
            return coefficients[0];
        else
            return coefficients[$ - 1];
    }

    /++
    +/
    ref inout(W) leastSignificant() inout @property return scope
    {
        static if (endian == WordEndian.little)
            return coefficients[0];
        else
            return coefficients[$ - 1];
    }

    /++
    +/
    void popMostSignificant() scope
    {
        static if (endian == WordEndian.big)
            coefficients = coefficients[1 .. $];
        else
            coefficients = coefficients[0 .. $ - 1];
    }

    /++
    +/
    void popLeastSignificant() scope
    {
        static if (endian == WordEndian.little)
            coefficients = coefficients[1 .. $];
        else
            coefficients = coefficients[0 .. $ - 1];
    }

    /++
    +/
    BigUIntView topMostSignificantPart(size_t length) return scope
    {
        static if (endian == WordEndian.big)
            return BigUIntView(coefficients[0 .. length]);
        else
            return BigUIntView(coefficients[$ - length .. $]);
    }

    /++
    +/
    BigUIntView topLeastSignificantPart(size_t length) return scope
    {
        static if (endian == WordEndian.little)
            return BigUIntView(coefficients[0 .. length]);
        else
            return BigUIntView(coefficients[$ - length .. $]);
    }

    /++
    Shifts left using at most `size_t.sizeof * 8 - 1` bits
    +/
    void smallLeftShiftInPlace()(uint shift) scope
    {
        assert(shift < W.sizeof * 8);
        if (shift == 0)
            return;
        auto csh = W.sizeof * 8 - shift;
        auto d = leastSignificantFirst;
        assert(d.length);
        foreach_reverse (i; 1 .. d.length)
            d[i] = (d[i] << shift) | (d[i - 1] >>> csh);
        d.front <<= shift;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto a = BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        a.smallLeftShiftInPlace(4);
        assert(a == BigUIntView!size_t.fromHexString("fbbfae3cd0aff2714a1de7022b0029d0"));
        a.smallLeftShiftInPlace(0);
        assert(a == BigUIntView!size_t.fromHexString("fbbfae3cd0aff2714a1de7022b0029d0"));
    }

    /++
    Shifts right using at most `size_t.sizeof * 8 - 1` bits
    +/
    void smallRightShiftInPlace()(uint shift)
    {
        assert(shift < W.sizeof * 8);
        if (shift == 0)
            return;
        auto csh = W.sizeof * 8 - shift;
        auto d = leastSignificantFirst;
        assert(d.length);
        foreach (i; 0 .. d.length - 1)
            d[i] = (d[i] >>> shift) | (d[i + 1] << csh);
        d.back >>>= shift;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto a = BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        a.smallRightShiftInPlace(4);
        assert(a == BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029"));
    }

    /++
    +/
    static BigUIntView fromHexString(C, bool allowUnderscores = false)(scope const(C)[] str)
        @trusted pure
        if (isSomeChar!C)
    {
        auto length = str.length / (W.sizeof * 2) + (str.length % (W.sizeof * 2) != 0);
        auto data = new Unqual!W[length];
        auto view = BigUIntView!(Unqual!W, endian)(data);
        if (view.fromHexStringImpl!(C, allowUnderscores)(str))
            return BigUIntView(cast(W[])view.coefficients);
        version(D_Exceptions)
            throw hexStringException;
        else
            assert(0, hexStringErrorMsg);
    }

    static if (isMutable!W)
    /++
    +/
    bool fromHexStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow scope
        if (isSomeChar!C)
    {
        pragma(inline, false);
        import mir.utility: _expect;
        static if (allowUnderscores) {
            if (_expect(str.length == 0, false)) // can't tell how big the coeff array needs to be, rely on a runtime check
                return false;
        } else {
            if (_expect(str.length == 0 || str.length > coefficients.length * W.sizeof * 2, false))
                return false;
        }

        leastSignificant = 0;
        auto work = topLeastSignificantPart(1);
        W current;
        size_t i, j;
        static if (allowUnderscores) bool recentUnderscore;

        do
        {
            ubyte c;
            switch(str[$ - ++i])
            {
                case '0': c = 0x0; break;
                case '1': c = 0x1; break;
                case '2': c = 0x2; break;
                case '3': c = 0x3; break;
                case '4': c = 0x4; break;
                case '5': c = 0x5; break;
                case '6': c = 0x6; break;
                case '7': c = 0x7; break;
                case '8': c = 0x8; break;
                case '9': c = 0x9; break;
                case 'A':
                case 'a': c = 0xA; break;
                case 'B':
                case 'b': c = 0xB; break;
                case 'C':
                case 'c': c = 0xC; break;
                case 'D':
                case 'd': c = 0xD; break;
                case 'E':
                case 'e': c = 0xE; break;
                case 'F':
                case 'f': c = 0xF; break;
                static if (allowUnderscores) 
                {
                    case '_': 
                        if (recentUnderscore) return false;
                        recentUnderscore = true;
                        continue;
                }
                default: return false;
            }
            ++j;
            static if (allowUnderscores) recentUnderscore = false;
            // how far do we need to shift to get to the top 4 bits
            enum s = W.sizeof * 8 - 4;
            // shift number to the top most 4 bits
            W cc = cast(W)(W(c) << s);
            // shift unsigned right 4 bits
            current >>>= 4;
            // add number to top most 4 bits of current var
            current |= cc;
            if (j % (W.sizeof * 2) == 0) // is this packed var full? 
            {
                work.mostSignificant = current;
                current = 0;
                if (_expect(work.coefficients.length < coefficients.length, true))
                {
                    work = topLeastSignificantPart(work.coefficients.length + 1);
                }
                else if (i < str.length) // if we've run out of coefficients before reaching the end of the string, error
                {
                    return false;
                }
            }
        }
        while(i < str.length);

        static if (allowUnderscores) 
        {
            // check for a underscore at the beginning or the end
            if (recentUnderscore || str[$ - 1] == '_') return false;
        }

        if (current)
        {
            current >>>= 4 * (W.sizeof * 2 - j % (W.sizeof * 2));
            work.mostSignificant = current;
        }

        coefficients = coefficients[0 .. (j / (W.sizeof * 2) + (j % (W.sizeof * 2) != 0))];

        return true;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigUIntView!size_t.fromHexString!(char, true)("abcd_efab_cdef");
        assert(cast(ulong)view == 0xabcd_efab_cdef);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        // Check that invalid underscores in hex literals throw an error.
        void expectThrow(const(char)[] input) {
            bool caught = false;
            try { 
                auto view = BigUIntView!size_t.fromHexString!(char, true)(input);
            } catch (Exception e) {
                caught = true;
            }

            assert(caught);
        }

        expectThrow("abcd_efab_cef_");
        expectThrow("abcd__efab__cef");
        expectThrow("_abcd_efab_cdef");
        expectThrow("_abcd_efab_cdef_");
        expectThrow("_abcd_efab_cdef__");
        expectThrow("__abcd_efab_cdef");
        expectThrow("__abcd_efab_cdef_");
        expectThrow("__abcd_efab_cdef__");
        expectThrow("__abcd__efab_cdef__");
        expectThrow("__abcd__efab__cdef__");
    }
 
    /++
    +/
    static BigUIntView fromBinaryString(C, bool allowUnderscores = false)(scope const(C)[] str)
        @trusted pure
        if (isSomeChar!C)
    {
        auto length = str.length / (W.sizeof * 8) + (str.length % (W.sizeof * 8) != 0);
        auto data = new Unqual!W[length];
        auto view = BigUIntView!(Unqual!W, endian)(data);
        if (view.fromBinaryStringImpl!(C, allowUnderscores)(str))
            return BigUIntView(cast(W[])view.coefficients);
        version(D_Exceptions)
            throw binaryStringException;
        else
            assert(0, binaryStringErrorMsg);
    }

    static if (isMutable!W)
    /++
    +/
    bool fromBinaryStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow scope
        if (isSomeChar!C)
    {
        pragma(inline, false);
        import mir.utility: _expect;
        static if (allowUnderscores) {
            if (_expect(str.length == 0, false)) // can't tell how big the coeff array needs to be, rely on a runtime check
                return false;
        } else {
            if (_expect(str.length == 0 || str.length > coefficients.length * W.sizeof * 8, false))
                return false;
        }

        leastSignificant = 0;
        auto work = topLeastSignificantPart(1);
        W current;
        size_t i, j;
        static if (allowUnderscores) bool recentUnderscore;

        do
        {
            ubyte c;
            switch(str[$ - ++i])
            {
                case '0': c = 0x0; break;
                case '1': c = 0x1; break;
                static if (allowUnderscores) 
                {
                    case '_': 
                        if (recentUnderscore) return false;
                        recentUnderscore = true;
                        continue;
                }
                default: return false;
            }
            ++j;
            static if (allowUnderscores) recentUnderscore = false;
            // how far do we need to shift to get to the top bit?
            enum s = W.sizeof * 8 - 1;
            // shift number to the top most bit
            W cc = cast(W)(W(c) << s);
            // shift unsigned right 1 bit
            current >>>= 1;
            // add number to top most bit of current var
            current |= cc;
            if (j % (W.sizeof * 8) == 0) // is this packed var full? 
            {
                work.mostSignificant = current;
                current = 0;
                if (_expect(work.coefficients.length < coefficients.length, true))
                {
                    work = topLeastSignificantPart(work.coefficients.length + 1);
                }
                else if (i < str.length) // if we've run out of coefficients before reaching the end of the string, error
                {
                    return false;
                }
            }
        }
        while(i < str.length);

        static if (allowUnderscores) 
        {
            // check for a underscore at the beginning or the end
            if (recentUnderscore || str[$ - 1] == '_') return false;
        }

        if (current)
        {
            current >>>= (W.sizeof * 8 - j % (W.sizeof * 8));
            work.mostSignificant = current;
        }

        coefficients = coefficients[0 .. (j / (W.sizeof * 8) + (j % (W.sizeof * 8) != 0))];

        return true;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigUIntView!size_t.fromBinaryString!(char, true)("1111_0000_0101");
        assert(cast(ulong)view == 0b1111_0000_0101);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        // Check that invalid underscores in hex literals throw an error.
        void expectThrow(const(char)[] input) {
            bool caught = false;
            try { 
                auto view = BigUIntView!size_t.fromBinaryString!(char, true)(input);
            } catch (Exception e) {
                caught = true;
            }

            assert(caught);
        }

        expectThrow("abcd");
        expectThrow("0101__1011__0111");
        expectThrow("_0101_1011_0111");
        expectThrow("_0101_1011_0111_");
        expectThrow("_0101_1011_0111__");
        expectThrow("__0101_1011_0111_");
        expectThrow("__0101_1011_0111__");
        expectThrow("__0101__1011_0111__");
        expectThrow("__1011__0111__1011__");
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients
    Note: doesn't support signs.
    +/
    bool fromStringImpl(C)(scope const(C)[] str)
        scope @trusted pure @nogc nothrow
        if (isSomeChar!C)
    {
        import mir.utility: _expect;

        assert(coefficients.length);

        if (_expect(str.length == 0, false))
            return false;

        leastSignificant = 0;
        uint d = str[0] - '0';
        str = str[1 .. $];

        W v;
        W t = 1;

        if (d == 0)
        {
            if (str.length == 0)
            {
                coefficients = null;
                return true;
            }
            return false;
        }
        else
        if (d >= 10)
            return false;

        auto work = topLeastSignificantPart(1);
        goto S;

        for(;;)
        {
            enum mp10 = W(10) ^^ MaxWordPow10!W;
            d = str[0] - '0';
            str = str[1 .. $];
            if (_expect(d > 10, false))
                break;
            v *= 10;
    S:
            t *= 10;
            v += d;

            if (_expect(t == mp10 || str.length == 0, false))
            {
            L:
                if (auto overflow = work.opOpAssign!"*"(t, v))
                {
                    if (_expect(work.coefficients.length < coefficients.length, true))
                    {
                        work = topLeastSignificantPart(work.coefficients.length + 1);
                        work.mostSignificant = overflow;
                    }
                    else
                    {
                        return false;
                    }
                }
                v = 0;
                t = 1;
                if (str.length == 0)
                {
                    this = work;
                    return true;
                }
            }
        }
        return false;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `bool overflow = big +(-)= big` operatrion.
    Params:
        rhs = value to add with non-empty coefficients
        overflow = (overflow) initial iteration overflow
    Precondition: non-empty coefficients length of greater or equal to the `rhs` coefficients length.
    Returns:
        true in case of unsigned overflow
    +/
    bool opOpAssign(string op)(scope BigUIntView!(const W, endian) rhs, bool overflow = false)
    @safe pure nothrow @nogc scope
        if (op == "+" || op == "-")
    {
        assert(this.coefficients.length > 0);
        assert(rhs.coefficients.length <= this.coefficients.length);
        auto ls = this.leastSignificantFirst;
        auto rs = rhs.leastSignificantFirst;
        do
        {
            bool overflowM, overflowG;
            ls.front = ls.front.cop!op(rs.front, overflowM).cop!op(overflow, overflowG);
            overflow = overflowG | overflowM;
            ls.popFront;
            rs.popFront;
        }
        while(rs.length);
        if (overflow && ls.length)
            return topMostSignificantPart(ls.length).opOpAssign!op(W(overflow));
        return overflow;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /// ditto
    bool opOpAssign(string op)(scope BigIntView!(const W, endian) rhs, bool overflow = false)
    @safe pure nothrow @nogc scope
        if (op == "+" || op == "-")
    {
        return rhs.sign == false ?
            opOpAssign!op(rhs.unsigned, overflow):
            opOpAssign!(inverseSign!op)(rhs.unsigned, overflow);
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `bool Overflow = big +(-)= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = value to add
    Returns:
        true in case of unsigned overflow
    +/
    bool opOpAssign(string op, T)(const T rhs)
        @safe pure nothrow @nogc scope
        if ((op == "+" || op == "-") && is(T == W))
    {
        assert(this.coefficients.length > 0);
        auto ns = this.leastSignificantFirst;
        W additive = rhs;
        do
        {
            bool overflow;
            ns.front = ns.front.cop!op(additive, overflow);
            if (!overflow)
                return overflow;
            additive = overflow;
            ns.popFront;
        }
        while (ns.length);
        return true;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /// ditto
    bool opOpAssign(string op, T)(const T rhs)
        @safe pure nothrow @nogc scope
        if ((op == "+" || op == "-") && is(T == Signed!W))
    {
        return rhs >= 0 ?
            opOpAssign!op(cast(W)rhs):
            opOpAssign!(inverseSign!op)(cast(W)(-rhs));
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `W overflow = (big += overflow) *= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned value to multiply by
        overflow = initial overflow
    Returns:
        unsigned overflow value
    +/
    W opOpAssign(string op : "*")(W rhs, W overflow = 0u)
        @safe pure nothrow @nogc scope
    {
        assert(coefficients.length);
        auto ns = this.leastSignificantFirst;
        do
        {
            import mir.utility: extMul;
            auto ext = ns.front.extMul(rhs);
            bool overflowM;
            ns.front = ext.low.cop!"+"(overflow, overflowM);
            overflow = ext.high + overflowM;
            ns.popFront;
        }
        while (ns.length);
        return overflow;
    }

    static if (isMutable!W && W.sizeof == 4 || W.sizeof == 8 && endian == TargetEndian)
    /++
    Performs `uint remainder = (overflow$big) /= scalar` operatrion, where `$` denotes big-endian concatenation.
    Precondition: non-empty coefficients, `overflow < rhs`
    Params:
        rhs = unsigned value to devide by
        overflow = initial unsigned overflow
    Returns:
        unsigned remainder value (evaluated overflow)
    +/
    uint opOpAssign(string op : "/")(uint rhs, uint overflow = 0)
        @safe pure nothrow @nogc scope
    {
        assert(overflow < rhs);
        assert(coefficients.length);
        static if (W.sizeof == 4)
        {
            auto ns = this.mostSignificantFirst;
            size_t i;
            do
            {
                auto ext = (ulong(overflow) << 32) ^ ns[i];
                ns[i] = cast(uint)(ext / rhs);
                overflow = ext % rhs;
            }
            while (++i < ns.length);
            if (mostSignificant == 0)
                popMostSignificant;
            return overflow;
        }
        else
        {
            auto work = opCast!(BigUIntView!uint);
            if (work.mostSignificant == 0)
                work.popMostSignificant;
            auto remainder = work.opOpAssign!op(rhs, overflow);
            coefficients = coefficients[0 .. work.coefficients.length / 2 + work.coefficients.length % 2];
            return remainder;
        }
    }

    static if (isMutable!W && W.sizeof == size_t.sizeof)
    /++
    Performs `W overflow = (big += overflow) *= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned fixed-length integer to multiply by
        overflow = initial overflow
    Returns:
        unsigned fixed-length integer overflow value
    +/
    UInt!size
    opOpAssign(string op : "*", size_t size)(UInt!size rhs, UInt!size overflow = 0)
        @safe pure nothrow @nogc scope
    {
        assert(coefficients.length);
        auto ns = this.leastSignificantFirst;
        do
        {
            auto t = rhs;
            auto overflowW = t.view *= ns.front;
            auto overflowM = t += overflow;
            overflowW += overflowM;
            ns.front = cast(size_t) t;
            static if (size > size_t.sizeof * 8)
                overflow = t.toSize!(size - size_t.sizeof * 8, false).toSize!size;
            BigUIntView!size_t(overflow.data).mostSignificant = overflowW;
            ns.popFront;
        }
        while (ns.length);
        return overflow;
    }

    /++
    Returns: the same intger view with inversed sign
    +/
    BigIntView!(W, endian) opUnary(string op : "-")() return scope
    {
        return typeof(return)(this, true);
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    +/
    void bitwiseNotInPlace() scope
    {
        foreach (ref coefficient; this.coefficients)
            coefficient = cast(W)~(0 + coefficient);
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `number=-number` operatrion.
    Precondition: non-empty coefficients
    Returns:
        true if 'number=-number=0' and false otherwise
    +/
    bool twoComplementInPlace() scope
    {
        assert(coefficients.length);
        bitwiseNotInPlace();
        return this.opOpAssign!"+"(W(1));
    }

    /++
    Returns: a slice of coefficients starting from the least significant.
    +/
    auto leastSignificantFirst()
        @safe pure nothrow @nogc @property return scope
    {
        import mir.ndslice.slice: sliced;
        static if (endian == WordEndian.little)
        {
            return coefficients.sliced;
        }
        else
        {
            import mir.ndslice.topology: retro;
            return coefficients.sliced.retro;
        }
    }

    ///
    auto leastSignificantFirst()
        const @safe pure nothrow @nogc @property return scope
    {
        import mir.ndslice.slice: sliced;
        static if (endian == WordEndian.little)
        {
            return coefficients.sliced;
        }
        else
        {
            import mir.ndslice.topology: retro;
            return coefficients.sliced.retro;
        }
    }

    /++
    Returns: a slice of coefficients starting from the most significant.
    +/
    auto mostSignificantFirst()
        @safe pure nothrow @nogc @property return scope
    {
        import mir.ndslice.slice: sliced;
        static if (endian == WordEndian.big)
        {
            return coefficients.sliced;
        }
        else
        {
            import mir.ndslice.topology: retro;
            return coefficients.sliced.retro;
        }
    }

    ///
    auto mostSignificantFirst()
        const @safe pure nothrow @nogc @property return scope
    {
        import mir.ndslice.slice: sliced;
        static if (endian == WordEndian.big)
        {
            return coefficients.sliced;
        }
        else
        {
            import mir.ndslice.topology: retro;
            return coefficients.sliced.retro;
        }
    }

    /++
    Strips most significant zero coefficients.
    +/
    BigUIntView normalized() return scope
    {
        auto number = this;
        if (number.coefficients.length) do
        {
            static if (endian == WordEndian.big)
            {
                if (number.coefficients[0])
                    break;
                number.coefficients = number.coefficients[1 .. $];
            }
            else
            {
                if (number.coefficients[$ - 1])
                    break;
                number.coefficients = number.coefficients[0 .. $ - 1];
            }
        }
        while (number.coefficients.length);
        return number;
    }

    ///ditto
    BigUIntView!(const W, endian) normalized() scope const
    {
        return lightConst.normalized;
    }

    /++
    +/
    bool bt()(size_t position) scope
    {
        import mir.ndslice.topology: bitwise;
        assert(position < coefficients.length * W.sizeof * 8);
        return leastSignificantFirst.bitwise[position];
    }

    /++
    +/
    size_t ctlz()() scope const @property
        @safe pure nothrow @nogc
    {
        import mir.bitop: ctlz;
        assert(coefficients.length);
        auto d = mostSignificantFirst;
        size_t ret;
        do
        {
            if (auto c = d.front)
            {
                ret += ctlz(c);
                break;
            }
            ret += W.sizeof * 8;
            d.popFront;
        }
        while(d.length);
        return ret;
    }

    /++
    +/
    size_t cttz()() scope const @property
        @safe pure nothrow @nogc
    {
        import mir.bitop: cttz;
        assert(coefficients.length);
        auto d = leastSignificantFirst;
        size_t ret;
        do
        {
            if (auto c = d.front)
            {
                ret += cttz(c);
                break;
            }
            ret += W.sizeof * 8;
            d.popFront;
        }
        while(d.length);
        return ret;
    }

    ///
    BigIntView!(W, endian) withSign()(bool sign)
    {
        return typeof(return)(this, sign);
    }

    /++
    Params:
        value = (out) unsigned integer
    Returns: true on success
    +/
    bool get(U)(scope out U value)
        @safe pure nothrow @nogc scope const
        if (isUnsigned!U)
    {
        auto d = lightConst.mostSignificantFirst;
        if (d.length == 0)
            return false;
        static if (U.sizeof > W.sizeof)
        {
            size_t i;
            for(;;)
            {
                value |= d[0];
                d = d[1 .. $];
                if (d.length == 0)
                    return false;
                i += cast(bool)value;
                value <<= W.sizeof * 8;
                import mir.utility: _expect;
                if (_expect(i >= U.sizeof / W.sizeof, false))
                    return true;
            }
        }
        else
        {
            for(;;)
            {
                W f = d[0];
                d = d[1 .. $];
                if (d.length == 0)
                {
                    value = cast(U)f;
                    static if (U.sizeof < W.sizeof)
                    {
                        if (value != f)
                            return true;
                    }
                    return false;
                }
                if (f)
                    return true;
            }
        }
    }

    /++
    Returns: true if the integer and equals to `rhs`.
    +/
    bool opEquals(ulong rhs)
        @safe pure nothrow @nogc const scope
    {
        foreach (d; lightConst.leastSignificantFirst)
        {
            static if (W.sizeof >= ulong.sizeof)
            {
                if (d != rhs)
                    return false;
                rhs = 0;
            }
            else
            {
                if (d != (rhs & W.max))
                    return false;
                rhs >>>= W.sizeof * 8;
            }
        }
        return rhs == 0;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view2 = BigUIntView!(const(ubyte), WordEndian.big)([1, 0]);
        assert(view2 == 256); // false
        assert(cast(ulong)view2 == 256); // true
        auto view = BigUIntView!(const(ubyte), WordEndian.big)([15, 255, 255]);
        assert(view == 1048575); // false
        assert(cast(ulong)view == 1048575); // true
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Params:
        str = string buffer, the tail paer 
    Precondition: mutable number with word size at least 4 bytes
    Postconditoin: the number is destroyed
    Returns: last N bytes used in the buffer
    +/
    size_t toStringImpl(C)(scope C[] str)
        @safe pure nothrow @nogc
        if (isSomeChar!C && isMutable!C)
    {
        assert(str.length);
        assert(str.length >= ceilLog10Exp2(coefficients.length * (W.sizeof * 8)));

        size_t i = str.length;
        while(coefficients.length > 1)
        {
            uint rem = this /= 1_000_000_000;
            foreach (_; 0 .. 9)
            {
                str[--i] = cast(char)(rem % 10 + '0');
                rem /= 10;
            }
        }

        W rem = coefficients.length == 1 ? coefficients[0] : W(0);
        do
        {
            str[--i] = cast(char)(rem % 10 + '0');
            rem /= 10;
        }
        while(rem);

        return str.length - i;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        import mir.bignum.integer;

        auto a = BigInt!2("123456789098765432123456789098765432100");
        char[ceilLog10Exp2(a.data.length * (size_t.sizeof * 8))] buffer;
        auto len = a.view.unsigned.toStringImpl(buffer);
        assert(buffer[$ - len .. $] == "123456789098765432123456789098765432100");
    }
}

///
version(mir_bignum_test)
@safe pure nothrow
unittest
{
    import std.traits;
    alias AliasSeq(T...) = T;

    foreach (T; AliasSeq!(ubyte, ushort, uint, ulong))
    foreach (endian; AliasSeq!(WordEndian.little, WordEndian.big))
    {
        static if (endian == WordEndian.little)
        {
            T[3] lhsData = [1, T.max-1, 0];
            T[3] rhsData = [T.max, T.max, 0];
        }
        else
        {
            T[3] lhsData = [0, T.max-1, 1];
            T[3] rhsData = [0, T.max, T.max];
        }

        auto lhs = BigUIntView!(T, endian)(lhsData).normalized;

        /// bool overflow = bigUInt op= scalar
        assert(lhs.leastSignificantFirst == [1, T.max-1]);
        assert(lhs.mostSignificantFirst == [T.max-1, 1]);
        static if (T.sizeof >= 4)
        {
            assert((lhs += T.max) == false);
            assert(lhs.leastSignificantFirst == [0, T.max]);
            assert((lhs += T.max) == false);
            assert((lhs += T.max) == true); // overflow bit
            assert(lhs.leastSignificantFirst == [T.max-1, 0]);
            assert((lhs -= T(1)) == false);
            assert(lhs.leastSignificantFirst == [T.max-2, 0]);
            assert((lhs -= T.max) == true); // underflow bit
            assert(lhs.leastSignificantFirst == [T.max-1, T.max]);
            assert((lhs -= Signed!T(-4)) == true); // overflow bit
            assert(lhs.leastSignificantFirst == [2, 0]);
            assert((lhs += Signed!T.max) == false); // overflow bit
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0]);

            ///  bool overflow = bigUInt op= bigUInt/bigInt
            lhs = BigUIntView!(T, endian)(lhsData);
            auto rhs = BigUIntView!(T, endian)(rhsData).normalized;
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0, 0]);
            assert(rhs.leastSignificantFirst == [T.max, T.max]);
            assert((lhs += rhs) == false);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 1, 0, 1]);
            assert((lhs -= rhs) == false);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0, 0]);
            assert((lhs += -rhs) == true);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 3, 0, T.max]);
            assert((lhs += -(-rhs)) == true);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0, 0]);

            /// W overflow = bigUInt *= scalar
            assert((lhs *= T.max) == 0);
            assert((lhs += T(Signed!T.max + 2)) == false);
            assert(lhs.leastSignificantFirst == [0, Signed!T.max + 2, 0]);
            lhs = lhs.normalized;
            lhs.leastSignificantFirst[1] = T.max / 2 + 3;
            assert(lhs.leastSignificantFirst == [0, T.max / 2 + 3]);
            assert((lhs *= 8u) == 4);
            assert(lhs.leastSignificantFirst == [0, 16]);
        }
    }
}

/++
Arbitrary length signed integer view.
+/
struct BigIntView(W, WordEndian endian = TargetEndian)
    if (is(Unqual!W == ubyte) || is(Unqual!W == ushort) || is(Unqual!W == uint) || is(Unqual!W == ulong))
{
    import mir.bignum.fp: Fp;

    /++
    Self-assigned to unsigned integer view $(MREF BigUIntView).

    Sign is stored in the most significant bit.

    The number is encoded as pair of `unsigned` and `sign`.
    +/
    BigUIntView!(W, endian) unsigned;

    /++
    Sign bit
    +/
    bool sign;

    ///
    inout(W)[] coefficients() inout @property return scope
    {
        return unsigned.coefficients;
    }

    ///
    this(W[] coefficients, bool sign = false)
    {
        this(BigUIntView!(W, endian)(coefficients), sign);
    }

    ///
    this(BigUIntView!(W, endian) unsigned, bool sign = false)
    {
        this.unsigned = unsigned;
        this.sign = sign;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients.
    +/
    bool fromStringImpl(C)(scope const(C)[] str)
        scope @trusted pure @nogc nothrow
        if (isSomeChar!C)
    {
        import mir.utility: _expect;

        if (_expect(str.length == 0, false))
            return false;

        if (str[0] == '-')
        {
            sign = true;
            str = str[1 .. $];
        }
        else
        if (_expect(str[0] == '+', false))
        {
            str = str[1 .. $];
        }

        return unsigned.fromStringImpl(str);
    }

    /++
    +/
    static BigIntView fromHexString(C, bool allowUnderscores = false)(scope const(C)[] str)
        @trusted pure
        if (isSomeChar!C)
    {
        auto length = str.length / (W.sizeof * 2) + (str.length % (W.sizeof * 2) != 0);
        auto ret = BigIntView!(Unqual!W, endian)(new Unqual!W[length]);
        if (ret.fromHexStringImpl!(C, allowUnderscores)(str))
            return  cast(BigIntView) ret;
        version(D_Exceptions)
            throw hexStringException;
        else
            assert(0, hexStringErrorMsg);
    }

    static if (isMutable!W)
    /++
    +/
    bool fromHexStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        pragma(inline, false);
        import mir.utility: _expect;

        assert(unsigned.coefficients.length);

        if (_expect(str.length == 0, false))
            return false;

        sign = false;

        if (str[0] == '-')
        {
            sign = true;
            str = str[1 .. $];
        }
        else
        if (_expect(str[0] == '+', false))
        {
            str = str[1 .. $];
        }

        return unsigned.fromHexStringImpl!(C, allowUnderscores)(str);
    }

    /++
    +/
    static BigIntView fromBinaryString(C, bool allowUnderscores = false)(scope const(C)[] str)
        @trusted pure
        if (isSomeChar!C)
    {
        auto length = str.length / (W.sizeof * 8) + (str.length % (W.sizeof * 8) != 0);
        auto ret = BigIntView!(Unqual!W, endian)(new Unqual!W[length]);
        if (ret.fromBinaryStringImpl!(C, allowUnderscores)(str))
            return cast(BigIntView) ret;
        version(D_Exceptions)
            throw binaryStringException;
        else
            assert(0, binaryStringErrorMsg);
    }

    static if (isMutable!W)
    /++
    +/
    bool fromBinaryStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        pragma(inline, false);
        import mir.utility: _expect;

        assert(unsigned.coefficients.length);

        if (_expect(str.length == 0, false))
            return false;

        sign = false;

        if (str[0] == '-')
        {
            sign = true;
            str = str[1 .. $];
        }
        else
        if (_expect(str[0] == '+', false))
        {
            str = str[1 .. $];
        }

        return unsigned.fromBinaryStringImpl!(C, allowUnderscores)(str);
    }

    ///
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() scope const
        if (isFloatingPoint!T && isMutable!T)
    {
        auto ret = this.unsigned.opCast!(T, wordNormalized, nonZero);
        if (sign)
            ret = -ret;
        return ret;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto a = cast(double) BigIntView!size_t.fromHexString("-afbbfae3cd0aff2714a1de7022b0029d");
        assert(a == -0xa.fbbfae3cd0bp+124);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto a = cast(double) BigIntView!size_t.fromBinaryString("-10101111101110111111101011100011110011010000101011111111001001110001010010100001110111100111000000100010101100000000001010011101");
        assert(a == -0xa.fbbfae3cd0bp+124);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto a = cast(double) BigIntView!size_t.fromHexString!(char, true)("-afbb_fae3_cd0a_ff27_14a1_de70_22b0_029d");
        assert(a == -0xa.fbbfae3cd0bp+124);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto a = cast(double) BigIntView!size_t.fromBinaryString!(char, true)("-1010_1111_1011_1011_1111_1010_1110_0011_1100_1101_0000_1010_1111_1111_0010_0111_0001_0100_1010_0001_1101_1110_0111_0000_0010_0010_1011_0000_0000_0010_1001_1101");
        assert(a == -0xa.fbbfae3cd0bp+124);
    }

    ///
    T opCast(T, bool nonZero = false)() scope const
        if (is(T == long) || is(T == int))
    {
        auto ret = this.unsigned.opCast!(Unsigned!T, nonZero);
        if (sign)
            ret = -ret;
        return ret;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!size_t.fromHexString("-afbbfae3cd0aff2714a1de7022b0021d");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!size_t.fromHexString!(char, true)("-afbb_fae3_cd0a_ff27_14a1_de70_22b0_021d");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ushort.fromHexString("-afbbfae3cd0aff2714a1de7022b0021d");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }
    
    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ushort.fromHexString!(char, true)("-afbb_fae3_cd0a_ff27_14a1_de70_22b0_021d");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ubyte.fromHexString("-afbbfae3cd0aff2714a1de7022b0021d");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ubyte.fromHexString!(char, true)("-afbb_fae3_cd0a_ff27_14a1_de70_22b0_021d");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!size_t.fromBinaryString!(char, true)("-10101111101110111111101011100011110011010000101011111111001001110001010010100001110111100111000000100010101100000000001000011101");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!size_t.fromBinaryString!(char, true)("-1010_1111_1011_1011_1111_1010_1110_0011_1100_1101_0000_1010_1111_1111_0010_0111_0001_0100_1010_0001_1101_1110_0111_0000_0010_0010_1011_0000_0000_0010_0001_1101");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ushort.fromBinaryString!(char, true)("-10101111101110111111101011100011110011010000101011111111001001110001010010100001110111100111000000100010101100000000001000011101");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ushort.fromBinaryString!(char, true)("-1010_1111_1011_1011_1111_1010_1110_0011_1100_1101_0000_1010_1111_1111_0010_0111_0001_0100_1010_0001_1101_1110_0111_0000_0010_0010_1011_0000_0000_0010_0001_1101");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ubyte.fromBinaryString!(char, true)("-10101111101110111111101011100011110011010000101011111111001001110001010010100001110111100111000000100010101100000000001000011101");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        auto view = BigIntView!ubyte.fromBinaryString!(char, true)("-1010_1111_1011_1011_1111_1010_1110_0011_1100_1101_0000_1010_1111_1111_0010_0111_0001_0100_1010_0001_1101_1110_0111_0000_0010_0010_1011_0000_0000_0010_0001_1101");
        assert(cast(long) view == -0x14a1de7022b0021d);
        assert(cast(int) view == -0x22b0021d);
    }

    /++
    +/
    T opCast(T : Fp!coefficientSize, size_t internalRoundLastBits = 0, bool wordNormalized = false, bool nonZero = false, size_t coefficientSize)() scope const
        if (internalRoundLastBits < size_t.sizeof * 8 && (size_t.sizeof >= W.sizeof || endian == TargetEndian))
    {
        auto ret = unsigned.opCast!(Fp!coefficientSize, internalRoundLastBits, wordNormalized, nonZero);
        ret.sign = sign;
        return ret;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        import mir.bignum.fixed: UInt;
        import mir.bignum.fp: Fp;

        auto fp = cast(Fp!128) BigIntView!size_t.fromHexString("-afbbfae3cd0aff2714a1de7022b0029d");
        assert(fp.sign);
        assert(fp.exponent == 0);
        assert(fp.coefficient == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    version(mir_bignum_test)
    @safe pure
    unittest
    {
        import mir.bignum.fixed: UInt;
        import mir.bignum.fp: Fp;

        auto fp = cast(Fp!128) BigIntView!size_t.fromHexString!(char, true)("-afbb_fae3_cd0a_ff27_14a1_de70_22b0_029d");
        assert(fp.sign);
        assert(fp.exponent == 0);
        assert(fp.coefficient == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));
    }

    static if (endian == TargetEndian)
    ///
    BigIntView!V opCast(T : BigIntView!V, V)() return scope
        if (V.sizeof <= W.sizeof)
    {
        return typeof(return)(this.unsigned.opCast!(BigUIntView!V), sign);
    }

    ///
    BigIntView!(const W, endian) lightConst()() return scope
        const @safe pure nothrow @nogc @property
    {
        return typeof(return)(unsigned.lightConst, sign);
    }

    ///ditto
    alias lightConst this;

    /++
    +/
    sizediff_t opCmp(BigIntView!(const W, endian) rhs) 
        const @safe pure nothrow @nogc scope
    {
        import mir.algorithm.iteration: cmp;
        if (auto s = rhs.sign - this.sign)
        {
            if (this.unsigned.coefficients.length && rhs.unsigned.coefficients.length)
                return s;
        }
        auto d = this.unsigned.opCmp(rhs.unsigned);
        return sign ? -d : d;
    }

    ///
    bool opEquals(BigIntView!(const W, endian) rhs)
        const @safe pure nothrow @nogc scope
    {
        return (this.sign == rhs.sign || unsigned.coefficients.length == 0) && this.unsigned == rhs.unsigned;
    }

    /++
    Returns: true if the integer and equals to `rhs`.
    +/
    bool opEquals(long rhs)
        @safe pure nothrow @nogc const scope
    {
        if (rhs == 0 && unsigned.coefficients.length == 0)
            return true;
        bool sign = rhs < 0;
        ulong urhs = sign ? -rhs : rhs;
        return sign == this.sign && unsigned == urhs;
    }

    /++
    +/
    BigIntView topMostSignificantPart(size_t length)
    {
        return BigIntView(unsigned.topMostSignificantPart(length), sign);
    }

    /++
    +/
    BigIntView topLeastSignificantPart(size_t length)
    {
        return BigIntView(unsigned.topLeastSignificantPart(length), sign);
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `bool overflow = big +(-)= big` operatrion.
    Params:
        rhs = value to add with non-empty coefficients
        overflow = (overflow) initial iteration overflow
    Precondition: non-empty coefficients length of greater or equal to the `rhs` coefficients length.
    Returns:
        true in case of unsigned overflow
    +/
    bool opOpAssign(string op)(scope BigIntView!(const W, endian) rhs, bool overflow = false)
    @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        assert(rhs.coefficients.length > 0);
        import mir.conv;
        debug assert(this.coefficients.length >= rhs.coefficients.length, this.coefficients.length.to!string ~ " " ~ rhs.coefficients.length.to!string);
        enum sum = op == "+";
        // pos += pos
        // neg += neg
        // neg -= pos
        // pos -= neg
        if ((sign == rhs.sign) == sum)
            return unsigned.opOpAssign!"+"(rhs.unsigned, overflow);
        // pos -= pos
        // pos += neg
        // neg += pos
        // neg -= neg
        if (unsigned.opOpAssign!"-"(rhs.unsigned, overflow))
        {
            sign = !sign;
            unsigned.twoComplementInPlace;
        }
        return false;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /// ditto
    bool opOpAssign(string op)(scope BigUIntView!(const W, endian) rhs, bool overflow = false)
    @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        return opOpAssign!op(rhs.signed, overflow);
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `bool overflow = big +(-)= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = value to add
    Returns:
        true in case of unsigned overflow
    +/
    bool opOpAssign(string op, T)(const T rhs)
        @safe pure nothrow @nogc
        if ((op == "+" || op == "-") && is(T == Signed!W))
    {
        assert(this.coefficients.length > 0);
        enum sum = op == "+";
        // pos += pos
        // neg += neg
        // neg -= pos
        // pos -= neg
        auto urhs = cast(W) (rhs < 0 ? -rhs : rhs);
        if ((sign == (rhs < 0)) == sum)
            return unsigned.opOpAssign!"+"(urhs);
        // pos -= pos
        // pos += neg
        // neg += pos
        // neg -= neg
        if (unsigned.opOpAssign!"-"(urhs))
        {
            sign = !sign;
            unsigned.twoComplementInPlace;
        }
        return false;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /// ditto
    bool opOpAssign(string op, T)(const T rhs)
        @safe pure nothrow @nogc
        if ((op == "+" || op == "-") && is(T == W))
    {
        assert(this.coefficients.length > 0);
        enum sum = op == "+";
        // pos += pos
        // neg -= pos
        if ((sign == false) == sum)
            return unsigned.opOpAssign!"+"(rhs);
        // pos -= pos
        // neg += pos
        if (unsigned.opOpAssign!"-"(rhs))
        {
            sign = !sign;
            unsigned.twoComplementInPlace;
        }
        return false;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `W overflow = (big += overflow) *= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned value to multiply by
        overflow = initial overflow
    Returns:
        unsigned overflow value
    +/
    W opOpAssign(string op : "*")(W rhs, W overflow = 0u)
        @safe pure nothrow @nogc
    {
        return unsigned.opOpAssign!op(rhs, overflow);
    }

    /++
    Returns: the same intger view with inversed sign
    +/
    BigIntView opUnary(string op : "-")()
    {
        return BigIntView(unsigned, !sign);
    }

    /++
    Returns: a slice of coefficients starting from the least significant.
    +/
    auto leastSignificantFirst()
        @safe pure nothrow @nogc @property
    {
        return unsigned.leastSignificantFirst;
    }

    /++
    Returns: a slice of coefficients starting from the most significant.
    +/
    auto mostSignificantFirst()
        @safe pure nothrow @nogc @property
    {
        return unsigned.mostSignificantFirst;
    }

    /++
    Strips zero most significant coefficients.
    Strips most significant zero coefficients.
    Sets sign to zero if no coefficients were left.
    +/
    BigIntView normalized()
    {
        auto number = this;
        number.unsigned = number.unsigned.normalized;
        number.sign = number.coefficients.length == 0 ? false : number.sign;
        return number;
    }

    ///ditto
    BigIntView!(const W, endian) normalized() const
    {
        return lightConst.normalized;
    }
}

///
version(mir_bignum_test)
@safe pure nothrow
unittest
{
    import std.traits;
    alias AliasSeq(T...) = T;

    foreach (T; AliasSeq!(ubyte, ushort, uint, ulong))
    foreach (endian; AliasSeq!(WordEndian.little, WordEndian.big))
    {
        static if (endian == WordEndian.little)
        {
            T[3] lhsData = [1, T.max-1, 0];
            T[3] rhsData = [T.max, T.max, 0];
        }
        else
        {
            T[3] lhsData = [0, T.max-1, 1];
            T[3] rhsData = [0, T.max, T.max];
        }

        auto lhs = BigIntView!(T, endian)(lhsData).normalized;

        ///  bool overflow = bigUInt op= scalar
        assert(lhs.leastSignificantFirst == [1, T.max-1]);
        assert(lhs.mostSignificantFirst == [T.max-1, 1]);

        static if (T.sizeof >= 4)
        {

            assert((lhs += T.max) == false);
            assert(lhs.leastSignificantFirst == [0, T.max]);
            assert((lhs += T.max) == false);
            assert((lhs += T.max) == true); // overflow bit
            assert(lhs.leastSignificantFirst == [T.max-1, 0]);
            assert((lhs -= T(1)) == false);
            assert(lhs.leastSignificantFirst == [T.max-2, 0]);
            assert((lhs -= T.max) == false);
            assert(lhs.leastSignificantFirst == [2, 0]);
            assert(lhs.sign);
            assert((lhs -= Signed!T(-4)) == false);
            assert(lhs.leastSignificantFirst == [2, 0]);
            assert(lhs.sign == false);
            assert((lhs += Signed!T.max) == false);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0]);

            ///  bool overflow = bigUInt op= bigUInt/bigInt
            lhs = BigIntView!(T, endian)(lhsData);
            auto rhs = BigUIntView!(T, endian)(rhsData).normalized;
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0, 0]);
            assert(rhs.leastSignificantFirst == [T.max, T.max]);
            assert((lhs += rhs) == false);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 1, 0, 1]);
            assert((lhs -= rhs) == false);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0, 0]);
            assert((lhs += -rhs) == false);
            assert(lhs.sign);
            assert(lhs.leastSignificantFirst == [T.max - (Signed!T.max + 2), T.max, 0]);
            assert(lhs.sign);
            assert((lhs -= -rhs) == false);
            assert(lhs.leastSignificantFirst == [Signed!T.max + 2, 0, 0]);
            assert(lhs.sign == false);
        }
    }
}

///
version(mir_bignum_test)
unittest
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.low_level_view: BigUIntView;
    auto bigView = BigUIntView!size_t.fromHexString("55a325ad18b2a77120d870d987d5237473790532acab45da44bc07c92c92babf0b5e2e2c7771cd472ae5d7acdb159a56fbf74f851a058ae341f69d1eb750d7e3");
    auto fixed = UInt!256.fromHexString("55e5669576d31726f4a9b58a90159de5923adc6c762ebd3c4ba518d495229072");
    auto overflow = bigView *= fixed;
    assert(overflow == UInt!256.fromHexString("1cbbe8c42dc21f936e4ce5b2f52ac404439857f174084012fcd1b71fdec2a398"));
    assert(bigView == BigUIntView!size_t.fromHexString("c73fd2b26f2514c103c324943b6c90a05d2732118d5f0099c36a69a8051bb0573adc825b5c9295896c70280faa4c4d369df8e92f82bfffafe078b52ae695d316"));

}

///
version(mir_bignum_test)
unittest
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.low_level_view: BigUIntView;
    auto bigView2 = BigUIntView!size_t.fromHexString("55a325ad18b2a77120d870d987d5237473790532acab45da44bc07c92c92babf0b5e2e2c7771cd472ae5d7acdb159a56fbf74f851a058ae341f69d1eb750d7e3");
    auto bigView = BigUIntView!size_t.fromHexString!(char, true)("55a3_25ad_18b2_a771_20d8_70d9_87d5_2374_7379_0532_acab_45da_44bc_07c9_2c92_babf_0b5e_2e2c_7771_cd47_2ae5_d7ac_db15_9a56_fbf7_4f85_1a05_8ae3_41f6_9d1e_b750_d7e3");
    auto fixed = UInt!256.fromHexString!(true)("55e5_6695_76d3_1726_f4a9_b58a_9015_9de5_923a_dc6c_762e_bd3c_4ba5_18d4_9522_9072");
    auto overflow = bigView *= fixed;
    assert(overflow == UInt!256.fromHexString("1cbbe8c42dc21f936e4ce5b2f52ac404439857f174084012fcd1b71fdec2a398"));
    assert(bigView == BigUIntView!size_t.fromHexString("c73fd2b26f2514c103c324943b6c90a05d2732118d5f0099c36a69a8051bb0573adc825b5c9295896c70280faa4c4d369df8e92f82bfffafe078b52ae695d316"));
}

/++
An utility type to wrap a local buffer to accumulate unsigned numbers.
+/
struct BigUIntAccumulator(W, WordEndian endian = TargetEndian)
    if (is(Unqual!W == uint) || is(Unqual!W == ulong))
{
    /++
    A group of coefficients for a $(MREF DecimalRadix)`!W`.

    The order corresponds to endianness.

    The unused part can be uninitialized.
    +/
    W[] coefficients;

    /++
    Current length of initialized coefficients.

    The initialization order corresponds to endianness.

    The `view` method may return a view with empty coefficients, which isn't usable.
    Put `0` or another number first to make the accumulator maintain a non-empty view.
    +/
    size_t length;

    /++
    Returns:
        Current unsigned integer view.
    Note:
        The method may return a view with empty coefficients, which isn't usable.
        Put `0` or another number first to make the accumulator maintain a non-empty view.
    +/
    BigUIntView!(W, endian) view() @safe pure nothrow @nogc @property
    {
        static if (endian == WordEndian.little)
            return typeof(return)(coefficients[0 .. length]);
        else
            return typeof(return)(coefficients[$ - length .. $]);
    }

    /++
    Returns:
        True if the accumulator can accept next most significant coefficient 
    +/
    bool canPut() @property
    {
        return length < coefficients.length;
    }

    /++
    Places coefficient to the next most significant position.
    +/
    void put(W coeffecient)
    in {
        assert(length < coefficients.length);
    }
    do {
        static if (endian == WordEndian.little)
            coefficients[length++] = coeffecient;
        else
            coefficients[$ - ++length] = coeffecient;
    }

    /++
    Strips most significant zero coefficients from the current `view`.
    Note:
        The `view` method may return a view with empty coefficients, which isn't usable.
        Put `0` or another number first to make the accumulator maintain a non-empty view.
    +/
    void normalize()
    {
        length = view.normalized.coefficients.length;
    }

    ///
    bool canPutN(size_t n)
    {
        return length + n <= coefficients.length;
    }

    ///
    bool approxCanMulPow5(size_t degree)
    {
        // TODO: more precise result
        enum n = MaxWordPow5!W;
        return canPutN(degree / n + (degree % n != 0));
    }

    ///
    bool canMulPow2(size_t degree)
    {
        import mir.bitop: ctlz;
        enum n = W.sizeof * 8;
        return canPutN(degree / n + (degree % n > ctlz(view.mostSignificant)));
    }

    ///
    void mulPow5(size_t degree)
    {
        // assert(approxCanMulPow5(degree));
        enum n = MaxWordPow5!W;
        enum wordInit = W(5) ^^ n;
        W word = wordInit;
        while(degree)
        {
            if (degree >= n)
            {
                degree -= n;
            }
            else
            {
                word = 1;
                do word *= 5;
                while(--degree);
            }
            if (auto overflow = view *= word)
            {
                put(overflow);
            }
        }
    }

    ///
    void mulPow2(size_t degree) scope @safe
    {
        import mir.bitop: ctlz;
        assert(canMulPow2(degree));
        enum n = W.sizeof * 8;
        auto ws = degree / n;
        auto oldLength = length;
        length += ws;
        if (ws)
        {
            auto v = view.leastSignificantFirst;
            foreach_reverse (i; 0 .. oldLength)
            {
                v[i + ws] = v[i];
            }
            do v[--ws] = 0;
            while(ws);
        }

        if (auto tail = cast(uint)(degree % n))
        {
            if (tail > ctlz(view.mostSignificant))
            {
                put(0);
                oldLength++;
            }
            view.topMostSignificantPart(oldLength).smallLeftShiftInPlace(tail);
        }
    }
}

///
version(mir_bignum_test)
@safe pure
unittest
{
    import std.traits;
    alias AliasSeq(T...) = T;

    foreach (T; AliasSeq!(uint, ulong))
    foreach (endian; AliasSeq!(WordEndian.little, WordEndian.big))
    {
        T[16 / T.sizeof] buffer;
        auto accumulator = BigUIntAccumulator!(T, endian)(buffer);
        assert(accumulator.length == 0);
        assert(accumulator.coefficients.length == buffer.length);
        assert(accumulator.view.coefficients.length == 0);
        // needs to put a number before any operations on `.view`
        accumulator.put(1);
        // compute N factorial
        auto N = 30;
        foreach(i; 1 .. N + 1)
        {
            if (auto overflow = accumulator.view *= i)
            {
                if (!accumulator.canPut)
                    throw new Exception("Factorial buffer overflow");
                accumulator.put(overflow);
            }
        }
        assert(accumulator.view == BigUIntView!(T, endian).fromHexString("D13F6370F96865DF5DD54000000"));
    }
}

/// Computes `13 * 10^^60`
version(mir_bignum_test)
@safe pure
unittest
{
    uint[7] buffer;
    auto accumulator = BigUIntAccumulator!uint(buffer);
    accumulator.put(13); // initial value
    assert(accumulator.approxCanMulPow5(60));
    accumulator.mulPow5(60);
    assert(accumulator.canMulPow2(60));
    accumulator.mulPow2(60);
    assert(accumulator.view == BigUIntView!uint.fromHexString("81704fcef32d3bd8117effd5c4389285b05d000000000000000"));
}

///
enum DecimalExponentKey
{
    ///
    none = 0,
    ///
    infinity = 1,
    ///
    nan = 2,
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
}

/++
+/
struct DecimalView(W, WordEndian endian = TargetEndian)
    if (isUnsigned!W)
{
    ///
    bool sign;
    ///
    long exponent;
    ///
    BigUIntView!(W, endian) coefficient;

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients
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
        import mir.utility: _expect;

        version(LDC)
        {
            static if ((allowSpecialValues && allowDExponent && allowStartingPlus && allowDotOnBounds && checkEmpty) == false)
                pragma(inline, true);
        }

        assert(coefficient.coefficients.length);

        coefficient.leastSignificant = 0;
        auto work = coefficient.topLeastSignificantPart(1);

        static if (checkEmpty)
        {
            if (_expect(str.length == 0, false))
                return false;
        }

        if (str[0] == '-')
        {
            sign = true;
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

        W v;
        W t = 1;
        bool dot;

        static if (allowUnderscores)
        {
            bool recentUnderscore;
        }

        // Was there a recent character within the set: ['.', 'e', 'E', 'd', 'D']?
        bool recentModifier;

        static if (!allowLeadingZeros)
        {
            if (d == 0)
            {
                if (str.length == 0)
                {
                    coefficient = coefficient.init;
                    return true;
                }
                if (str[0] >= '0' && str[0] <= '9')
                    return false;
                goto S;
            }
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
                recentModifier = true;
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
            enum mp10 = W(10) ^^ MaxWordPow10!W;
            d = str[0] - '0';
            str = str[1 .. $];

            if (_expect(d <= 10, true))
            {
                static if (allowUnderscores)
                {
                    recentUnderscore = false;
                }
                recentModifier = false;
                v *= 10;
        S:
                t *= 10;
                v += d;
                exponentShift -= dot;

                if (_expect(t == mp10 || str.length == 0, false))
                {
                L:
                    if (auto overflow = work.opOpAssign!"*"(t, v))
                    {
                        if (_expect(work.coefficients.length < coefficient.coefficients.length, true))
                        {
                            work = coefficient.topLeastSignificantPart(work.coefficients.length + 1);
                            work.mostSignificant = overflow;
                        }
                        else
                        {
                            return false;
                        }
                    }

                    v = 0;
                    t = 1;
                    if (str.length == 0)
                    {
                    M:
                        exponent += exponentShift;
                        coefficient = work.mostSignificant == 0 ? coefficient.init : work;
                        static if (allowUnderscores)
                        {
                            // If we have no characters, then we should return true IF
                            // the last character was NOT a underscore OR a modifier
                            return !recentUnderscore && !recentModifier;
                        }
                        else
                        {
                            // If we don't allow underscores, and we have no characters,
                            // then we should return true IF the character was NOT a modifier.
                            return !recentModifier;
                        }
                    }
                }

                continue;
            }

            switch (d)
            {
                case DecimalExponentKey.dot:
                    // The dot modifier CANNOT be preceded by any modifiers. 
                    if (recentModifier || key != DecimalExponentKey.none)
                        return false;

                    static if (allowUnderscores)
                    {
                        // If we allow underscores, the dot also CANNOT be preceded by any underscores.
                        // It must be preceded by a number.
                        if (recentUnderscore)
                            return false;
                    }

                    key = DecimalExponentKey.dot;
                    if (_expect(dot, false))
                        break;
                    dot = true;
                    if (str.length)
                    {
                        recentModifier = true;
                        continue;
                    }
                    static if (allowDotOnBounds)
                    {
                        goto L;
                    }
                    else
                    {
                        return false;
                    }
                static if (allowExponent)
                {
                    static if (allowDExponent)
                    {
                        case DecimalExponentKey.d:
                        case DecimalExponentKey.D:
                            goto case DecimalExponentKey.e;
                    }
                    case DecimalExponentKey.e:
                    case DecimalExponentKey.E:
                        import mir.parse: parse;
                        // We don't really care if the e/E/d/D modifiers are preceded by a modifier,
                        // so as long as they are a dot or a regular number.
                        if (key != DecimalExponentKey.dot && key != DecimalExponentKey.none)
                            return false;
                        key = cast(DecimalExponentKey)d;
                        if (parse(str, exponent) && str.length == 0)
                        {
                            recentModifier = false;
                            if (t != 1)
                                goto L;
                            goto M;
                        }
                        break;
                }
                static if (allowUnderscores)
                {
                    case '_' - '0':
                        // A underscore cannot be preceded by an underscore or a modifier.
                        if (recentUnderscore || recentModifier)
                            return false;
                        
                        recentUnderscore = true;
                        if (str.length)
                            continue;
                        break;
                }
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
                    coefficient = coefficient.init;
                    key = DecimalExponentKey.infinity;
                    return true;
                }
                if (d == 'n' - '0' && stail == cast(C[2])"an" || d == 'N' - '0' && (stail == cast(C[2])"aN" || stail == cast(C[2])"AN"))
                {
                    coefficient.leastSignificant = 1;
                    coefficient = coefficient.topLeastSignificantPart(1);
                    key = DecimalExponentKey.nan;
                    return true;
                }
            }
            return false;
        }
    }

    ///
    DecimalView!(const W, endian) lightConst()()
        const @safe pure nothrow @nogc @property
    {
        return typeof(return)(sign, exponent, coefficient.lightConst);
    }
    ///ditto
    alias lightConst this;

    /++
    +/
    BigIntView!(W, endian) signedCoefficient()
    {
        return typeof(return)(coefficient, sign);
    }

    /++
    Mir parsing supports up-to quadruple precision. The conversion error is 0 ULP for normal numbers. 
    Subnormal numbers with an exponent greater than or equal to -512 have upper error bound equal to 1 ULP.
    +/
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() scope const
        if (isFloatingPoint!T && isMutable!T)
    {
        version(LDC)
        {
            static if (wordNormalized)
                pragma(inline, true);
        }

        import mir.bignum.fixed: UInt;
        import mir.bignum.fp: Fp, extendedMul;
        import mir.bignum.internal.dec2flt_table;
        import mir.math.common: floor;
        import mir.utility: _expect;

        auto coeff = coefficient.lightConst;
        T ret = 0;

        static if (!wordNormalized)
            coeff = coeff.normalized;

        if (_expect(exponent == exponent.max, false))
        {
            ret = coeff.coefficients.length ? T.nan : T.infinity;
            goto R;
        }

        static if (!nonZero)
            if (coeff.coefficients.length == 0)
                goto R;

        enum S = 9;

        static if (T.mant_dig < 64)
        {
            Fp!64 load(long e)
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

                    auto c = coeff.opCast!(Fp!64, 0, true, true);
                    auto z = c.extendedMul(load(exponent));
                    ret = cast(T) z;
                    auto slop = (coeff.coefficients.length > (ulong.sizeof / W.sizeof)) + 3 * expSign;
                    long bitsDiff = (cast(ulong) z.opCast!(Fp!64).coefficient & mask) - half;
                    if (_expect((bitsDiff < 0 ? -bitsDiff : bitsDiff) > slop, true))
                        goto R;
                    if (slop == 0 && exponent <= MaxWordPow5!ulong || exponent == 0)
                        goto R;
                    if (slop == 3 && MaxFpPow5!T >= -exponent && cast(ulong)c.coefficient < bound)
                    {
                        auto e = load(-exponent);
                        ret =  c.opCast!(T, true) / cast(T) (cast(ulong)e.coefficient >> e.exponent);
                        goto R;
                    }
                    ret = algoR!T(ret, coeff, cast(int) exponent);
                    goto R;
                }
                ret = expSign ? 0 : T.infinity;
                goto R;
            }
        }
        else
        {
            enum P = 1 << S;
            static assert(min_p10_e <= -P);
            static assert(max_p10_e >= P);
            Fp!128 load(long e)
            {
                auto idx = cast(sizediff_t)e - min_p10_e;
                ulong h = p10_coefficients[idx][0];
                ulong l = p10_coefficients[idx][1];
                if (l >= cast(ulong)long.min)
                    h--;
                version(BigEndian)
                    auto p10coeff = UInt!128(cast(ulong[2])[h, l]);
                else
                    auto p10coeff = UInt!128(cast(ulong[2])[l, h]);
                auto p10exp = p10_exponents[idx] - 64;
                return Fp!128(false, p10exp, p10coeff);
            }

            {
                auto expSign = exponent < 0;
                ulong exp = exponent;
                exp = expSign ? -exp : exp;
                if (exp >= 5000)
                {
                    ret = expSign ? 0 : T.infinity;
                    goto R;
                }
                long index = exp & 0x1FF;
                bool gotoAlgoR;
                auto c = load(expSign ? -index : index);
                {
                    exp >>= S;
                    gotoAlgoR = exp != 0;
                    if (_expect(gotoAlgoR, false))
                    {
                        auto v = load(expSign ? -P : P);
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
                auto z = coeff.opCast!(Fp!128, 0, true, true).extendedMul(c);
                ret = cast(T) z;
                if (!gotoAlgoR)
                {
                    static if (T.mant_dig == 64)
                        enum ulong mask = ulong.max;
                    else
                        enum ulong mask = (1UL << (128 - T.mant_dig)) - 1;
                    enum ulong half = (1UL << (128 - T.mant_dig - 1));
                    enum UInt!128 bound = UInt!128(1) << T.mant_dig;

                    auto slop = (coeff.coefficients.length > (ulong.sizeof * 2 / W.sizeof)) + 3 * expSign;
                    long bitsDiff = (cast(ulong) z.opCast!(Fp!128).coefficient & mask) - half;
                    if (_expect((bitsDiff < 0 ? -bitsDiff : bitsDiff) > slop, true))
                        goto R;
                    if (slop == 0 && exponent <= 55 || exponent == 0)
                        goto R;
                    if (slop == 3 && MaxFpPow5!T >= -exponent && c.coefficient < bound)
                    {
                        auto e = load(-exponent);
                        ret =  c.opCast!(T, true) / cast(T) e;
                        goto R;
                    }
                }
                ret = algoR!T(ret, coeff, cast(int) exponent);
                goto R;
            }
        }
    R:
        if (sign)
            ret = -ret;
        return ret;
    }
}

@optStrategy("minsize")
package T algoR(T, W, WordEndian endian)(T ret, scope BigUIntView!(const W, endian) coeff, int exponent)
{
    pragma(inline, false);

    import mir.bignum.fixed: UInt;
    import mir.bignum.integer: BigInt;
    import mir.math.common: floor;
    import mir.math.ieee: ldexp, frexp, nextDown, nextUp;
    import mir.utility: _expect;

    BigInt!256 x = void, y = void; // max value is 2^(2^14)-1
    if (exponent >= 0)
    {
        if (!x.copyFrom(coeff) && !x.mulPow5(exponent)) // if no overflow
            ret = ldexp(cast(T) x, exponent);
    }
    else do
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
        y.__ctor(m);
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

///
version(mir_bignum_test)
unittest
{
    alias AliasSeq(T...) = T;

    foreach (T; AliasSeq!(float, double, real))
    {{
        T value = 3.518437208883201171875E+013;
        
    }}

    foreach(E; AliasSeq!(WordEndian.little, WordEndian.big))
    foreach(W; AliasSeq!(ulong, uint, ushort, ubyte))
    static if (!(E != TargetEndian && (W.sizeof > size_t.sizeof || W.sizeof == 1)))
    {{
        alias Args = AliasSeq!(W, E);

        auto view = DecimalView!Args(false, -8, BigUIntView!Args.fromHexString("BEBC2000000011E1A3"));

        assert (cast(float)view == 3.518437208883201171875E+013f);
        assert (cast(double)view == 3.518437208883201171875E+013);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 3.518437208883201171875E+013L);

        view = DecimalView!Args(true, -169, BigUIntView!Args.fromHexString("5A174AEDA65CC"));
        assert (cast(float)view == -0);
        assert (cast(double)view == -0x1.1p-511);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == -0x8.80000000000019fp-514L);

        view = DecimalView!Args(true, 293, BigUIntView!Args.fromHexString("36496F6C4ED38"));
        assert (cast(float)view == -float.infinity);
        assert (cast(double)view == -9.55024478104888e+307);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == -9.55024478104888e+307L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 1);
        assert (cast(double)view == 1);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1L);

        view = DecimalView!Args(false, -5, BigUIntView!Args.fromHexString("3"));
        assert (cast(float)view == 3e-5f);
        assert (cast(double)view == 3e-5);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 3e-5L);

        view = DecimalView!Args(false, -1, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0.1f);
        assert (cast(double)view == 0.1);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0.1L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("3039"));
        assert (cast(float)view == 12345.0f);
        assert (cast(double)view == 12345.0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 12345.0L);

        view = DecimalView!Args(false, -7, BigUIntView!Args.fromHexString("98967F"));
        assert (cast(float)view == 0.9999999f);
        assert (cast(double)view == 0.9999999);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0.9999999L);

        view = DecimalView!Args(false, -324, BigUIntView!Args.fromHexString("4F0CEDC95A718E"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 2.2250738585072014e-308);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 2.2250738585072014e-308L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("1FFFFFFFFFFFFFFFD"));
        assert (cast(float)view == 36893488147419103229f);
        assert (cast(double)view == 36893488147419103229.0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x1FFFFFFFFFFFFFFFDp0L);

        view = DecimalView!Args(false, -33, BigUIntView!Args.fromHexString("65"));
        assert (cast(float)view == 101e-33f);
        assert (cast(double)view == 101e-33);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 101e-33L);

        view = DecimalView!Args(false, 23, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 1e23f);
        assert (cast(double)view == 1e23);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e23L);

        view = DecimalView!Args(false, 23, BigUIntView!Args.fromHexString("81B"));
        assert (cast(float)view == 2075e23f);
        assert (cast(double)view == 0xaba3d58a1f1a98p+32);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xaba3d58a1f1a9cp+32L);
    
        view = DecimalView!Args(false, -23, BigUIntView!Args.fromHexString("2209"));
        assert (cast(float)view == 8713e-23f);
        assert (cast(double)view == 0x1.9b75b4e7de2b9p-64);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xc.dbada73ef15c401p-67L);

        view = DecimalView!Args(false, 300, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == 0x1.7e43c8800759cp+996);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xb.f21e44003acdd2dp+993L);

        view = DecimalView!Args(false, 245, BigUIntView!Args.fromHexString("B3A73CEB227"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == 0x1.48e3735333cb6p+857);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xa.471b9a999e5b01ep+854L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("88BF4748507FB9900ADB624CCFF8D78897DC900FB0460327D4D86D327219"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == 0x1.117e8e90a0ff7p+239);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.8bf4748507fb99p+236L);

        view = DecimalView!Args(false, -324, BigUIntView!Args.fromHexString("5"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x0.0000000000001p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.18995ce7aa0e1b2p-1077L);

        view = DecimalView!Args(false, -324, BigUIntView!Args.fromHexString("5B"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x0.0000000000012p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x9.3594d9adeb09a55p-1073L);

        view = DecimalView!Args(false, -322, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x0.0000000000014p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xa.1ebfb4219491a1fp-1073L);

        view = DecimalView!Args(false, -320, BigUIntView!Args.fromHexString("CA1CCB"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x0.000063df832d9p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xc.7bf065b215888c7p-1043L);

        view = DecimalView!Args(false, -319, BigUIntView!Args.fromHexString("33CE7943FB"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x1.000000000162p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.000000000b103b6p-1025L);

        view = DecimalView!Args(false, -309, BigUIntView!Args.fromHexString("15"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x0.f19c2629ccf53p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xf.19c2629ccf52fc4p-1026L);

        view = DecimalView!Args(false, -340, BigUIntView!Args.fromHexString("AF87023B9BF0EE"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x0.0000000000001p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xf.fffffffffffff64p-1078L);

        view = DecimalView!Args(false, 400, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xd.a763fc8cb9ff9e6p+1325L);

        view = DecimalView!Args(false, 309, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xb.201833b35d63f73p+1023L);

        view = DecimalView!Args(false, 308, BigUIntView!Args.fromHexString("2"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.e679c2f5e44ff8fp+1021L);

        view = DecimalView!Args(false, 308, BigUIntView!Args.fromHexString("2"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.e679c2f5e44ff8fp+1021L);

        view = DecimalView!Args(false, 295, BigUIntView!Args.fromHexString("1059949B7090"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.00000000006955ap+1021L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("0"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.init);
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0L);

        view = DecimalView!Args(false, -325, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xa.5ced43b7e3e9188p-1083L);

        view = DecimalView!Args(false, -326, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.4a57695fe98746dp-1086L);

        view = DecimalView!Args(false, -500, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.33ada2003db9a8p-1664L);

        view = DecimalView!Args(false, -1000, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.68a9188a89e1467p-3325L);

        view = DecimalView!Args(false, -4999, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0L);

        view = DecimalView!Args(false, -10000, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0L);

        view = DecimalView!Args(false, -4969, BigUIntView!Args.fromHexString("329659A941466C6B"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == real.min_normal * real.epsilon);

        view = DecimalView!Args(false, -15, BigUIntView!Args.fromHexString("525DB0200FFAB"));
        assert (cast(float)view == 1.448997445238699f);
        assert (cast(double)view == 0x1.72f17f1f49aadp+0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xb.978bf8fa4d56cp-3L);

        view = DecimalView!Args(false, -15, BigUIntView!Args.fromHexString("525DB0200FFAB"));
        assert (cast(float)view == 1.448997445238699f);
        assert (cast(double)view == 0x1.72f17f1f49aadp+0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xb.978bf8fa4d56cp-3L);

        view = DecimalView!Args(false, -325, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xa.5ced43b7e3e9188p-1083L);

        view = DecimalView!Args(false, -326, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8.4a57695fe98746dp-1086L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 1);
        assert (cast(double)view == 0x1p+0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0x8p-3L);

        view = DecimalView!Args(false, -5, BigUIntView!Args.fromHexString("3"));
        assert (cast(float)view == 3e-5f);
        assert (cast(double)view == 0x1.f75104d551d69p-16);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xf.ba8826aa8eb4635p-19L);

        view = DecimalView!Args(false, -1, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0.1f);
        assert (cast(double)view == 0x1.999999999999ap-4);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xc.ccccccccccccccdp-7L);

        view = DecimalView!Args(false, -7, BigUIntView!Args.fromHexString("98967F"));
        assert (cast(float)view == 0.9999999f);
        assert (cast(double)view == 0x1.fffffca501acbp-1);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0xf.ffffe5280d65435p-4L);
    }}
}

/++
+/
struct BinaryView(W, WordEndian endian = TargetEndian)
{
    ///
    bool sign;
    ///
    long exponent;
    ///
    BigUIntView!(W, endian) coefficient;

    ///
    DecimalView!(const W, endian) lightConst()()
        const @safe pure nothrow @nogc @property
    {
        return typeof(return)(sign, exponent, coefficient.lightConst);
    }
    ///ditto
    alias lightConst this;

    /++
    +/
    BigIntView!(W, endian) signedCoefficient()
    {
        return typeof(return)(sign, coefficients);
    }
}
