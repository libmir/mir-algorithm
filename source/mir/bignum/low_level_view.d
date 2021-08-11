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
version (D_Exceptions)
{
    package immutable hexStringException = new Exception(hexStringErrorMsg);
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
    BigUIntView!V opCast(T : BigUIntView!V, V)() scope return
        if (V.sizeof <= W.sizeof)
    {
        return typeof(return)(cast(V[])this.coefficients);
    }

    ///
    BigUIntView!(const W, endian) lightConst()()
        const @safe pure nothrow @nogc @property scope return
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
    ref inout(W) mostSignificant() inout @property scope return
    {
        static if (endian == WordEndian.big)
            return coefficients[0];
        else
            return coefficients[$ - 1];
    }

    /++
    +/
    ref inout(W) leastSignificant() inout @property scope return
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
    BigUIntView topMostSignificantPart(size_t length) scope return
    {
        static if (endian == WordEndian.big)
            return BigUIntView(coefficients[0 .. length]);
        else
            return BigUIntView(coefficients[$ - length .. $]);
    }

    /++
    +/
    BigUIntView topLeastSignificantPart(size_t length) scope return
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
    static BigUIntView fromHexString(C)(scope const(C)[] str)
        @trusted pure
        if (isSomeChar!C)
    {
        auto length = str.length / (W.sizeof * 2) + (str.length % (W.sizeof * 2) != 0);
        auto data = new Unqual!W[length];
        if (BigUIntView!(Unqual!W, endian)(data).fromHexStringImpl(str))
            return BigUIntView(cast(W[])data);
        version(D_Exceptions)
            throw hexStringException;
        else
            assert(0, hexStringErrorMsg);
    }

    static if (isMutable!W)
    /++
    +/
    bool fromHexStringImpl(C)(scope const(C)[] str)
        @safe pure @nogc nothrow scope
        if (isSomeChar!C)
    {
        pragma(inline, false);
        import mir.utility: _expect;
        if (_expect(str.length == 0 || str.length > coefficients.length * W.sizeof * 2, false))
            return false;
        coefficients = coefficients[0 .. str.length / (W.sizeof * 2) + (str.length % (W.sizeof * 2) != 0)];
        auto rdata = leastSignificantFirst;
        W current;
        size_t i;
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
                default: return false;
            }
            enum s = W.sizeof * 8 - 4;
            W cc = cast(W)(W(c) << s);
            current >>>= 4;
            current |= cc;
            if (i % (W.sizeof * 2) == 0)
            {
                rdata.front = current;
                rdata.popFront;
                current = 0;
            }
        }
        while(i < str.length);
        if (current)
        {
            current >>>= 4 * (W.sizeof * 2 - i % (W.sizeof * 2));
            rdata.front = current;
        }
        return true;
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients
    Note: doesn't support signs.
    +/
    bool fromStringImpl(C)(scope const(C)[] str)
        @safe pure @nogc nothrow
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
    BigIntView!(W, endian) opUnary(string op : "-")() scope return
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
        @safe pure nothrow @nogc @property scope return
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
        const @safe pure nothrow @nogc @property scope return
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
        @safe pure nothrow @nogc @property scope return
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
        const @safe pure nothrow @nogc @property scope return
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
    BigUIntView normalized() scope return
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
    inout(W)[] coefficients() inout @property scope return
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
        @safe pure @nogc nothrow
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
    static BigIntView fromHexString(C)(scope const(C)[] str)
        @trusted pure
        if (isSomeChar!C)
    {
        auto length = str.length / (W.sizeof * 2) + (str.length % (W.sizeof * 2) != 0);
        auto ret = BigIntView!(Unqual!W, endian)(new Unqual!W[length]);
        if (ret.fromHexStringImpl(str))
            return  cast(BigIntView) ret;
        version(D_Exceptions)
            throw hexStringException;
        else
            assert(0, hexStringErrorMsg);
    }

    static if (isMutable!W)
    /++
    +/
    bool fromHexStringImpl(C)(scope const(C)[] str)
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

        return unsigned.fromHexStringImpl(str);
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
        auto view = BigIntView!ubyte.fromHexString("-afbbfae3cd0aff2714a1de7022b0021d");
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

    static if (endian == TargetEndian)
    ///
    BigIntView!V opCast(T : BigIntView!V, V)() scope return
        if (V.sizeof <= W.sizeof)
    {
        return typeof(return)(this.unsigned.opCast!(BigUIntView!V), sign);
    }

    ///
    BigIntView!(const W, endian) lightConst()() scope return
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
struct DecimalView(W, WordEndian endian = TargetEndian, Exp = sizediff_t)
    if (isUnsigned!W)
{
    ///
    bool sign;
    ///
    Exp exponent;
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
        @safe pure @nogc nothrow
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
                            return !recentUnderscore;
                        }
                        else
                        {
                            return true;
                        }
                    }
                }

                continue;
            }
            static if (allowUnderscores)
            {
                if (recentUnderscore)
                    return false;
            }
            switch (d)
            {
                case DecimalExponentKey.dot:
                    key = DecimalExponentKey.dot;
                    if (_expect(dot, false))
                        break;
                    dot = true;
                    if (str.length)
                    {
                        static if (allowUnderscores)
                        {
                            recentUnderscore = true;
                        }
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
                        key = cast(DecimalExponentKey)d;
                        if (parse(str, exponent) && str.length == 0)
                        {
                            if (t != 1)
                                goto L;
                            goto M;
                        }
                        break;
                }
                static if (allowUnderscores)
                {
                    case '_' - '0':
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
    DecimalView!(const W, endian, Exp) lightConst()()
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
            Fp!64 load(Exp e)
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
            Fp!128 load(Exp e)
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
                Unsigned!Exp exp = exponent;
                exp = expSign ? -exp : exp;
                if (exp >= 5000)
                {
                    ret = expSign ? 0 : T.infinity;
                    goto R;
                }
                Exp index = exp & 0x1FF;
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
struct BinaryView(W, WordEndian endian = TargetEndian, Exp = int)
{
    ///
    bool sign;
    ///
    Exp exponent;
    ///
    BigUIntView!(W, endian) coefficient;

    ///
    DecimalView!(const W, endian, Exp) lightConst()()
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
