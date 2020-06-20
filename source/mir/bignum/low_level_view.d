/++
Low-level betterC utilities for big integer arithmetic libraries.

The module provides $(REF BigUIntAccumulator), $(REF BigUIntView), and $(LREF BigIntView).

Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.low_level_view;

import mir.checkedint;
import std.traits;

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

private template MaxFpPow5(T)
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
    BigIntView!(W, endian) signed()() @safe pure nothrow @nogc @property
    {
        return typeof(return)(this);
    }

    ///
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() const
        if (isFloatingPoint!T && isMutable!T)
    {
        import mir.bignum.fp;
        enum md = T.mant_dig;
        enum b = size_t.sizeof * 8;
        enum n = md / b + (md % b != 0);
        enum s = n * b;
        return opCast!(Fp!s, s - md, wordNormalized, nonZero).opCast!(T, true);
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_test)
    unittest
    {
        auto a = cast(double) BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a == 0xa.fbbfae3cd0bp+124);
        assert(cast(double) BigUIntView!size_t.init == 0);
        assert(cast(double) BigUIntView!size_t([0]) == 0);
    }

    ///
    T opCast(T : Fp!coefficientSize, size_t internalRoundLastBits = 0, bool wordNormalized = false, bool nonZero = false, size_t coefficientSize)() const
        if (internalRoundLastBits < size_t.sizeof * 8 && (size_t.sizeof >= W.sizeof || endian == TargetEndian))
    {
        static if (isMutable!W)
        {
            return lightConst.opCast!(T, internalRoundLastBits, wordNormalized, nonZero);
        }
        else
        static if (W.sizeof > size_t.sizeof)
        {
            integer.opCast!(BigUIntView!size_t).opCast!(internalRoundLastBits, false, nonZero);
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
    version(mir_test)
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

    static if (endian == TargetEndian)
    ///
    BigUIntView!V opCast(T : BigUIntView!V, V)()
        if (V.sizeof <= W.sizeof)
    {
        return typeof(return)(cast(V[])this.coefficients);
    }

    ///
    BigUIntView!(const W, endian) lightConst()()
        const @safe pure nothrow @nogc @property
    {
        return typeof(return)(coefficients);
    }
    ///ditto
    alias lightConst this;

    /++
    +/
    sizediff_t opCmp(BigUIntView!(const W, endian) rhs)
        const @safe pure nothrow @nogc
    {
        import mir.algorithm.iteration: cmp;
        if (auto d = this.coefficients.length - rhs.coefficients.length)
            return d;
        return cmp(this.lightConst.normalized.mostSignificantFirst, rhs.lightConst.normalized.mostSignificantFirst);
    }

    ///
    bool opEquals(BigUIntView!(const W, endian) rhs)
        const @safe pure nothrow @nogc
    {
        return this.coefficients == rhs.coefficients;
    }

    /++
    +/
    ref inout(W) mostSignificant() inout @property
    {
        static if (endian == WordEndian.big)
            return coefficients[0];
        else
            return coefficients[$ - 1];
    }

    /++
    +/
    ref inout(W) leastSignificant() inout @property
    {
        static if (endian == WordEndian.little)
            return coefficients[0];
        else
            return coefficients[$ - 1];
    }

    /++
    +/
    void popMostSignificant()
    {
        static if (endian == WordEndian.big)
            coefficients = coefficients[1 .. $];
        else
            coefficients = coefficients[0 .. $ - 1];
    }

    /++
    +/
    void popLeastSignificant()
    {
        static if (endian == WordEndian.little)
            coefficients = coefficients[1 .. $];
        else
            coefficients = coefficients[0 .. $ - 1];
    }

    /++
    +/
    BigUIntView topMostSignificantPart(size_t length)
    {
        static if (endian == WordEndian.big)
            return BigUIntView(coefficients[0 .. length]);
        else
            return BigUIntView(coefficients[$ - length .. $]);
    }

    /++
    +/
    BigUIntView topLeastSignificantPart(size_t length)
    {
        static if (endian == WordEndian.little)
            return BigUIntView(coefficients[0 .. length]);
        else
            return BigUIntView(coefficients[$ - length .. $]);
    }

    /++
    Shifts left using at most `size_t.sizeof * 8 - 1` bits
    +/
    void smallLeftShiftInPlace()(uint shift)
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
    version(mir_test)
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
    version(mir_test)
    @safe pure
    unittest
    {
        auto a = BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        a.smallRightShiftInPlace(4);
        assert(a == BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029"));
    }

    /++
    +/
    static BigUIntView fromHexString(scope const(char)[] str)
        @trusted pure
    {
        auto length = str.length / (W.sizeof * 2) + (str.length % (W.sizeof * 2) != 0);
        auto data = new Unqual!W[length];
        BigUIntView!(Unqual!W, endian)(data).fromHexStringImpl(str);
        return BigUIntView(cast(W[])data);
    }

    static if (isMutable!W)
    /++
    +/
    void fromHexStringImpl(scope const(char)[] str)
        @safe pure @nogc
    {
        pragma(inline, false);
        import mir.utility: _expect;
        if (_expect(str.length == 0 || str.length > coefficients.length * W.sizeof * 2, false))
        {
            version(D_Exceptions)
                throw hexStringException;
            else
                assert(0, hexStringErrorMsg);
        }
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
                default:
                    version(D_Exceptions)
                        throw hexStringException;
                    else
                        assert(0, hexStringErrorMsg);
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
    bool opOpAssign(string op)(BigUIntView!(const W, endian) rhs, bool overflow = false)
    @safe pure nothrow @nogc
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
    bool opOpAssign(string op)(BigIntView!(const W, endian) rhs, bool overflow = false)
    @safe pure nothrow @nogc
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
        @safe pure nothrow @nogc
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
        @safe pure nothrow @nogc
        if ((op == "+" || op == "-") && is(T == Signed!W))
    {
        return rhs >= 0 ?
            opOpAssign!op(cast(W)rhs):
            opOpAssign!(inverseSign!op)(cast(W)(-rhs));
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    Performs `W overflow = big *= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned value to multiply by
    Returns:
        unsigned overflow value
    +/
    W opOpAssign(string op : "*")(W rhs, W overflow = 0u)
        @safe pure nothrow @nogc
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

    static if (isMutable!W && W.sizeof == size_t.sizeof)
    /++
    Performs `W overflow = big *= fixed` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned fixed-length integer to multiply by
    Returns:
        unsigned fixed-length integer overflow value
    +/
    UInt!size
    opOpAssign(string op : "*", size_t size)(UInt!size rhs, UInt!size overflow = 0)
        @safe pure nothrow @nogc
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
    BigIntView!(W, endian) opUnary(string op : "-")()
    {
        return typeof(return)(this, true);
    }

    static if (isMutable!W && W.sizeof >= 4)
    /++
    +/
    void bitwiseNotInPlace()
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
    bool twoComplementInPlace()
    {
        assert(coefficients.length);
        bitwiseNotInPlace();
        return this.opOpAssign!"+"(W(1));
    }

    /++
    Returns: a slice of coefficients starting from the least significant.
    +/
    auto leastSignificantFirst()
        @safe pure nothrow @nogc @property
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
        const @safe pure nothrow @nogc @property
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
        @safe pure nothrow @nogc @property
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
        const @safe pure nothrow @nogc @property
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
    BigUIntView normalized()
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
    BigUIntView!(const W, endian) normalized() const
    {
        return lightConst.normalized;
    }

    /++
    +/
    bool bt()(size_t position)
    {
        import mir.ndslice.topology: bitwise;
        assert(position < coefficients.length * W.sizeof * 8);
        return leastSignificantFirst.bitwise[position];
    }

    /++
    +/
    size_t ctlz()() const @property
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
    size_t cttz()() const @property
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
    Returns: $(SUBREF exception, IonErrorCode)
    +/
    bool get(U)(scope out U value)
        @safe pure nothrow @nogc const
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
        @safe pure nothrow @nogc const
    {
        foreach_reverse(d; lightConst.leastSignificantFirst)
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
}

///
version(mir_test)
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
    inout(W)[] coefficients() inout @property
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

    ///
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() const
        if (isFloatingPoint!T)
    {
        auto ret = this.unsigned.opCast!(T, wordNormalized, nonZero);
        if (sign)
            ret = -ret;
        return ret;
    }


    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_test)
    unittest
    {
        auto a = cast(double) -BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a == -0xa.fbbfae3cd0bp+124);
    }

    /++
    +/
    T opCast(T : Fp!coefficientSize, size_t internalRoundLastBits = 0, bool wordNormalized = false, bool nonZero = false, size_t coefficientSize)() const
        if (internalRoundLastBits < size_t.sizeof * 8 && (size_t.sizeof >= W.sizeof || endian == TargetEndian))
    {
        auto ret = unsigned.opCast!(Fp!coefficientSize, internalRoundLastBits, wordNormalized, nonZero);
        ret.sign = sign;
        return ret;
    }

    static if (W.sizeof == size_t.sizeof && endian == TargetEndian)
    ///
    version(mir_test)
    @safe pure
    unittest
    {
        import mir.bignum.fixed: UInt;
        import mir.bignum.fp: Fp;

        auto fp = cast(Fp!128) -BigUIntView!size_t.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(fp.sign);
        assert(fp.exponent == 0);
        assert(fp.coefficient == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));
    }

    static if (endian == TargetEndian)
    ///
    BigIntView!V opCast(T : BigIntView!V, V)()
        if (V.sizeof <= W.sizeof)
    {
        return typeof(return)(this.unsigned.opCast!(BigUIntView!V), sign);
    }

    ///
    BigIntView!(const W, endian) lightConst()()
        const @safe pure nothrow @nogc @property
    {
        return typeof(return)(unsigned.lightConst, sign);
    }

    ///ditto
    alias lightConst this;

    /++
    +/
    sizediff_t opCmp(BigIntView!(const W, endian) rhs) 
        const @safe pure nothrow @nogc
    {
        import mir.algorithm.iteration: cmp;
        if (auto s = rhs.sign - this.sign)
        {
            return s;
        }
        sizediff_t d = this.unsigned.opCmp(rhs.unsigned);
        return sign ? -d : d;
    }

    ///
    bool opEquals(BigIntView!(const W, endian) rhs)
        const @safe pure nothrow @nogc
    {
        return this.sign == rhs.sign && this.unsigned == rhs.unsigned;
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
    bool opOpAssign(string op)(BigIntView!(const W, endian) rhs, bool overflow = false)
    @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        assert(rhs.coefficients.length > 0);
        import std.conv;
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
    bool opOpAssign(string op)(BigUIntView!(const W, endian) rhs, bool overflow = false)
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
    Performs `W overflow = big *= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned value to multiply by
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
version(mir_test)
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
    void mulPow2(size_t degree)
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
version(mir_test)
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

///
version(mir_test)
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

/// Computes `13 * 10^^60`
version(mir_test)
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

// /++
// +/
// BigUIntView!(W, endian) multiplyAddImpl(W, WordEndian endian)(
//     BigUIntView!(W, endian) result,
//     BigUIntView!(const W, endian) a,
//     BigUIntView!(const W, endian) b, out bool overflow)
// @safe pure nothrow @nogc
// {
//     import mir.utility: swap;
//     assert(a.length);
//     assert(b.length);
//     assert(result.length);
//     if (a.length > b.length)
//         swap(a, b);
//             assert(coefficients.length);
//     assert(b.length <= result.length);

//     auto rs = a.leastSignificantFirst;
//     do
//     {
//         auto ns = b.leastSignificantFirst;
//         do
//         {
//             import mir.utility: extMul;
//             bool overflowM;
//             bool overflowN;
//             auto ext = ns.front.extMul(rhs);
//             ns.front = ext.low.cop!"+"(overflow, overflowM)
//                 .cop!"+"(overflow, overflowN);
//             overflow = ext.high + overflowM;
//             ns.popFront;
//         }
//         while (ns.length);
//     }
//     while (rs.length);
//     return overflow;
// }

alias d1 = DecimalView!(uint, WordEndian.little, );
alias d2 = DecimalView!(uint, WordEndian.big);
alias d3 = DecimalView!(ulong, WordEndian.little, );
alias d4 = DecimalView!(ulong, WordEndian.big);
alias d5 = DecimalView!(uint, WordEndian.little, long);
alias d6 = DecimalView!(uint, WordEndian.big, long);
alias d7 = DecimalView!(ulong, WordEndian.little, long);
alias d8 = DecimalView!(ulong, WordEndian.big, long);

/++
+/
struct DecimalView(W, WordEndian endian = TargetEndian, Exp = int)
{
    ///
    bool sign;
    ///
    Exp exponent;
    ///
    BigUIntView!(W, endian) coefficient;

    alias toSingle = opCast!float;
    alias toDouble = opCast!double;
    alias toReal = opCast!real;

    ///
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() const
        if (isFloatingPoint!T && isMutable!T)
    {
        import mir.bignum.integer: BigInt;
        import mir.bignum.fixed: UInt;
        import mir.bignum.fp: Fp, extendedMul;
        import mir.bignum.internal.dec2flt_table;
        import mir.math.common: floor;
        import mir.math.ieee: ldexp, frexp, nextDown, nextUp;
        import mir.utility: _expect;

        auto coeff = coefficient.lightConst;
        T ret = 0;
        static if (!wordNormalized)
            coeff = coeff.normalized;
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
                    goto AlgoR;
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
                    auto p10coeff = UInt!128(cast(size_t[ulong.sizeof / size_t.sizeof * 2])cast(ulong[2])[h, l]);
                else
                    auto p10coeff = UInt!128(cast(size_t[ulong.sizeof / size_t.sizeof * 2])cast(ulong[2])[l, h]);
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
            }
        }

    AlgoR:
        if (exponent >= 0)
        {
            BigInt!256 x; // max value is 2^(2^14)-1
            if (x.copyFrom(coeff) || x.mulPow5(exponent)) // if overflow
                goto R;
            ret = ldexp(cast(T) x, cast(int) exponent);
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

            BigInt!256 x; // max value is 2^(2^14)-1
            if (x.copyFrom(coeff)) // if overflow
                break;
            auto y = BigInt!256(m); // max value is 2^(2^14)-1
            y.mulPow5(-exponent);
            auto shift = k - cast(int)exponent;
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
    R:
        if (sign)
            ret = -ret;
        return ret;
    }
}

///
version(mir_test)
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
        assert (cast(double)view == -1.584897405380044e-154);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == -1.584897405380044e-154L);

        view = DecimalView!Args(true, 293, BigUIntView!Args.fromHexString("36496F6C4ED38"));
        assert (cast(float)view == -float.infinity);
        assert (cast(double)view == -9.55024478104888e+307);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == -9.55024478104888e+307L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 1);
        assert (cast(double)view == 1);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1);

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
            assert (cast(real)view == 36893488147419103229.0L);

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
        assert (cast(double)view == 8713e-23);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 8713e-23L);

        view = DecimalView!Args(false, 300, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == 1e300);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e300L);

        view = DecimalView!Args(false, 245, BigUIntView!Args.fromHexString("B3A73CEB227"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == 123456789.34567e250);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 123456789.34567e250L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("88BF4748507FB9900ADB624CCFF8D78897DC900FB0460327D4D86D327219"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == 943794359898089732078308743689303290943794359843568973207830874368930329.0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 943794359898089732078308743689303290943794359843568973207830874368930329.0L);

        view = DecimalView!Args(false, -324, BigUIntView!Args.fromHexString("5"));
        assert (cast(float)view == 0);
        assert (cast(double)view == double.min_normal * double.epsilon);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 5e-324L);

        view = DecimalView!Args(false, -324, BigUIntView!Args.fromHexString("5B"));
        assert (cast(float)view == 0);
        assert (cast(double)view == double.min_normal * double.epsilon * 18);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 91e-324L);

        view = DecimalView!Args(false, -322, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == double.min_normal * double.epsilon * 20);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e-322L);

        view = DecimalView!Args(false, -320, BigUIntView!Args.fromHexString("CA1CCB"));
        assert (cast(float)view == 0);
        assert (cast(double)view == double.min_normal * double.epsilon * 26809479897);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 13245643e-320L);

        view = DecimalView!Args(false, -319, BigUIntView!Args.fromHexString("33CE7943FB"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 2.22507385851e-308);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 2.22507385851e-308L);

        view = DecimalView!Args(false, -309, BigUIntView!Args.fromHexString("15"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0x0.f19c2629ccf53p-1022);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 2.1e-308L);

        view = DecimalView!Args(false, -340, BigUIntView!Args.fromHexString("AF87023B9BF0EE"));
        assert (cast(float)view == 0);
        assert (cast(double)view == double.min_normal * double.epsilon);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 4.9406564584124654e-324L);

        view = DecimalView!Args(false, 400, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e400L);

        view = DecimalView!Args(false, 309, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e309L);

        view = DecimalView!Args(false, 308, BigUIntView!Args.fromHexString("2"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 2e308L);

        view = DecimalView!Args(false, 308, BigUIntView!Args.fromHexString("2"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 2e308L);

        view = DecimalView!Args(false, 295, BigUIntView!Args.fromHexString("1059949B7090"));
        assert (cast(float)view == float.infinity);
        assert (cast(double)view == double.infinity);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1.7976931348624e308L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("0"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0);

        view = DecimalView!Args(false, 0, BigUIntView!Args.init);
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0);

        view = DecimalView!Args(false, -325, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e-325L);

        view = DecimalView!Args(false, -326, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e-326L);

        view = DecimalView!Args(false, -500, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e-500L);

        view = DecimalView!Args(false, -1000, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e-1000L);

        view = DecimalView!Args(false, -4999, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0);

        view = DecimalView!Args(false, -10000, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0);

        view = DecimalView!Args(false, -4969, BigUIntView!Args.fromHexString("329659A941466C6B"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == real.min_normal * real.epsilon);

        view = DecimalView!Args(false, -15, BigUIntView!Args.fromHexString("525DB0200FFAB"));
        assert (cast(float)view == 1.448997445238699f);
        assert (cast(double)view == 0x1.72f17f1f49aadp0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1.448997445238699L);

        view = DecimalView!Args(false, -15, BigUIntView!Args.fromHexString("525DB0200FFAB"));
        assert (cast(float)view == 1.448997445238699f);
        assert (cast(double)view == 0x1.72f17f1f49aadp0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1.448997445238699L);

        view = DecimalView!Args(false, -325, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e-325L);

        view = DecimalView!Args(false, -326, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 0);
        assert (cast(double)view == 0);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1e-326L);

        view = DecimalView!Args(false, 0, BigUIntView!Args.fromHexString("1"));
        assert (cast(float)view == 1);
        assert (cast(double)view == 1);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 1);

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

        view = DecimalView!Args(false, -7, BigUIntView!Args.fromHexString("98967F"));
        assert (cast(float)view == 0.9999999f);
        assert (cast(double)view == 0.9999999);
        static if (real.mant_dig >= 64)
            assert (cast(real)view == 0.9999999L);
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
}
