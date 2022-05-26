/++
Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.integer;

import mir.bitop;
import mir.serde: serdeProxy, serdeScoped;
import mir.utility;
import std.traits;

/++
Stack-allocated big signed integer.
Params:
    maxSize64 = count of 64bit words in coefficient
+/
@serdeScoped @serdeProxy!(const(char)[])
struct BigInt(uint maxSize64)
    if (maxSize64 && maxSize64 <= ushort.max)
{
    import mir.bignum.low_level_view;
    import mir.bignum.fixed;

    ///
    bool sign;
    ///
    uint length;
    ///
    size_t[ulong.sizeof / size_t.sizeof * maxSize64] data = void;

    ///
    this(uint size)(UInt!size fixedInt)
    {
        this(fixedInt.data);
    }

    ///
    this(uint N)(size_t[N] data)
        if (N <= this.data.length)
    {
        sign = false;
        version(LittleEndian)
            this.data[0 .. N] = data;
        else
            this.data[$ - N .. $] = data;
        length = data.length;
        normalize;
    }

    ///
    this(ulong data)
    {
        sign = false;
        static if (size_t.sizeof == ulong.sizeof)
        {
            length = 1;
            view.leastSignificantFirst[0] = data;
        }
        else
        {
            length = 2;
            auto d = view.leastSignificantFirst;
            d[0] = cast(uint) data;
            d[1] = cast(uint) (data >> 32);
        }
        normalize;
    }

    ///
    this()(scope const(char)[] str) @safe pure @nogc
        // if (isSomeChar!C)
    {
        if (fromStringImpl(str))
            return;
        static if (__traits(compiles, () @nogc { throw new Exception("Can't parse BigInt."); }))
        {
            import mir.exception: MirException;
            throw new MirException("Can't parse BigInt!" ~ maxSize64.stringof ~ " from string `", str , "`.");
        }
        else
        {
            static immutable exception = new Exception("Can't parse BigInt!" ~ maxSize64.stringof ~ ".");
            throw exception;
        }
    }

    ///
    ref opAssign(ulong data) return
    {
        static if (size_t.sizeof == ulong.sizeof)
        {
            length = 1;
            view.leastSignificantFirst[0] = data;
        }
        else
        {
            length = 2;
            auto d = view.leastSignificantFirst;
            d[0] = cast(uint) data;
            d[1] = cast(uint) (data >> 32);
        }
        normalize;
        return this;
    }

    static if (maxSize64 == 3)
    ///
    version(mir_bignum_test) @safe pure @nogc unittest
    {
        import mir.math.constant: PI;
        BigInt!4 integer = "-34010447314490204552169750449563978034784726557588085989975288830070948234680"; // constructor
        assert(integer.sign);
        integer.sign = false;
        assert(integer == BigInt!4.fromHexString("4b313b23aa560e1b0985f89cbe6df5460860e39a64ba92b4abdd3ee77e4e05b8"));
    }

    ///
    ref opAssign(uint rhsMaxSize64)(auto ref scope const BigInt!rhsMaxSize64 rhs) return
        if (rhsMaxSize64 < maxSize64)
    {
        this.sign = rhs.sign;
        this.length = rhs.length;
        version(LittleEndian)
        {
            data[0 .. length] = rhs.data[0 .. length];
        }
        else
        {
            data[$ - length .. $] = rhs.data[$ - length .. $];
        }
        return this;
    }

    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients.
    +/
    bool fromStringImpl(C)(scope const(C)[] str)
        scope @trusted pure @nogc nothrow
        if (isSomeChar!C)
    {
        auto work = BigIntView!size_t(data[]); 
        if (work.fromStringImpl(str))
        {
            length = cast(uint) work.coefficients.length;
            sign = work.sign;
            return true;
        }
        return false;
    }

    ///
    BigInt copy() @property
    {
        BigInt ret;
        ret.sign = sign;
        ret.length = length;
        ret.data = data;
        return ret;
    }

    ///
    bool opEquals()(auto ref const BigInt rhs)
        const @safe pure nothrow @nogc
    {
        return view == rhs.view;
    }

    ///
    bool opEquals()(size_t rhs, bool rhsSign = false)
        const @safe pure nothrow @nogc
    {
        return rhs == 0 && length == 0 || length == 1 && sign == rhsSign && view.unsigned.leastSignificant == rhs;
    }

    ///
    bool opEquals()(sizediff_t rhs)
        const @safe pure nothrow @nogc
    {
        auto sign = rhs < 0;
        return opEquals(sign ? ulong(-rhs) : ulong(rhs), sign);
    }

    /++
    +/
    auto opCmp()(auto ref const BigInt rhs) 
        const @safe pure nothrow @nogc
    {
        return view.opCmp(rhs.view);
    }

    ///
    BigIntView!size_t view()() @property
    {
        version (LittleEndian)
            return typeof(return)(data[0 .. length], sign);
        else
            return typeof(return)(data[$ - length .. $], sign);
    }

    ///
    BigIntView!(const size_t) view()() const @property
    {
        version (LittleEndian)
            return typeof(return)(data[0 .. length], sign);
        else
            return typeof(return)(data[$ - length .. $], sign);
    }

    ///
    void normalize()()
    {
        auto norm = view.normalized;
        this.length = cast(uint) norm.unsigned.coefficients.length;
        this.sign = norm.sign;
    }

    /++
    +/
    void putCoefficient(size_t value)
    {
        assert(length < data.length);
        version (LittleEndian)
            data[length++] = value;
        else
            data[$ - ++length] = value;
    }

    /++
    Performs `size_t overflow = (big += overflow) *= scalar` operatrion.
    Params:
        rhs = unsigned value to multiply by
        overflow = initial overflow value
    Returns:
        unsigned overflow value
    +/
    size_t opOpAssign(string op : "*")(size_t rhs, size_t overflow = 0u)
        @safe pure nothrow @nogc
    {
        if (length == 0)
            goto L;
        overflow = view.unsigned.opOpAssign!op(rhs, overflow);
        if (overflow && length < data.length)
        {
        L:
            putCoefficient(overflow);
            overflow = 0;
        }
        return overflow;
    }

    /++
    Performs `uint remainder = (overflow$big) /= scalar` operatrion, where `$` denotes big-endian concatenation.
    Precondition: `overflow < rhs`
    Params:
        rhs = unsigned value to devide by
        overflow = initial unsigned overflow
    Returns:
        unsigned remainder value (evaluated overflow)
    +/
    uint opOpAssign(string op : "/")(uint rhs, uint overflow = 0)
        @safe pure nothrow @nogc
    {
        assert(overflow < rhs);
        if (length)
            return view.unsigned.opOpAssign!op(rhs, overflow);
        return overflow;
    }

    /++
    Performs `size_t overflow = (big += overflow) *= fixed` operatrion.
    Params:
        rhs = unsigned value to multiply by
        overflow = initial overflow value
    Returns:
        unsigned overflow value
    +/
    UInt!size opOpAssign(string op : "*", size_t size)(UInt!size rhs, UInt!size overflow = 0)
        @safe pure nothrow @nogc
    {
        if (length == 0)
            goto L;
        overflow = view.unsigned.opOpAssign!op(rhs, overflow);
        if (overflow && length < data.length)
        {
        L:
            static if (size <= 64)
            {
                auto o = cast(ulong)overflow;
                static if (size_t.sizeof == ulong.sizeof)
                {
                    putCoefficient(o);
                    overflow = UInt!size.init;
                }
                else
                {
                    putCoefficient(cast(uint)o);
                    o >>= 32;
                    if (length < data.length)
                    {
                        putCoefficient(cast(uint)o);
                        o = 0;
                    }
                    overflow = UInt!size(o);
                }
            }
            else
            {
                do
                {
                    putCoefficient(cast(size_t)overflow);
                    overflow >>= size_t.sizeof * 8;
                }
                while(overflow && length < data.length);
            }
        }
        return overflow;
    }

    /++
    Performs `big /= rhs` operation.
    Params:
        rhs = unsigned value to divide by
    Returns:
        quotient from division
    +/
    ref opOpAssign(string op : "/", size_t size)(UInt!size rhs)
        @safe pure nothrow @nogc return
    {
        import mir.bignum.low_level_view : divm, BigUIntView;

        enum m = ((data.length * (size_t.sizeof * 8)) / (uint.sizeof * 8));

        if (length)
        {
            uint[m + 1] _div = void;
            // shouldn't be unaligned here -- maybe a possibility though
            _div[0 .. $ - 1] = cast(uint[m])data;
            _div[$ - 1] = 0;

            BigUIntView!uint dividend = BigUIntView!uint(_div);
            BigUIntView!uint divisor = cast(BigUIntView!uint)rhs.view;
            BigUIntView!uint quotient = cast(BigUIntView!uint)view.unsigned;
            data = 0;
            divm(dividend, divisor, quotient);
            length = cast(uint)view.normalized.coefficients.length;
        }
        return this;
    }

    /// ditto
    ref opOpAssign(string op : "/")(ulong rhs)
        @safe pure nothrow @nogc return
    {
        if (length)
        {
            return this.opOpAssign!"/"(UInt!64(rhs));
        }
        return this;
    }

    /// ditto
    ref opOpAssign(string op : "/")(long rhs)
        @safe pure nothrow @nogc return
    {
        if (length)
        {
            ulong div = rhs < 0 ? rhs * -1 : rhs;
            auto result = this.opOpAssign!"/"(div);
            // If this is a negative number, then we should keep the negative sign if rhs > 0.
            // If it is not, then we should check if we're dividing by a negative number (rhs < 0),
            // and apply the negative sign as such.
            this.sign = result.sign ? rhs > 0 : rhs < 0; 
        }
        return this;
    }

    /// ditto
    ref opOpAssign(string op : "/", size_t rhsMaxSize64)(const ref BigInt!rhsMaxSize64 rhs)
        @safe pure nothrow @nogc return
    {
        import mir.bignum.low_level_view : divm, BigUIntView;

        enum m = (data.length * (size_t.sizeof * 8)), n = (rhsMaxSize64 / (uint.sizeof * 8));

        if (length)
        {
            UInt!(m + (size_t.sizeof * 8)) _div;
            // shouldn't be unaligned here -- maybe a possibility though
            _div.data[0 .. $ - 1] = data;

            BigUIntView!uint dividend = cast(BigUIntView!uint)_div.view;
            BigUIntView!uint divisor = cast(BigUIntView!uint)rhs.view.unsigned;
            BigUIntView!uint quotient = cast(BigUIntView!uint)view.unsigned;
            data = 0;
            divm(dividend, divisor, quotient);
            length = cast(uint)view.normalized.coefficients.length;

            // If this is a negative number, then we should keep the negative sign if we are not negative.
            // If we are not negative, then we should check if we're dividing by a negative number (,
            // and apply the negative sign as such.
            this.sign = rhs.sign ? this.sign != rhs.sign : this.sign;
        }
        return this;
    }

    /++
    Performs `big %= rhs` operation.
    Params:
        rhs = unsigned value to divide by
    Returns:
        remainder from division
    +/
    ref opOpAssign(string op : "%", size_t size)(UInt!size rhs)
        @safe pure nothrow @nogc return
    {
        import mir.bignum.low_level_view : divm, BigUIntView;

        enum m = ((data.length * (size_t.sizeof * 8)) / (uint.sizeof * 8));

        if (length)
        {
            uint[m+1] _div = void;
            // We don't necessarily care about the quotient,
            // so we should avoid an expensive 0-initialization here.
            uint[m] q = void;
            // shouldn't be unaligned here -- maybe a possibility though
            _div[0 .. $ - 1] = cast(uint[m])data;
            _div[$ - 1] = 0;

            BigUIntView!uint dividend = BigUIntView!uint(_div);
            BigUIntView!uint divisor = cast(BigUIntView!uint)rhs.view;
            BigUIntView!uint quotient = BigUIntView!uint(q); 
            divm(dividend, divisor, quotient);

            data = 0;
            // FIXME: ugly ugly cast
            (cast(uint[m])data)[0 .. dividend.coefficients.length] = dividend.coefficients;
            auto normLen = cast(uint)dividend.normalized.coefficients.length;

            static if (uint.sizeof != size_t.sizeof) {
                // Round up where size_t is not as large as uint
                normLen += (normLen % (size_t.sizeof / uint.sizeof));
            } 
            length = (normLen * (uint.sizeof * 8)) / (size_t.sizeof * 8);
        }
        return this;
    }

    /// ditto
    ref opOpAssign(string op : "%")(ulong rhs)
        @safe pure nothrow @nogc return
    {
        if (length)
        {
            return this.opOpAssign!"%"(UInt!64(rhs));
        }
        return this;
    }

    /// ditto
    ref opOpAssign(string op : "%")(long rhs)
        @safe pure nothrow @nogc return
    {
        if (length)
        {
            ulong div = rhs < 0 ? rhs * -1 : rhs;
            this.opOpAssign!"%"(div);

            // Add back if it is necessary (XXX: is this even correct??) 
            if ((this.sign && rhs > 0) || (!this.sign && rhs < 0))
            {
                this.opOpAssign!("+")(BigIntView!(const size_t)(UInt!64(div).view, rhs < 0));
            }
        }
        return this;
    }

    /// ditto
    ref opOpAssign(string op : "%", size_t rhsMaxSize64)(ref const BigInt!rhsMaxSize64 rhs)
    {
        import mir.bignum.low_level_view : divm, BigUIntView;

        enum m = ((data.length * (size_t.sizeof * 8)) / (uint.sizeof * 8));

        if (length)
        {
            uint[m+1] _div = void;
            // We don't necessarily care about the quotient,
            // so we should avoid an expensive 0-initialization here.
            uint[m] q = void;
            // shouldn't be unaligned here -- maybe a possibility though
            _div[0 .. $ - 1] = cast(uint[m])data;
            _div[$ - 1] = 0;

            BigUIntView!uint dividend = BigUIntView!uint(_div);
            BigUIntView!uint divisor = cast(BigUIntView!uint)rhs.view.unsigned;
            BigUIntView!uint quotient = BigUIntView!uint(q); 
            divm(dividend, divisor, quotient);

            data = 0;
            (cast(uint[m])data)[0 .. dividend.coefficients.length] = dividend.coefficients;

            // Round to even upwards
            auto normLen = cast(uint)dividend.normalized.coefficients.length;

            static if (uint.sizeof != size_t.sizeof) {
                // Round up where size_t is not as large as uint
                normLen += (normLen % (size_t.sizeof / uint.sizeof));
            } 
            length = (normLen * (uint.sizeof * 8)) / (size_t.sizeof * 8);
            // Add back if it is necessary (XXX: is this even correct??) 
            if ((this.sign && !rhs.sign) || (!this.sign && rhs.sign))
            {
                this.opOpAssign!("+")(rhs);
            }
        }

        return this;
    }

    /++
    Performs `size_t overflow = big *= fixed` operatrion.
    Params:
        rhs = unsigned value to multiply by
    Returns:
        overflow
    +/
    bool opOpAssign(string op, size_t rhsMaxSize64)(ref const BigInt!rhsMaxSize64 rhs)
        @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        return opOpAssign!op(rhs.view);
    }

    /// ditto
    bool opOpAssign(string op)(BigIntView!(const size_t) rhs)
        @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        sizediff_t diff = length - rhs.coefficients.length;
        if (diff < 0)
        {
            auto oldLength = length;
            length = cast(int)rhs.coefficients.length;
            view.unsigned.leastSignificantFirst[oldLength .. $] = 0;
        }
        else
        if (rhs.coefficients.length == 0)
            return false;
        auto thisView = view;
        auto overflow = thisView.opOpAssign!op(rhs);
        this.sign = thisView.sign;
        if (overflow)
        {
            if (length < data.length)
            {
                putCoefficient(overflow);
                overflow = false;
            }
        }
        else
        {
            normalize;
        }
        return overflow;
    }
    /++
    +/
    static BigInt fromHexString(bool allowUnderscores = false)(scope const(char)[] str)
        @trusted pure
    {
        BigInt ret;
        if (ret.fromHexStringImpl!(char, allowUnderscores)(str))
            return ret;
        version(D_Exceptions)
            throw hexStringException;
        else
            assert(0, hexStringErrorMsg);
    }

    /++
    +/
    bool fromHexStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        auto work = BigIntView!size_t(data);
        auto ret = work.fromHexStringImpl!(C, allowUnderscores)(str);
        if (ret)
        {
            length = cast(uint)work.unsigned.coefficients.length;
            sign = work.sign;
        }
        return ret;
    }

    /++
    +/
    static BigInt fromBinaryString(bool allowUnderscores = false)(scope const(char)[] str)
        @trusted pure
    {
        BigInt ret;
        if (ret.fromBinaryStringImpl!(char, allowUnderscores)(str))
            return ret;
        version(D_Exceptions)
            throw binaryStringException;
        else
            assert(0, binaryStringErrorMsg);
    }

    static if (maxSize64 == 3)
    ///
    version(mir_bignum_test) @safe pure @nogc unittest
    {
        BigInt!4 integer = "-34010447314490204552169750449563978034784726557588085989975288830070948234680"; // constructor
        assert(integer == BigInt!4.fromBinaryString("-100101100110001001110110010001110101010010101100000111000011011000010011000010111111000100111001011111001101101111101010100011000001000011000001110001110011010011001001011101010010010101101001010101111011101001111101110011101111110010011100000010110111000"));
    }

    /++
    +/
    bool fromBinaryStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        auto work = BigIntView!size_t(data);
        auto ret = work.fromBinaryStringImpl!(C, allowUnderscores)(str);
        if (ret)
        {
            length = cast(uint)work.unsigned.coefficients.length;
            sign = work.sign;
        }
        return ret;
    }

    ///
    bool mulPow5(size_t degree)
    {
        // assert(approxCanMulPow5(degree));
        if (length == 0)
            return false;
        enum n = MaxWordPow5!size_t;
        enum wordInit = size_t(5) ^^ n;
        size_t word = wordInit;
        bool of;
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
                of = length >= data.length;
                if (!of)
                    putCoefficient(overflow);
            }
        }
        return of;
    }

    ///
    ref BigInt opOpAssign(string op)(size_t shift)
        @safe pure nothrow @nogc return
        if (op == "<<" || op == ">>")
    {
        auto index = shift / (size_t.sizeof * 8);
        auto bs = shift % (size_t.sizeof * 8);
        auto ss = size_t.sizeof * 8 - bs;
        static if (op == ">>")
        {
            if (index >= length)
            {
                length = 0;
                return this;
            }
            auto d = view.leastSignificantFirst;
            if (bs)
            {
                foreach (j; 0 .. d.length - (index + 1))
                {
                    d[j] = (d[j + index] >>> bs) | (d[j + (index + 1)] << ss);
                }
            }
            else
            {
                foreach (j; 0 .. d.length - (index + 1))
                {
                    d[j] = d[j + index];
                }
            }
            auto most = d[$ - (index + 1)] = d.back >>> bs;
            length -= index + (most == 0);
        }
        else
        {
            if (index >= data.length || length == 0)
            {
                length = 0;
                return this;
            }

            if (bs)
            {
                auto most = view.unsigned.mostSignificant >> ss;
                length += index;
                if (length < data.length)
                {
                    if (most)
                    {
                        length++;
                        view.unsigned.mostSignificant = most;
                        length--;
                    }
                }
                else
                {
                    length = data.length;
                }

                auto d = view.leastSignificantFirst;
                foreach_reverse (j; index + 1 .. length)
                {
                    d[j] = (d[j - index] << bs) | (d[j - (index + 1)] >> ss);
                }
                d[index] = d.front << bs;
                if (length < data.length)
                    length += most != 0;
            }
            else
            {
                length = cast(uint) min(length + index, cast(uint)data.length);
                auto d = view.leastSignificantFirst;
                foreach_reverse (j; index .. length)
                {
                    d[j] = d[j - index];
                }
            }
            view.leastSignificantFirst[0 .. index] = 0;
        }
        return this;
    }

    ///
    T opCast(T, bool wordNormalized = false, bool nonZero = false)() const
        if (isFloatingPoint!T && isMutable!T)
    {
        return view.opCast!(T, wordNormalized, nonZero);
    }

    ///
    T opCast(T, bool nonZero = false)() const
        if (is(T == long) || is(T == int))
    {
        return this.view.opCast!(T, nonZero);
    }

    /++
    Returns: overflow flag
    +/
    bool copyFrom(W, WordEndian endian)(BigIntView!(const W, endian) view)
    {
        static if (W.sizeof > size_t.sizeof && endian == TargetEndian)
        {
            return this.copyFrom(cast(BigIntView!(const size_t))view);
        }
        else
        {
            this.sign = view.sign;
            auto lhs = BigUIntView!W(cast(W[])data);
            auto rhs = view;
            auto overflow = lhs.coefficients.length < rhs.coefficients.length;
            auto n = overflow ? lhs.coefficients.length : rhs.coefficients.length;
            lhs.leastSignificantFirst[0 .. n] = rhs.leastSignificantFirst[0 .. n];
            this.length = cast(uint)(n / (size_t.sizeof / W.sizeof));
            if (auto tail = n % (size_t.sizeof / W.sizeof))
            {
                this.length++;
                auto shift = ((size_t.sizeof / W.sizeof) - tail) * (W.sizeof * 8);
                auto value = this.view.unsigned.mostSignificant;
                value <<= shift;
                value >>= shift;
                this.view.unsigned.mostSignificant = value;
            }
            return overflow;
        }
    }

    /// ditto
    bool copyFrom(W, WordEndian endian)(BigUIntView!(const W, endian) view)
    {
        return this.copyFrom(BigIntView!(const W, endian)(view));
    }

    ///
    immutable(C)[] toString(C = char)() const @safe pure nothrow
        if(isSomeChar!C && isMutable!C)
    {
        C[ceilLog10Exp2(data.length * (size_t.sizeof * 8)) + 1] buffer = void;
        BigInt copy = this;
        auto len = copy.view.unsigned.toStringImpl(buffer);
        if (sign)
            buffer[$ - ++len] = '-';
        return buffer[$ - len .. $].idup;
    }

    static if (maxSize64 == 3)
    ///
    version(mir_bignum_test) @safe pure unittest
    {
        auto str = "-34010447314490204552169750449563978034784726557588085989975288830070948234680";
        auto integer = BigInt!4(str);
        assert(integer.toString == str);

        integer = BigInt!4.init;
        assert(integer.toString == "0");
    }

    ///
    void toString(C = char, W)(scope ref W w) const
        if(isSomeChar!C && isMutable!C)
    {
        C[ceilLog10Exp2(data.length * (size_t.sizeof * 8)) + 1] buffer = void;
        BigInt copy = this;
        auto len = copy.view.unsigned.toStringImpl(buffer);
        if (sign)
            buffer[$ - ++len] = '-';
        w.put(buffer[$ - len .. $]);
    }

    static if (maxSize64 == 3)
    /// Check @nogc toString impl
    version(mir_bignum_test) @safe pure @nogc unittest
    {
        import mir.format: stringBuf;
        auto str = "-34010447314490204552169750449563978034784726557588085989975288830070948234680";
        auto integer = BigInt!4(str);
        stringBuf buffer;
        buffer << integer;
        assert(buffer.data == str);
    }
}


///
version(mir_bignum_test)
unittest
{
    import mir.bignum.fixed;
    import mir.bignum.low_level_view;

    {
        auto a = BigInt!4.fromHexString("c39b18a9f06fd8e962d99935cea0707f79a222050aaeaaaed17feb7aa76999d7");
        auto b = UInt!128.fromHexString("f79a222050aaeaaa417fa25a2ac93291");

        assert((a /= b) == BigInt!4.fromHexString("ca3d7e25aebe687b7cc1b250b44690fb"));
        a = BigInt!4.fromHexString("c39b18a9f06fd8e962d99935cea0707f79a222050aaeaaaed17feb7aa76999d7");
        assert((a %= b) == BigInt!4.fromHexString("bf4c87424431d21563f23b1fc00d75ac"));
    }

    {
        auto a = BigInt!4.fromHexString("7fff000080000000000000000000");
        auto b = UInt!128.fromHexString("80000000000000000001"); 

        assert((a /= b) == BigInt!4.fromHexString("fffe0000"));
        a = BigInt!4.fromHexString("7fff000080000000000000000000");
        assert((a %= b) == BigInt!4.fromHexString("7fffffffffff00020000"));
    }

    {
        auto a = BigInt!16.fromHexString("76d053cdcc87ec8c9455c375d6a08c799fad73cf07415e70af5dfacaff4bd306647a7cceb98839cce89ae65900938821564fd2af3c9d881c172264bb17e3530ce79b938d5eb7ffec558be43ab5b684978417c5053fb8df63fc65c9efd8b2e86469c53259509eb597f81647930f24ef05a79bfecf04e5ec52414c6a3f7481d533");
        auto b = UInt!128.fromHexString("9c5c1aa6ad7ad18065a3a74598e27bee");

        assert((a /= b) == BigInt!16.fromHexString("c2871f2b07522bda1e63de12850d2208bb242c716b5739d6744ee1d9c937b8d765d3742e18785d08c2405e5c83f3c875d5726d09dfaee29e813675a4f91bfee01e8cbbbca9588325d54cf2a625faffde4d8709e0517f786f609d8ce6997e0e71d2f976ae169b0c4be7a7dba3135af96c"));
        a = BigInt!16.fromHexString("76d053cdcc87ec8c9455c375d6a08c799fad73cf07415e70af5dfacaff4bd306647a7cceb98839cce89ae65900938821564fd2af3c9d881c172264bb17e3530ce79b938d5eb7ffec558be43ab5b684978417c5053fb8df63fc65c9efd8b2e86469c53259509eb597f81647930f24ef05a79bfecf04e5ec52414c6a3f7481d533");
        assert((a %= b) == BigInt!16.fromHexString("85d81587a8b62af1874315d26ebf0ecb"));
    }

    {
        auto a = BigInt!4.fromHexString("DEADBEEF");
        auto b = UInt!256.fromHexString("18aeff9fa4aace484a9f8f9002cdf38fa6e53fc0f6c035051dc86931c1c08316");

        assert((a /= b) == 0);
        a = BigInt!4.fromHexString("DEADBEEF");
        assert((a %= b) == 0xDEADBEEF);
    }

    {
        auto a = BigInt!4.fromHexString("DEADBEEF");
        assert((a /= -0xDEADL) == -65536);
        a = BigInt!4.fromHexString("DEADBEEF"); 
        assert((a %= 0xDEADL) == 48879);
        a = BigInt!4.fromHexString("DEADBEEF"); 
        assert((a %= -0xDEADL) == -8126);
        a = BigInt!4.fromHexString("-DEADBEEF");
        assert((a %= 0xDEADL) == 8126);
        a = BigInt!4.fromHexString("-DEADBEEF");
        assert((a %= -0xDEADL) == -48879);
    }

    {
        // Test whether or not our sign flipping is actually correct in division
        auto a = BigInt!4.fromHexString("DEADBEEF");
        auto b = BigInt!4.fromHexString("DEAD");
        assert((a /= b) == 65536);
        a = BigInt!4.fromHexString("-DEADBEEF");
        b = BigInt!4.fromHexString("DEAD");
        assert((a /= b) == -65536);
        a = BigInt!4.fromHexString("DEADBEEF");
        b = BigInt!4.fromHexString("-DEAD");
        assert((a /= b) == -65536);
        a = BigInt!4.fromHexString("-DEADBEEF");
        b = BigInt!4.fromHexString("-DEAD");
        assert((a /= b) == 65536);

        // Test whether or not our sign flipping is actually correct in rem
        a = BigInt!4.fromHexString("DEADBEEF");
        b = BigInt!4.fromHexString("DEAD");
        assert((a %= b) == 48879);
        a = BigInt!4.fromHexString("DEADBEEF");
        b = BigInt!4.fromHexString("-DEAD");
        assert((a %= b) == -8126);
        a = BigInt!4.fromHexString("-DEADBEEF");
        b = BigInt!4.fromHexString("DEAD");
        assert((a %= b) == 8126);
        a = BigInt!4.fromHexString("-DEADBEEF");
        b = BigInt!4.fromHexString("-DEAD");
        assert((a %= b) == -48879);
    }
    
}

///
version(mir_bignum_test)
unittest
{
    import mir.bignum.fixed;
    import mir.bignum.low_level_view;

    auto a = BigInt!4.fromHexString("4b313b23aa560e1b0985f89cbe6df5460860e39a64ba92b4abdd3ee77e4e05b8");
    auto b = BigInt!4.fromHexString("c39b18a9f06fd8e962d99935cea0707f79a222050aaeaaaed17feb7aa76999d7");
    auto c = BigInt!4.fromHexString("7869dd864619cace5953a09910327b3971413e6aa5f417fa25a2ac93291b941f");
    c.sign = true;
    assert(a != b);
    assert(a < b);
    a -= b;
    assert(a.sign);
    assert(a == c);
    a -= a;
    assert(!a.sign);
    assert(!a.length);

    auto d = BigInt!4.fromHexString("0de1a911c6dc8f90a7169a148e65d22cf34f6a8254ae26362b064f26ac44218a");
    assert((b *= 0x7869dd86) == 0x5c019770);
    assert(b == d);

    d = BigInt!4.fromHexString("856eeb23e68cc73f2a517448862cdc97e83f9dfa23768296724bf00fda7df32a");
    auto o = b *= UInt!128.fromHexString("f79a222050aaeaaa417fa25a2ac93291");
    assert(o == UInt!128.fromHexString("d6d15b99499b73e68c3331eb0f7bf16"));
    assert(b == d);

    d = BigInt!4.fromHexString("d"); // initial value
    d.mulPow5(60);
    c = BigInt!4.fromHexString("81704fcef32d3bd8117effd5c4389285b05d");
    assert(d == c);

    d >>= 80;
    c = BigInt!4.fromHexString("81704fcef32d3bd8");
    assert(d == c);

    c = BigInt!4.fromHexString("c39b18a9f06fd8e962d99935cea0707f79a222050aaeaaaed17feb7aa76999d7");
    d = BigInt!4.fromHexString("9935cea0707f79a222050aaeaaaed17feb7aa76999d700000000000000000000");
    c <<= 80;
    assert(d == c);
    c >>= 80;
    c <<= 84;
    d <<= 4;
    assert(d == c);
    assert(c != b);
    b.sign = true;
    assert(!c.copyFrom(b.view));
    assert(c == b);
    b >>= 18;
    auto bView = cast(BigIntView!ushort)b.view;
    assert(!c.copyFrom(bView.topLeastSignificantPart(bView.unsigned.coefficients.length - 1)));
    assert(c == b);
}

version(mir_bignum_test)
@safe pure @nogc unittest
{
    BigInt!4 i = "-0";
    assert(i.view.coefficients.length == 0);
    assert(cast(long) i == 0);
}
