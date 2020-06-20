/++
Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.integer;

import std.traits;
import mir.bitop;
import mir.utility;

/++
Stack-allocated big signed integer.
Params:
    maxSize64 = count of 64bit words in coefficient
+/
struct BigInt(size_t maxSize64)
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

    @disable this(this);

    ///
    this(size_t size)(UInt!size fixedInt)
    {
        this(fixedInt.data);
    }

    ///
    this(size_t N)(size_t[N] data)
        if (N <= this.data.length)
    {
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
        auto d = view.leastSignificantFirst;
        static if (size_t.sizeof == ulong.sizeof)
        {
            d.front = data;
            length = 1;
        }
        else
        {
            d.front = cast(uint) data;
            d[1] = cast(uint) (data >> 32);
            length = 2;
        }
        normalize;
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
    bool opEquals(ref const BigInt rhs)
        const @safe pure nothrow @nogc
    {
        return view == rhs.view;
    }

    /++
    +/
    auto opCmp(ref const BigInt rhs) 
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
    Performs `size_t overflow = big *= scalar` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned value to multiply by
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
    Performs `size_t overflow = big *= fixed` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned value to multiply by
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
    Performs `size_t overflow = big *= fixed` operatrion.
    Precondition: non-empty coefficients
    Params:
        rhs = unsigned value to multiply by
    Returns:
        overflow
    +/
    bool opOpAssign(string op)(ref const BigInt rhs)
        @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        int diff = length - rhs.length;
        if (diff < 0)
        {
            auto oldLength = length;
            length = rhs.length;
            view.unsigned.leastSignificantFirst[oldLength .. $] = 0;
        }
        else
        if (rhs.length == 0)
            return false;
        auto thisView = view;
        auto overflow = thisView.opOpAssign!op(rhs.view);
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
    static BigInt fromHexString()(scope const(char)[] str)
        @trusted pure
    {
        BigInt ret;
        auto len = str.length / (size_t.sizeof * 2) + (str.length % (size_t.sizeof * 2) != 0);
        if (len > ret.data.length)
        {
            version(D_Exceptions)
                throw hexStringException;
            else
                assert(0, hexStringErrorMsg);
        }
        ret.length = cast(uint)len;
        ret.view.unsigned.fromHexStringImpl(str);
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

    /++
    +/
    bool copyFrom(W, WordEndian endian)(BigIntView!(const W, endian) view)
    {
        static if (W.sizeof > size_t.sizeof)
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
}

///
version(mir_test)
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
