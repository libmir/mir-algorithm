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
    size64 = count of 64bit words in coefficient
+/
@serdeScoped @serdeProxy!(const(char)[])
struct BigInt(uint size64)
    if (size64 && size64 <= ushort.max)
{
    import mir.bignum.low_level_view;
    import mir.bignum.fixed;

    ///
    bool sign;
    ///
    uint length;
    ///
    size_t[ulong.sizeof / size_t.sizeof * size64] data;// = void;

@safe:

    ///
    this(uint size)(UInt!size fixedInt)
    {
        this(fixedInt.data);
    }

    ///
    this(uint N)(size_t[N] data)
        if (N <= this.data.length)
    {
        static if (data.length == 0)
        {
            sign = false;
            length = 0;
        }
        static if (data.length == 1)
        {
            this(data[0]);
        }
        else
        static if (data.length == 2)
        {
            sign = false;
            this.data[0] = data[0];
            this.data[1] = data[1];
            this.length = data[1] ? 2 : data[0] != 0;
        }
        else
        {
            sign = false;
            this.data[0 .. N] = data;
            length = data.length;
            normalize;
        }
    }

    ///
    this(ulong data)
    {
        sign = false;
        static if (size_t.sizeof == ulong.sizeof)
        {
            length = data != 0;
            this.data[0] = data;
        }
        else
        {
            this.length = !!data + !!(data >> 32);
            this.data[0] = cast(uint) data;
            this.data[1] = cast(uint) (data >> 32);
        }
    }

    ///
    this(long data)
    {
        this(ulong(data < 0 ? -data : data));
        this.sign = data < 0;
    }

    ///
    this(int data)
    {
        this(long(data));
    }

    ///
    this(uint data)
    {
        this(ulong(data));
    }

    ///
    this()(scope const(char)[] str) @safe pure @nogc
    {
        if (fromStringImpl(str))
            return;
        static if (__traits(compiles, () @nogc { throw new Exception("Can't parse BigInt."); }))
        {
            import mir.exception: MirException;
            throw new MirException("Can't parse BigInt!" ~ size64.stringof ~ " from string `", str , "`.");
        }
        else
        {
            static immutable exception = new Exception("Can't parse BigInt!" ~ size64.stringof ~ ".");
            { import mir.exception : toMutable; throw exception.toMutable; }
        }
    }

    ///
    inout(size_t)[] coefficients()() inout @property scope return
    {
        return data[0 .. length];
    }

    ///
    ref opAssign(ulong data) return scope
    {
        __ctor(data);
        return this;
    }

    ///
    ref opAssign(long data) return scope
    {
        __ctor(data);
        return this;
    }

    ///
    ref opAssign(uint data) return scope
    {
        __ctor(data);
        return this;
    }

    ///
    ref opAssign(int data) return scope
    {
        __ctor(data);
        return this;
    }

    ///
    ref opAssign(uint rhsSize)(UInt!rhsSize data) return scope
    {
        __ctor(data);
        return this;
    }

    static if (size64 == 3)
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
    ref opAssign(uint rhsSize64)(auto ref scope const BigInt!rhsSize64 rhs) return
        @trusted pure nothrow @nogc
        in (rhs.length <= this.data.length)
    {
        static if (size64 == rhsSize64)
        {
            if (&this is &rhs)
                return this;
        }
        this.sign = rhs.sign;
        this.length = rhs.length;
        this.data[0 .. length] = rhs.data[0 .. length];
        return this;
    }

    ///
    static BigInt fromBigEndian()(scope const(ubyte)[] data, bool sign = false)
        @trusted pure @nogc
    {
        static immutable bigIntOverflowException = new Exception("BigInt!" ~ size64.stringof ~ ".fromBigEndian: data overflow");
        BigInt ret = void;
        if (!ret.copyFromBigEndian(data, sign))
            { import mir.exception : toMutable; throw bigIntOverflowException.toMutable; }
        return ret;
    }

    ///
    bool copyFromBigEndian()(scope const(ubyte)[] data, bool sign = false)
        @trusted pure @nogc
    {
        while(data.length && data[0] == 0)
            data = data[1 .. $];
        if (data.length == 0)
        {
            this.length = 0;
            this.sign = false;
        }
        else
        {
            if (data.length > this.data.sizeof)
                return false;
            this.sign = sign;
            this.length = cast(uint) (data.length / size_t.sizeof);
            auto tail = data[0 .. data.length % size_t.sizeof];
            data = data[data.length % size_t.sizeof .. $];
            foreach_reverse (ref c; this.coefficients)
            {
                size_t value;
                foreach (j; 0 .. size_t.sizeof)
                {
                    value <<= 8;
                    value |= data[0];
                    data = data[1 .. $];
                }
                c = value;
            }
            assert(data.length == 0);
            if (tail.length)
            {
                this.length++; 
                size_t value;
                foreach (b; tail)
                {
                    value <<= 8;
                    value |= b;
                }
                this.data[length - 1] = value;
            }
        }
        return true;
    }

    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients.
    +/
    bool fromStringImpl(C)(scope const(C)[] str)
        scope @trusted pure @nogc nothrow
        if (isSomeChar!C)
    {
        auto work = data[].BigIntView!size_t; 
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
        BigInt ret = void;
        ret.sign = sign;
        ret.length = length;
        ret.data[0 .. length] = data[0 .. length];
        return ret;
    }

    ///
    bool opEquals()(auto ref const BigInt rhs)
        const @safe pure nothrow @nogc
    {
        return view == rhs.view;
    }

    ///
    bool opEquals(ulong rhs, bool rhsSign = false)
        const @safe pure nothrow @nogc
    {
        if (rhs == 0 && this.length == 0 || this.length == 1 && this.sign == rhsSign && this.data[0] == rhs)
            return true;
        static if (is(size_t == ulong) || size64 == 1)
            return false;    
        else
            return this.length == 2 && this.data[0] == cast(uint) rhs && this.data[1] == cast(uint) (rhs >> 32);
    }

    ///
    bool opEquals(long rhs)
        const @safe pure nothrow @nogc
    {
        auto sign = rhs < 0;
        return this.opEquals(sign ? ulong(-rhs) : ulong(rhs), sign);
    }

    ///
    bool opEquals(uint rhs)
        const @safe pure nothrow @nogc
    {
        return opEquals(ulong(rhs), false);
    }

    ///
    bool opEquals(int rhs)
        const @safe pure nothrow @nogc
    {
        return opEquals(long(rhs));
    }

    /++
    +/
    auto opCmp()(auto ref const BigInt rhs) 
        const @safe pure nothrow @nogc
    {
        return view.opCmp(rhs.view);
    }

    ///
    BigIntView!size_t view()() scope return @property
    {
        return typeof(return)(this.data[0 .. this.length], this.sign);
    }

    ///
    BigIntView!(const size_t) view()() const scope return @property
    {
            return typeof(return)(this.data[0 .. this.length], this.sign);
    }

    ///
    void normalize()()
    {
        pragma(inline, false);
        auto norm = view.normalized;
        this.length = cast(uint) norm.unsigned.coefficients.length;
        this.sign = norm.sign;
    }

    /++
    +/
    void putCoefficient(size_t value)
    {
        assert(length < data.length);
            data[length++] = value;
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

    ///
    ref opOpAssign(string op, size_t size)(UInt!size rhs)
        @safe pure nothrow @nogc scope return
        if (op == "/" || op == "%")
    {
        BigInt!(size / 64) bigRhs = rhs;
        return this.opOpAssign!op(bigRhs);
    }

    /// ditto
    ref opOpAssign(string op)(ulong rhs)
        @safe pure nothrow @nogc scope return
        if (op == "/" || op == "%")
    {
        BigInt!1 bigRhs = rhs;
        return this.opOpAssign!op(bigRhs);
    }

    /// ditto
    ref opOpAssign(string op)(long rhs)
        @safe pure nothrow @nogc scope return
        if (op == "/" || op == "%")
    {
        BigInt!1 bigRhs = rhs;
        return this.opOpAssign!op(bigRhs);
    }

    /++
    +/
    ref powMod(uint expSize)(scope ref const BigInt!expSize exponent, scope ref const BigInt modulus)
        @safe pure nothrow @nogc return scope
        in(!exponent.sign)
    {
        return this.powMod(exponent.view.unsigned, modulus);
    }

    ///ditto
    ref powMod()(scope BigUIntView!(const size_t) exponent, scope ref const BigInt modulus)
        @safe pure nothrow @nogc return scope
    {
        pragma(inline, false);

        import mir.ndslice.topology: bitwise;

        if (modulus == 1 || modulus == -1)
        {
            this.sign = 0;
            this.length = 0;
            return this;
        }

        BigInt!(size64 * 2) bas = void;
        bas = this;
        BigInt!(size64 * 2) res = void;
        res = 1u;

        foreach (b; exponent.coefficients.bitwise[0 .. $ - exponent.ctlz])
        {
            bas %= modulus;
            if (b)
            {
                res *= bas;
                res %= modulus;
            }
            bas *= bas;
        }

        this = res;
        return this;
    }

    ///
    static if (size64 == 3)
    version (mir_bignum_test)
    unittest
    {
        BigInt!3 x = 2;
        BigInt!3 e = 10;
        BigInt!3 m = 100;

        x.powMod(e, m);
        assert(x == 24);
    }

    ///
    static if (size64 == 3)
    version (mir_bignum_test)
    unittest
    {
        BigInt!3 x = 564321;
        BigInt!3 e = "13763753091226345046315979581580902400000310";
        BigInt!3 m = "13763753091226345046315979581580902400000311";

        x.powMod(e, m);
        assert(x == 1);
    }

    /++
    +/
    ref multiply(uint aSize64, uint bSize64)
    (
        scope ref const BigInt!aSize64 a,
        scope ref const BigInt!bSize64 b,
    )
        @safe pure nothrow @nogc scope return
        if (size64 >= aSize64 + bSize64)
    {
        import mir.utility: max;
        import mir.bignum.internal.kernel : multiply, karatsubaRequiredBuffSize;
        enum sizeM = ulong.sizeof / size_t.sizeof;
        size_t[max(aSize64 * sizeM, bSize64 * sizeM).karatsubaRequiredBuffSize] buffer = void;
        this.length = cast(uint) multiply(data, a.coefficients, b.coefficients, buffer);
        this.sign = (this.length != 0) & (a.sign ^ b.sign);
        return this;
    }

    ///
    ref divMod(uint divisorSize64, uint remainderSize = size64)
    (
        scope ref const BigInt!divisorSize64 divisor,
        scope ref BigInt!size64 quotient,
        scope ref BigInt!remainderSize remainder,
    )
        const @trusted pure nothrow @nogc scope return
        if (remainderSize >= divisorSize64)
    {
        return this.divMod(divisor, quotient, &remainder);
    }

    private ref divMod(uint divisorSize64, uint remainderSize = size64)
    (
        scope ref const BigInt!divisorSize64 divisor,
        scope ref BigInt!size64 quotient,
        scope BigInt!remainderSize* remainder = null,
    )
        const @trusted pure nothrow @nogc scope return
        if (remainderSize >= divisorSize64)
    {
        import mir.bignum.internal.kernel : divMod, divisionRequiredBuffSize;

        pragma(inline, false);

        if (divisor.length == 0)
            assert(0, "Zero BigInt divizor");
        if (divisor.coefficients[$ - 1] == 0)
            assert(0, "Denormalized BigInt divizor");

        if (this.length < divisor.length)
        {
            if (remainder !is null)
            {
                if (&this !is remainder)
                    *remainder = this;
                remainder.sign = 0;
            }

            static if (size64 == remainderSize)
                if (&quotient is remainder)
                    return this;

            quotient.sign = 0;
            quotient.length = 0;

            return this;
        }

        enum sizeM = ulong.sizeof / size_t.sizeof;
        enum vlen = min(divisorSize64, size64);
        size_t[divisionRequiredBuffSize(size64 * sizeM, vlen * sizeM)] buffer = void;

        quotient.length = cast(uint) divMod(
            quotient.data,
            remainder !is null ? remainder.data[] : null,
            this.coefficients,
            divisor.coefficients,
            buffer,
        );

        quotient.sign = (this.sign ^ divisor.sign) && quotient.length;

        if (remainder !is null)
        {
            remainder.sign = 0;
            remainder.length = divisor.length;
            remainder.normalize;
        }

        return this;
    }

    /++
    Performs `this %= rhs` and `this /= rhs` operations.
    Params:
        rhs = value to divide by
    Returns:
        remainder or quotient from the truncated division
    +/
    ref opOpAssign(string op, size_t rhsSize64)(scope const ref BigInt!rhsSize64 rhs)
        @safe pure nothrow @nogc return
        if (op == "/" || op == "%")
    {
        enum isRem = op == "%";
        return this.divMod(rhs, this, isRem ? &this : null);
    }

    /++
    Performs `this %= rhs` and `this /= rhs` operations.
    Params:
        rhs = value to divide by
    Returns:
        remainder or quotient from the truncated division
    +/
    ref opOpAssign(string op : "*", size_t rhsSize64)(scope const ref BigInt!rhsSize64 rhs)
        @safe pure nothrow @nogc return
    {
        BigInt!(size64 + rhsSize64) c = void;
        c.multiply(this, rhs);
        this = c;
        return this;
    }

    ///
    static if (size64 == 3)
    version (mir_bignum_test)
    unittest
    {
        BigInt!32 x = "236089459999051800787306800176765276560685597708945239133346035689205694959466543423391020917332149321603397284295007899190053323478336179162578944";
        BigInt!32 y = "19095614279677503764429420557677401943131308638097701560446870251856566051181587499424174939645900335127490246389509326965738171086235365599977209919032320327138167362675030414072140005376";
        BigInt!32 z = "4508273263639244391466225874448166762388283627989411942887789415132291146444880491003321910228134369483394456858712486391978856464207606191606690798518090459546799016472580324664149788791167494389789813815605288815981925073283892089331019170542792502117265455020551819803771537458327634120582677504637693661973404860326560198184402944";
        x *= y;
        assert(x == z);
    }

    /++
    Performs `size_t overflow = big *= fixed` operatrion.
    Params:
        rhs = unsigned value to multiply by
    Returns:
        overflow
    +/
    bool opOpAssign(string op, size_t rhsSize64)(ref const BigInt!rhsSize64 rhs)
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
            coefficients[oldLength .. $] = 0;
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

    /// ditto
    bool opOpAssign(string op)(ulong rhs)
        @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        import mir.ndslice.bignum.fixed: UInt;
        return this.opOpAssign!op(rhs.UInt!64.view.signed);
    }

    /// ditto
    bool opOpAssign(string op)(uint rhs)
        @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        return this.opOpAssign!op(ulong(rhs));
    }

    /// ditto
    bool opOpAssign(string op)(long rhs)
        @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        import mir.bignum.fixed: UInt;
        auto sign = rhs < 0;
        rhs = sign ? -rhs : rhs;
        return this.opOpAssign!op(rhs.UInt!64.view.normalized.signed(sign));
    }

    /// ditto
    bool opOpAssign(string op)(int rhs)
        @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        return this.opOpAssign!op(long(rhs));
    }

    /++
    +/
    static BigInt fromHexString(bool allowUnderscores = false)(scope const(char)[] str)
        @trusted pure
    {
        BigInt ret = void;
        if (ret.fromHexStringImpl!(char, allowUnderscores)(str))
            return ret;
        version(D_Exceptions)
            { import mir.exception : toMutable; throw hexStringException.toMutable; }
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
        length = cast(uint)work.unsigned.coefficients.length;
        sign = work.sign;
        return ret;
    }

    /++
    +/
    static BigInt fromBinaryString(bool allowUnderscores = false)(scope const(char)[] str)
        @trusted pure
    {
        BigInt ret = void;
        if (ret.fromBinaryStringImpl!(char, allowUnderscores)(str))
            return ret;
        version(D_Exceptions)
            { import mir.exception : toMutable; throw binaryStringException.toMutable; }
        else
            assert(0, binaryStringErrorMsg);
    }

    static if (size64 == 3)
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
        length = cast(uint)work.unsigned.coefficients.length;
        sign = work.sign;
        return ret;
    }

    ///
    ref pow()(ulong degree)
    {
        BigInt!size64 bas = void;
        bas = this;
        this = 1u;

        while (degree)
        {
            if (degree & 1)
                this *= bas;
            bas *= bas;
            degree >>= 1;
        }
        return this;
    }

    ///
    bool mulPow5()(ulong degree)
    {
        import mir.bignum.internal.dec2float: MaxWordPow5;
        // assert(approxCanMulPow5(degree));
        if (length == 0)
            return false;
        enum n = MaxWordPow5!size_t;
        enum wordInit = size_t(5) ^^ n;
        size_t word = wordInit;
        size_t overflow;

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
            overflow |= this *= word;
        }
        return overflow != 0;
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
            auto d = view.coefficients;
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
            auto most = d[$ - (index + 1)] = d[$ - 1] >>> bs;
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
                auto most = coefficients[$ - 1] >> ss;
                length += index;
                if (length < data.length)
                {
                    if (most)
                    {
                        length++;
                        coefficients[$ - 1] = most;
                        length--;
                    }
                }
                else
                {
                    length = data.length;
                }

                auto d = view.coefficients;
                foreach_reverse (j; index + 1 .. length)
                {
                    d[j] = (d[j - index] << bs) | (d[j - (index + 1)] >> ss);
                }
                d[index] = d[0] << bs;
                if (length < data.length)
                    length += most != 0;
            }
            else
            {
                length = cast(uint) min(length + index, cast(uint)data.length);
                auto d = view.coefficients;
                foreach_reverse (j; index .. length)
                {
                    d[j] = d[j - index];
                }
            }
            view.coefficients[0 .. index] = 0;
        }
        return this;
    }

    ///
    T opCast(T)() const
        if (isFloatingPoint!T && isMutable!T)
    {
        return view.opCast!T;
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
    bool copyFrom(W)(scope const(W)[] coefficients, bool sign = false)
        if (__traits(isUnsigned, W))
    {
        static if (W.sizeof > size_t.sizeof)
        {
            return this.copyFrom(cast(BigIntView!(const size_t))view, sign);
        }
        else
        {
            this.sign = sign;
            auto dest = cast(W[])data;
            auto overflow = dest.length < coefficients.length;
            auto n = overflow ? dest.length : coefficients.length;
            this.length = cast(uint)(n / (size_t.sizeof / W.sizeof));
            dest[0 .. n] = coefficients[0 .. n];
            static if (size_t.sizeof / W.sizeof > 1)
            {
                if (auto tail = n % (size_t.sizeof / W.sizeof))
                {
                    this.length++;
                    auto shift = ((size_t.sizeof / W.sizeof) - tail) * (W.sizeof * 8);
                    auto value = this.coefficients[$ - 1];
                    value <<= shift;
                    value >>= shift;
                    this.coefficients[$ - 1] = value;
                }
            }
            return overflow;
        }
    }

    ///
    immutable(C)[] toString(C = char)() scope const @safe pure nothrow
        if(isSomeChar!C && isMutable!C)
    {
        C[ceilLog10Exp2(data.length * (size_t.sizeof * 8)) + 1] buffer = void;
        BigInt copy = this;
        auto len = copy.view.unsigned.toStringImpl(buffer);
        if (sign)
            buffer[$ - ++len] = '-';
        return buffer[$ - len .. $].idup;
    }

    static if (size64 == 3)
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
    void toString(C = char, W)(ref scope W w) scope const
        if(isSomeChar!C && isMutable!C)
    {
        C[ceilLog10Exp2(data.length * (size_t.sizeof * 8)) + 1] buffer = void;
        BigInt copy = this;
        auto len = copy.view.unsigned.toStringImpl(buffer);
        if (sign)
            buffer[$ - ++len] = '-';
        w.put(buffer[$ - len .. $]);
    }

    ///
    size_t bitLength()() const @property
    {
        return length == 0 ? 0 : length * size_t.sizeof * 8 - data[length - 1].ctlz;
    }

    ///
    size_t ctlz()() const @property
    {
        return data.sizeof * 8 - bitLength;
    }
}

/// Check @nogc toString impl
version(mir_bignum_test) @safe pure @nogc unittest
{
    import mir.format;
    auto str = "-34010447314490204552169750449563978034784726557588085989975288830070948234680";
    auto integer = BigInt!4(str);
    auto buffer = stringBuf;
    buffer << integer;
    assert(buffer.data == str);
}

///
version(mir_bignum_test)
unittest
{
    import mir.test;
    import mir.bignum.fixed;
    import mir.bignum.low_level_view;

    {
        auto a = BigInt!4.fromHexString("c39b18a9f06fd8e962d99935cea0707f79a222050aaeaaaed17feb7aa76999d7");
        auto b = UInt!128.fromHexString("f79a222050aaeaaa417fa25a2ac93291");

        // ca3d7e25aebe687b 168dcef32d0bb2f0
        auto c = BigInt!4.fromHexString("bf4c87424431d21563f23b1fc00d75ac");
        a %= b;
        a.should == c;
        a = BigInt!4.fromHexString("c39b18a9f06fd8e962d99935cea0707f79a222050aaeaaaed17feb7aa76999d7");
        a /= b;
        assert(a == BigInt!4.fromHexString("ca3d7e25aebe687b7cc1b250b44690fb"));
    }

    {
        auto a = BigInt!4.fromHexString("7fff000080000000000000000000");
        auto b = UInt!128.fromHexString("80000000000000000001");

        auto c = BigInt!4.fromHexString("fffe0000");
        a /= b;
        a.should == c;

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

    void test(const long av, const long bv)
    {
        auto a = BigInt!4(av);
        const b = BigInt!4(bv);
        a /= b;
        assert(a == av / bv);
        a = BigInt!4(av);
        a %= b;
        assert(a == av % bv);
    }

    {
        auto av = 0xDEADBEEF;
        auto bv = 0xDEAD;
        test(+av, +bv);
        // test(+av, -bv);
        // test(-av, +bv);
        // test(+av, +bv);
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
    assert(!c.copyFrom(b.coefficients, b.sign));
    assert(c == b);
    b >>= 18;
    auto bView = cast(BigIntView!ushort)b.view;
    assert(!c.copyFrom(bView.coefficients[0 .. $ - 1], bView.sign));
    assert(c == b);
}

version(mir_bignum_test)
@safe pure @nogc unittest
{
    BigInt!4 i = "-0";
    assert(i.coefficients.length == 0);
    assert(!i.sign);
    assert(cast(long) i == 0);
}
