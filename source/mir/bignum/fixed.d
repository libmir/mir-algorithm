/++
Note:
    The module doesn't provide full arithmetic API for now.
+/
module mir.bignum.fixed;

import std.traits;
import mir.bitop;
import mir.utility;

/++
Fixed-length unsigned integer.

Params:
    size = size in bits
+/
struct UInt(size_t size)
    if (size % (size_t.sizeof * 8) == 0 && size >= size_t.sizeof * 8)
{
    import mir.bignum.fixed: UInt;
    /++
    Payload. The data is located in the target endianness.
    +/
    size_t[size / (size_t.sizeof * 8)] data;

    ///
    this(size_t N)(auto ref const size_t[N] data)
        if (N && N <= this.data.length)
    {
        version(LittleEndian)
            this.data[0 .. N] = data;
        else
            this.data[$ - N .. $] = data;
    }

    ///
    this(size_t argSize)(auto ref const UInt!argSize arg)
        if (argSize <= size)
    {
        this(arg.data);
    }

    static if (size_t.sizeof == uint.sizeof && data.length % 2 == 0)
    ///
    this()(auto ref const ulong[data.length / 2] data)
    {
        if (!__ctfe)
        {
            this.data =  cast(typeof(this.data)) data;
        }
        else
        {
            version(LittleEndian)
            {
                static foreach (i; 0 .. data.length)
                {
                    this.data[i * 2 + 0] = cast(uint) data[i];
                    this.data[i * 2 + 1] = cast(uint) (data[i] >> 32);
                }
            }
            else
            {
                static foreach (i; 0 .. data.length)
                {
                    this.data[i * 2 + 1] = cast(uint) data[i];
                    this.data[i * 2 + 0] = cast(uint) (data[i] >> 32);
                }
            }
        }
    }

    static if (size >= 64)
    ///
    this(ulong data)
    {
        static if (size_t.sizeof == ulong.sizeof)
        {
            this.data[0] = data;
        }
        else
        {
            this.data[0] = cast(uint) data;
            this.data[1] = cast(uint) (data >> 32);
        }
    }

    static if (size < 64)
    ///
    this(uint data)
    {
        this.data[0] = data;
    }

    ///
    this(C)(scope const(C)[] str) @safe pure @nogc
        if (isSomeChar!C)
    {
        if (fromStringImpl(str))
            return;
        static if (__traits(compiles, () @nogc { throw new Exception("Can't parse UInt."); }))
        {
            import mir.exception: MirException;
            throw new MirException("Can't parse UInt!" ~ size.stringof ~ " from string `", str , "`.");
        }
        else
        {
            static immutable exception = new Exception("Can't parse UInt!" ~ size.stringof ~ ".");
            throw exception;
        }
    }

    static if (size == 128)
    ///
    version(mir_bignum_test) @safe pure @nogc unittest
    {
        import mir.math.constant: PI;
        UInt!256 integer = "34010447314490204552169750449563978034784726557588085989975288830070948234680"; // constructor
        assert(integer == UInt!256.fromHexString("4b313b23aa560e1b0985f89cbe6df5460860e39a64ba92b4abdd3ee77e4e05b8"));
    }

    /++
    Returns: false in case of overflow or incorrect string.
    Precondition: non-empty coefficients.
    +/
    bool fromStringImpl(C)(scope const(C)[] str)
        scope @trusted pure @nogc nothrow
        if (isSomeChar!C)
    {
        import mir.bignum.low_level_view: BigUIntView;
        return BigUIntView!size_t(data[]).fromStringImpl(str);
    }

    ///
    immutable(C)[] toString(C = char)() scope const @safe pure nothrow
        if(isSomeChar!C && isMutable!C)
    {
        UInt!size copy = this;
        auto work = copy.view.normalized;
        import mir.bignum.low_level_view: ceilLog10Exp2;
        C[ceilLog10Exp2(data.length * (size_t.sizeof * 8))] buffer = void;
        return buffer[$ - work.toStringImpl(buffer) .. $].idup;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test) @safe pure unittest
    {
        auto str = "34010447314490204552169750449563978034784726557588085989975288830070948234680";
        auto integer = UInt!256(str);
        assert(integer.toString == str);

        integer = UInt!256.init;
        assert(integer.toString == "0");
    }

    ///
    void toString(C = char, W)(ref scope W w) scope const
        if(isSomeChar!C && isMutable!C)
    {
        UInt!size copy = this;
        auto work = copy.view.normalized;
        import mir.bignum.low_level_view: ceilLog10Exp2;
        C[ceilLog10Exp2(data.length * (size_t.sizeof * 8))] buffer = void;
        w.put(buffer[$ - work.toStringImpl(buffer) .. $]);
    }

    static if (size == 128)
    /// Check @nogc toString impl
    version(mir_bignum_test) @safe pure @nogc unittest
    {
        import mir.format: stringBuf;
        auto str = "34010447314490204552169750449563978034784726557588085989975288830070948234680";
        auto integer = UInt!256(str);
        auto buffer = stringBuf;
        buffer << integer;
        assert(buffer.data == str);
    }

    ///
    enum UInt!size max = ((){UInt!size ret; ret.data = size_t.max; return ret;})();

    ///
    enum UInt!size min = UInt!size.init;

    import mir.bignum.low_level_view: BigUIntView;

    ///
    BigUIntView!size_t view() @property pure nothrow @nogc scope return @safe
    {
        return BigUIntView!size_t(data);
    }

    ///
    BigUIntView!(const size_t) view() const @property pure nothrow @nogc scope return @safe
    {
        return BigUIntView!(const size_t)(data);
    }

    ///
    static UInt!size fromHexString(bool allowUnderscores = false)(scope const(char)[] str)
    {
        typeof(return) ret;
        if (ret.fromHexStringImpl!(char, allowUnderscores)(str))
            return ret;
        version(D_Exceptions)
        {
            import mir.bignum.low_level_view: hexStringException;
            throw hexStringException;
        }
        else
        {
            import mir.bignum.low_level_view: hexStringErrorMsg;
            assert(0, hexStringErrorMsg);
        }
    }

    /++
    +/
    bool fromHexStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        return view.fromHexStringImpl!(C, allowUnderscores)(str);
    }

    ///
    static UInt!size fromBinaryString(bool allowUnderscores = false)(scope const(char)[] str)
    {
        typeof(return) ret;
        if (ret.fromBinaryStringImpl!(char, allowUnderscores)(str))
            return ret;
        version(D_Exceptions)
        {
            import mir.bignum.low_level_view: binaryStringException;
            throw binaryStringException;
        }
        else
        {
            import mir.bignum.low_level_view: binaryStringErrorMsg;
            assert(0, binaryStringErrorMsg);
        }
    }

    /++
    +/
    bool fromBinaryStringImpl(C, bool allowUnderscores = false)(scope const(C)[] str)
        @safe pure @nogc nothrow
        if (isSomeChar!C)
    {
        return view.fromBinaryStringImpl!(C, allowUnderscores)(str);
    }

    /++
    +/
    auto opEquals(size_t rhsSize)(auto ref const UInt!rhsSize rhs) const
    {
        static if (rhsSize == size)
            return this.data == rhs.data;
        else
        static if (rhsSize > size)
            return this.toSize!rhsSize.data == rhs.data;
        else
            return this.data == rhs.toSize!size.data;
    }

    static if (size >= 64)
    /// ditto
    auto opEquals(ulong rhs) const
    {
        return opEquals(UInt!size(rhs));
    }
    else
    auto opEquals(uint rhs) const
    {
        return opEquals(UInt!size(rhs));
    }

    /++
    +/
    auto opCmp(UInt!size rhs) const
    {
        foreach_reverse(i; 0 .. data.length)
        {
            if (this.data[i] < rhs.data[i])
                return -1;
            if (this.data[i] > rhs.data[i])
                return +1;
        }
        return 0;
    }

    static if (size >= 64)
    /// ditto
    auto opCmp(ulong rhs) const scope
    {
        return opCmp(UInt!size(rhs));
    }
    else
    auto opCmp(uint rhs) const scope
    {
        return opCmp(UInt!size(rhs));
    }

    static if (size >= 64)
    /++
    +/
    ref UInt!size opAssign(ulong rhs) scope return
        @safe pure nothrow @nogc
    {
        this.data = UInt!size(rhs).data;
        return this;
    }
    else
    ///
    ref UInt!size opAssign(uint rhs) scope return
        @safe pure nothrow @nogc
    {
        this.data = UInt!size(rhs).data;
        return this;
    }

    /++
    +/
    ref UInt!size opAssign(uint rhsSize)(UInt!rhsSize rhs) scope return
        @safe pure nothrow @nogc
    {
        this.data = UInt!size(rhs).data;
        return this;
    }

    /++
    `bool overflow = a += b ` and `bool overflow = a -= b` operations.
    +/
    bool opOpAssign(string op)(UInt!size rhs, bool overflow = false)
        @safe pure nothrow @nogc scope
        if (op == "+" || op == "-")
    {
        return view.opOpAssign!op(rhs.view, overflow);
    }

    /// ditto
    bool opOpAssign(string op)(size_t rhs)
        @safe pure nothrow @nogc scope
        if (op == "+" || op == "-")
    {
        return view.opOpAssign!op(rhs);
    }

    static if (size_t.sizeof < ulong.sizeof)
    /// ditto
    bool opOpAssign(string op)(ulong rhs)
        @safe pure nothrow @nogc scope
        if (op == "+" || op == "-")
    {
        return opOpAssign!op(UInt!size(rhs));
    }

    /// ditto
    bool opOpAssign(string op, uint rsize)(UInt!rsize rhs, bool overflow = false)
        @safe pure nothrow @nogc scope
        if ((op == "+" || op == "-") && rsize < size)
    {
        return opOpAssign!op(rhs.toSize!size, overflow);
    }

    /++
    Returns: overflow value of multiplication
    +/
    size_t opOpAssign(string op : "*")(size_t rhs, size_t carry = 0)
        @safe pure nothrow @nogc scope
    {
        return view.opOpAssign!op(rhs, carry);
    }

    static if (size_t.sizeof == 4)
    /// ditto
    auto opOpAssign(string op : "*")(ulong rhs)
        @safe pure nothrow @nogc scope
    {
        return opOpAssign!op(UInt!64(rhs));
    }


    /++
    Returns: overflow value of multiplication
    +/
    void opOpAssign(string op : "*", size_t rhsSize)(UInt!rhsSize rhs)
        @safe pure nothrow @nogc scope
        if (rhsSize <= size)
    {
        this = extendedMul(this, rhs).toSize!size;
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
        @safe pure nothrow @nogc scope
    {
        assert(overflow < rhs);
        auto work = view.normalized;
        if (worl.coefficients.length)
            return work.opOpAssign!op(rhs, overflow);
        return overflow;
    }

    /++
    Performs division & extracts the remainder.
    Params:
        rhs = unsigned value to divide by
    Returns: quotient, sets `rhs` to remainder
    +/ 
    ref divMod(size_t rhsSize)(scope ref UInt!rhsSize rhs)
        @safe pure nothrow @nogc scope return
    {
        import mir.bignum.internal.kernel: divMod, divisionRequiredBuffSize;

        UInt!size quotient;

        auto dividendV = this.view;
        auto divisorV = rhs.view;
        divisorV = divisorV.normalized;
        dividendV = dividendV.normalized;

        import mir.utility: min;
        enum vlen = min(rhs.data.length, data.length);
        size_t[divisionRequiredBuffSize(data.length, vlen)] buffer = void;

        divMod(
            quotient.data,
            divisorV.coefficients,
            dividendV.coefficients,
            divisorV.coefficients,
            buffer);
        this = quotient;
        return this;
    }

    /++
    Performs `big /= rhs` operation.
    Params:
        rhs = unsigned value to divide by
    Returns:
        quotient from division 
    +/
    ref opOpAssign(string op : "/", size_t rhsSize)(UInt!rhsSize rhs)
        @safe pure nothrow @nogc scope return
    {
        return this.divMod(rhs);
    }

    /// ditto
    ref opOpAssign(string op : "/")(ulong rhs)
        @safe pure nothrow @nogc scope return
    {
        return opOpAssign!(op, ulong.sizeof * 8)(UInt!(ulong.sizeof * 8)(rhs));
    }

    /++
    Performs `big %= rhs` operation.
    Params:
        rhs = unsigned value to divide by
    Returns:
        remainder from division
    +/
    ref opOpAssign(string op : "%", size_t rhsSize)(UInt!rhsSize rhs)
        @safe pure nothrow @nogc scope return
    {
        this.divMod(rhs);
        this = cast(UInt!size)rhs;
    }

    /// ditto
    ref opOpAssign(string op : "%")(ulong rhs)
        @safe pure nothrow @nogc scope
    {
        return opOpAssign!(op, ulong.sizeof * 8)(UInt!(ulong.sizeof * 8)(rhs));
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("e3251bacb112c88b71ad3f85a970a314");
        auto b = UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d");
        assert(a / b == UInt!128.fromHexString("1"));
        assert(a % b == UInt!128.fromHexString("36920c8e407c9645d0b611586c0a077"));
    }

    ///
    ref UInt!size opOpAssign(string op)(UInt!size rhs) nothrow return
        if (op == "^" || op == "|" || op == "&")
    {
        static foreach (i; 0 .. data.length)
            mixin(`data[i] ` ~ op ~ `= rhs.data[i];`);
        return this;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d");
        auto b = UInt!128.fromHexString("e3251bacb112c88b71ad3f85a970a314");
        assert((a.opBinary!"|"(b)) == UInt!128.fromHexString("ffbffbeffd1affaf75adfff5abf0a39d"));
    }

    ///
    ref UInt!size opOpAssign(string op)(size_t rhs) nothrow return scope
        if (op == "^" || op == "|" || op == "&")
    {
        mixin(`view.coefficients[0] ` ~ op ~ `= rhs;`);
        return this;
    }

    static if (size_t.sizeof < ulong.sizeof)
    /// ditto
    ref opOpAssign(string op)(ulong rhs) return
        @safe pure nothrow @nogc scope
        if (op == "^" || op == "|" || op == "&")
    {
        return opOpAssign!op(UInt!size(rhs));
    }

    ///
    ref UInt!size opOpAssign(string op)(size_t shift)
        @safe pure nothrow @nogc return
        if (op == "<<" || op == ">>")
    {
        auto d = view.coefficients;
        assert(shift < size);
        auto index = shift / (size_t.sizeof * 8);
        auto bs = shift % (size_t.sizeof * 8);
        auto ss = size_t.sizeof * 8 - bs;
        static if (op == ">>")
        {
            if (bs)
            {
                foreach (j; 0 .. data.length - (index + 1))
                {
                    d[j] = (d[j + index] >>> bs) | (d[j + (index + 1)] << ss);
                }
            }
            else
            {
                foreach (j; 0 .. data.length - (index + 1))
                {
                    d[j] = d[j + index];
                }
            }
            d[$ - (index + 1)] = d[$ - 1] >>> bs;
            foreach (j; data.length - index .. data.length)
            {
                d[j] = 0;
            }
        }
        else
        {
            if (bs)
            {
                foreach_reverse (j; index + 1 .. data.length)
                {
                    d[j] = (d[j - index] << bs) | (d[j - (index + 1)] >> ss);
                }
            }
            else
            {
                foreach_reverse (j; index + 1 .. data.length)
                {
                    d[j] = d[j - index];
                }
            }
            d[index] = d[0] << bs;
            foreach_reverse (j; 0 .. index)
            {
                d[j] = 0;
            }
        }
        return this;
    }

    /++
    `auto c = a << b` operation.
    +/
    UInt!size opBinary(string op)(size_t rhs)
        const @safe pure nothrow @nogc
        if (op == "<<" || op == ">>>" || op == ">>")
    {
        UInt!size ret = this;
        ret.opOpAssign!op(rhs);
        return ret;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a << 0 == a);
        assert(a << 4 == UInt!128.fromHexString("fbbfae3cd0aff2714a1de7022b0029d0"));
        assert(a << 68 == UInt!128.fromHexString("4a1de7022b0029d00000000000000000"));
        assert(a << 127 == UInt!128.fromHexString("80000000000000000000000000000000"));
        assert(a >> 0 == a);
        assert(a >> 4 == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029"));
        assert(a >> 68 == UInt!128.fromHexString("afbbfae3cd0aff2"));
        assert(a >> 127 == UInt!128(1));
    }

    /++
    Binary operations
    +/
    template opBinary(string op)
        if (op == "^" || op == "|" || op == "&" || op == "+" || op == "-" || op == "*" || op == "/" || op == "%")
    {
        ///
        UInt!size opBinary(size_t rsize)(UInt!rsize rhs)
            const @safe pure nothrow @nogc
            if (rsize <= size)
        {
            UInt!size ret = this;
            ret.opOpAssign!op(rhs);
            return ret;
        }

        /// ditto
        UInt!size opBinary(ulong rhs)
            const @safe pure nothrow @nogc
        {
            UInt!size ret = this;
            ret.opOpAssign!op(rhs);
            return ret;
        }
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a / UInt!128.fromHexString("5") == UInt!128.fromHexString("23259893f5ceffd49db9f949a0899a1f"));
        assert(a == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));
        assert(a % UInt!128.fromHexString("5") == UInt!128.fromHexString("2"));
        assert(a == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d"));

        assert(a / 5 == UInt!128.fromHexString("23259893f5ceffd49db9f949a0899a1f"));
        assert(a % 5 == UInt!64.fromHexString("2"));
        assert(a % 5 == 2);
    }

    /// ditto
    template opBinaryRight(string op)
        if (op == "^" || op == "|" || op == "&" || op == "+" || op == "*")
    {
        ///
        UInt!size opBinaryRight(size_t lsize)(UInt!lsize lhs)
            const @safe pure nothrow @nogc
            if (lsize < size)
        {
            UInt!size ret = this;
            ret.opOpAssign!op(lhs);
            return ret;
        }

        /// ditto
        UInt!size opBinaryRight(ulong lhs)
            const @safe pure nothrow @nogc
        {
            UInt!size ret = this;
            ret.opOpAssign!op(lhs);
            return ret;
        }
    }

    /++
    Shifts left using at most `size_t.sizeof * 8 - 1` bits
    +/
    UInt!size smallLeftShift(uint shift) const
    {
        assert(shift < size_t.sizeof * 8);
        UInt!size ret = this;
        if (shift)
        {
            auto csh = size_t.sizeof * 8 - shift;
            static foreach_reverse (i; 1 .. data.length)
            {
                ret.data[i] = (ret.data[i] << shift) | (ret.data[i - 1] >>> csh);
            }
            ret.data[0] = ret.data[0] << shift;
        }
        return ret;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a.smallLeftShift(4) == UInt!128.fromHexString("fbbfae3cd0aff2714a1de7022b0029d0"));
    }

    /++
    Shifts right using at most `size_t.sizeof * 8 - 1` bits
    +/
    UInt!size smallRightShift(uint shift) const
    {
        assert(shift < size_t.sizeof * 8);
        UInt!size ret = this;
        if (shift)
        {
            auto csh = size_t.sizeof * 8 - shift;
            static foreach (i; 0 .. data.length - 1)
            {
                ret.data[i] = (ret.data[i] >>> shift) | (ret.data[i + 1] << csh);
            }
            ret.data[$ - 1] = ret.data[$ - 1] >>> shift;
        }
        return ret;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a.smallRightShift(4) == UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029"));
    }

    /++
    +/
    T opCast(T)() const
        if (is(Unqual!T == bool))
    {
        static foreach (i; 0 .. data.length)
        {
            if (data[i])
                return true;
        }
        return false;
    }

    /++
    +/
    T opCast(T)() const
        if (is(Unqual!T == ulong))
    {
        static if (size_t.sizeof == ulong.sizeof)
        {
            return data[0];
        }
        else
        {
            return data[0] | (ulong(data[1]) << 32);
        }
    }

    /++
    +/
    T opCast(T)() const @safe pure nothrow @nogc
        if (is(T == UInt!newSize, uint newSize))
    {
        enum newLength = typeof(return).data.length;
        static if (newLength <= data.length)
        {
            return typeof(return)(data[0 .. newLength]);
        }
        else
        {
            typeof(return) ret;
            ret.data[0 .. data.length] = data;
            return ret;
        }
    }

    /++
    +/
    T opCast(T)() const
        if (is(Unqual!T == uint))
    {
        return cast(uint) data[0];
    }

    /++
    Returns:
        the number with shrinked or extended size.
    +/
    UInt!newSize toSize(size_t newSize, bool lowerBits = true)()
        const @safe pure @nogc nothrow
    {
        typeof(return) ret;
        import mir.utility: min;
        enum N = min(ret.data.length, data.length);
        static if (lowerBits)
        {
                ret.data[0 .. N] = data[0 .. N];
        }
        else
        {
                ret.data[0 .. N] = data[$ - N .. $];
        }
        return ret;
    }

    ///
    UInt!(size + additionalRightBits) rightExtend(size_t additionalRightBits)()
        const @safe pure @nogc nothrow
    {
        static if (additionalRightBits)
        {
            typeof(return) ret;
            version (BigEndian)
                ret.data[0 .. data.length] = data;
            else
                ret.data[$ - data.length .. $] = data;
            return ret;
        }
        else
        {
            return this;
        }
    }

    /++
    +/
    bool bt(size_t position) const
        @safe pure nothrow @nogc
    {
        assert(position < data.sizeof * 8);
        return view.bt(position);
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("afbbfae3cd0aff2714a1de7022b0029d");
        assert(a.bt(127) == 1);
        assert(a.bt(126) == 0);
        assert(a.bt(125) == 1);
        assert(a.bt(124) == 0);
        assert(a.bt(0) == 1);
        assert(a.bt(1) == 0);
        assert(a.bt(2) == 1);
        assert(a.bt(3) == 1);
    }

    /++
    +/
    size_t ctlz() const scope @property
        @safe pure nothrow @nogc
    {
        return view.ctlz;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d");
        assert (a.ctlz == 0);
        a = UInt!128.init;
        assert (a.ctlz == 128);
        a = UInt!128.fromHexString("3");
        assert (a.ctlz == 126);
    }

    /++
    +/
    size_t cttz() const @property
        @safe pure nothrow @nogc
    {
        return view.cttz;
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    @safe pure @nogc
    unittest
    {
        auto a = UInt!128.fromHexString("d");
        assert (a.cttz == 0);
        a = UInt!128.init;
        assert (a.cttz == 128);
        a = UInt!128.fromHexString("300000000000000000");
        assert (a.cttz == 68);
    }

    /++
    +/
    bool signBit() const @property
    {
            return data[$ - 1] >> (size_t.sizeof * 8 - 1);
    }

    /// ditto
    void signBit(bool value) @property
    {
        enum signMask = ptrdiff_t.max;
            data[$ - 1] = (data[$ - 1] & ptrdiff_t.max) | (size_t(value) << (size_t.sizeof * 8 - 1));
    }

    static if (size == 128)
    ///
    version(mir_bignum_test)
    unittest
    {
        auto a = UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d");
        assert(a.signBit);
        a.signBit = false;
        assert(a == UInt!128.fromHexString("5fbbfae3cd0aff2714a1de7022b0029d"));
        assert(!a.signBit);
        a.signBit = true;
        assert(a == UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d"));
    }
}

/++
+/
UInt!sizeB extendedMulHigh(size_t sizeA, size_t sizeB)(UInt!sizeA a, UInt!sizeB b)
    @safe pure nothrow @nogc
{
    return (extendedMul(a, b) >> sizeA).toSize!sizeB;
}

/++
+/
UInt!(sizeA + sizeB) extendedMul(size_t sizeA, size_t sizeB)(UInt!sizeA a, UInt!sizeB b)
    @safe pure nothrow @nogc
{
    UInt!(sizeA + sizeB) ret;
    enum al = a.data.length;
    enum alp1 = a.data.length + 1;
        ret.data[0 .. alp1] = extendedMul(a, b.data[0]).data;
        static foreach ( i; 1 .. b.data.length)
            ret.data[i .. i + alp1] = extendedMulAdd(a, b.data[i], UInt!sizeA(ret.data[i .. i + al])).data;
    return ret;
}

/// ditto
UInt!(size + size_t.sizeof * 8)
    extendedMul(size_t size)(UInt!size a, size_t b)
    @safe pure nothrow @nogc
{
    size_t overflow = a.view *= b;
    auto ret = a.toSize!(size + size_t.sizeof * 8);
    ret.data[$ - 1] = overflow;
    return ret;
}

/// ditto
auto extendedMul()(ulong a, ulong b)
    @safe pure nothrow @nogc
{
    static if (size_t.sizeof == ulong.sizeof)
    {
        import mir.utility: extMul;
        auto e = extMul(a, b);
        return UInt!128([e.low, e.high]);
    }
    else
    {
        return extendedMul(UInt!64(a), UInt!64(b));
    }
}

/// ditto
auto extendedMul()(uint a, uint b)
    @safe pure nothrow @nogc
{
    static if (size_t.sizeof == uint.sizeof)
    {
        import mir.utility: extMul;
        auto e = extMul(a, b);
        version(LittleEndian)
            return UInt!64([e.low, e.high]);
        else
            return UInt!64([e.high, e.low]);
    }
    else
    {
        return UInt!64([ulong(a) * b]);
    }
}

///
version(mir_bignum_test)
@safe pure @nogc
unittest
{
    auto a = UInt!128.max;
    auto b = UInt!256.max;
    auto c = UInt!384.max;
    assert(extendedMul(a, a) == UInt!256.max - UInt!128.max - UInt!128.max);
    assert(extendedMul(a, b) == UInt!384.max - UInt!128.max - UInt!256.max);
    assert(extendedMul(b, a) == UInt!384.max - UInt!128.max - UInt!256.max);

    a = UInt!128.fromHexString("dfbbfae3cd0aff2714a1de7022b0029d");
    b = UInt!256.fromHexString("3fe48f2dc8aad570d037bc9b323fc0cfa312fcc2f63cb521bd8a4ca6157ef619");
    c = UInt!384.fromHexString("37d7034b86e8d58a9fc564463fcedef9e2ad1126dd2c0f803e61c72852a9917ef74fa749e7936a9e4e224aeeaff91f55");
    assert(extendedMul(a, b) == c);
    assert(extendedMul(b, a) == c);

    a = UInt!128.fromHexString("23edf5ff44ee3a4feafc652607aa1eb9");
    b = UInt!256.fromHexString("d3d79144b8941fb50c9102e3251bacb112c88b71ad3f85a970a31458ce24297b");
    c = UInt!384.fromHexString("1dbb62fe6ca5fed101068eda7222d6a9857633ecdfed37a2d156ff6309065ecc633f31465727677a93a7acbd1dac63e3");
    assert(extendedMul(a, b) == c);
    assert(extendedMul(b, a) == c);
}

/// ulong
version(mir_bignum_test)
@safe pure @nogc
unittest
{
    ulong a = 0xdfbbfae3cd0aff27;
    ulong b = 0x14a1de7022b0029d;
    auto c = UInt!128.fromHexString("120827399968ea2a2db185d16e8cc8eb");
    assert(extendedMul(a, b) == c);
    assert(extendedMul(b, a) == c);
}

/// uint
version(mir_bignum_test)
@safe pure @nogc
unittest
{
    uint a = 0xdfbbfae3;
    uint b = 0xcd0aff27;
    auto c = UInt!64.fromHexString("b333243de8695595");
    assert(extendedMul(a, b) == c);
    assert(extendedMul(b, a) == c);
}

/++
+/
UInt!(size + size_t.sizeof * 8)
    extendedMulAdd(size_t size)(UInt!size a, size_t b, UInt!size c)
{
    auto ret = extendedMul(a, b);
    auto view = ret.view;
    view.coefficients[$ - 1] += view.topLeastSignificantPart(a.data.length) += c.view;
    return ret;
}
