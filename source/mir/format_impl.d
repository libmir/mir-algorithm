///
module mir.format_impl;

import mir.format;

@safe pure @nogc nothrow:


size_t printFloatingPointExtend(T, C)(T c, scope ref const FormatSpec spec, scope ref C[512] buf) @trusted
{
    char[512] cbuf = void;
    return extendASCII(cbuf[].ptr, buf[].ptr, printFloatingPoint(cast(double)c, spec, cbuf));
}

size_t printFloatingPointGen(T)(T c, scope ref const FormatSpec spec, scope ref char[512] buf) @trusted
    if(is(T == float) || is(T == double) || is(T == real))
{
    import mir.math.common: copysign, fabs;
    bool neg = copysign(1, c) < 0;
    c = fabs(c);
    char specFormat = spec.format;
    version (CRuntime_Microsoft)
    {
        if (c != c || c.fabs == c.infinity)
        {
            size_t i;
            char s = void;
            if (copysign(1, c) < 0)
                s = '-';
            else
            if (spec.plus)
                s = '+';
            else
            if (spec.space)
                s = ' ';
            else
                goto S;
            buf[0] = s;
            i = 1;
        S:
            static immutable char[3][2][2] special = [["inf", "INF"], ["nan", "NAN"]];
            auto p = &special[c != c][(specFormat & 0xDF) == specFormat][0];
            buf[i + 0] = p[0];
            buf[i + 1] = p[1];
            buf[i + 2] = p[2];
            return i + 3;
        }
    }
    alias T = double;
    static if (is(T == real))
        align(4) char[12] fmt = "%%%%%%*.*gL\0";
    else
        align(4) char[12] fmt = "%%%%%%*.*g\0\0";

    if (specFormat && specFormat != 's' && specFormat != 'g' && specFormat != 'G')
    {
        assert (
            specFormat == 'e'
         || specFormat == 'E'
         || specFormat == 'f'
         || specFormat == 'F'
         || specFormat == 'a'
         || specFormat == 'A', "Wrong floating point format specifier.");
        fmt[9] = specFormat;
    }
    uint fmtRevLen = 5;
    if (spec.hash) fmt[fmtRevLen--] = '#';
    if (spec.space) fmt[fmtRevLen--] = ' ';
    if (spec.zero) fmt[fmtRevLen--] = '0';
    if (spec.plus) fmt[fmtRevLen--] = '+';
    if (spec.dash) fmt[fmtRevLen--] = '-';

    import core.stdc.stdio : snprintf;
    ptrdiff_t res = assumePureSafe(&snprintf)((()@trusted =>buf.ptr)(), buf.length - 1, &fmt[fmtRevLen], spec.width, spec.precision, c);
    assert (res >= 0, "snprintf failed to print a floating point number");
    import mir.utility: min;
    return res < 0 ? 0 : min(cast(size_t)res, buf.length - 1);
}

auto assumePureSafe(T)(T t) @trusted
    // if (isFunctionPointer!T || isDelegate!T)
{
    import std.traits;
    enum attrs = (functionAttributes!T | FunctionAttribute.pure_ | FunctionAttribute.safe) & ~FunctionAttribute.system;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}

////////// FLOATING POINT //////////

pragma(inline, false) size_t printFloatingPoint(float c, scope ref const FormatSpec spec, scope ref char[512] buf)
{
    return printFloatingPoint(cast(double)c, spec, buf);
}

pragma(inline, false) size_t printFloatingPoint(double c, scope ref const FormatSpec spec, scope ref char[512] buf)
{
    return printFloatingPointGen(c, spec, buf);
}

pragma(inline, false) size_t printFloatingPoint(real c, scope ref const FormatSpec spec, scope ref char[512] buf)
{
    version (CRuntime_Microsoft)
    {
        return printFloatingPoint(cast(double) c, spec, buf);
    }
    else
    {
        pragma(inline, false);
        return printFloatingPointGen(c, spec, buf);
    }
}

pragma(inline, false) size_t printFloatingPoint(float c, scope ref const FormatSpec spec, scope ref wchar[512] buf)
{
    return printFloatingPoint(cast(double)c, spec, buf);
}

pragma(inline, false) size_t printFloatingPoint(double c, scope ref const FormatSpec spec, scope ref wchar[512] buf)
{
    return printFloatingPointExtend(c, spec, buf);
}

pragma(inline, false) size_t printFloatingPoint(real c, scope ref const FormatSpec spec, scope ref wchar[512] buf)
{
    version (CRuntime_Microsoft)
    {
        return printFloatingPoint(cast(double) c, spec, buf);
    }
    else
    {
        return printFloatingPointExtend(c, spec, buf);
    }
}

pragma(inline, false) size_t printFloatingPoint(float c, scope ref const FormatSpec spec, scope ref dchar[512] buf)
{
    return printFloatingPoint(cast(double)c, spec, buf);
}

pragma(inline, false) size_t printFloatingPoint(double c, scope ref const FormatSpec spec, scope ref dchar[512] buf)
{
    return printFloatingPointExtend(c, spec, buf);
}

pragma(inline, false) size_t printFloatingPoint(real c, scope ref const FormatSpec spec, scope ref dchar[512] buf)
{
    version (CRuntime_Microsoft)
    {
        return printFloatingPoint(cast(double) c, spec, buf);
    }
    else
    {
        return printFloatingPointExtend(c, spec, buf);
    }
}

nothrow:

pragma(inline, false) size_t printHexadecimal(uint c, ref char[8] buf, bool upper) { return printHexadecimalGen!(uint, char)(c, buf, upper); }
pragma(inline, false) size_t printHexadecimal(ulong c, ref char[16] buf, bool upper) { return printHexadecimalGen!(ulong, char)(c, buf, upper); }
static if (is(ucent))
pragma(inline, false) size_t printHexadecimal(ucent c, ref char[32] buf, bool upper) { return printHexadecimalGen!(ucent, char)(c, buf, upper); }

pragma(inline, false) size_t printHexadecimal(uint c, ref wchar[8] buf, bool upper) { return printHexadecimalGen!(uint, wchar)(c, buf, upper); }
pragma(inline, false) size_t printHexadecimal(ulong c, ref wchar[16] buf, bool upper) { return printHexadecimalGen!(ulong, wchar)(c, buf, upper); }
static if (is(ucent))
pragma(inline, false) size_t printHexadecimal(ucent c, ref wchar[32] buf, bool upper) { return printHexadecimalGen!(ucent, wchar)(c, buf, upper); }

pragma(inline, false) size_t printHexadecimal(uint c, ref dchar[8] buf, bool upper) { return printHexadecimalGen!(uint, dchar)(c, buf, upper); }
pragma(inline, false) size_t printHexadecimal(ulong c, ref dchar[16] buf, bool upper) { return printHexadecimalGen!(ulong, dchar)(c, buf, upper); }
static if (is(ucent))
pragma(inline, false) size_t printHexadecimal(ucent c, ref dchar[32] buf, bool upper) { return printHexadecimalGen!(ucent, dchar)(c, buf, upper); }

size_t printHexadecimalGen(T, C)(T c, ref C[T.sizeof * 2] buf, bool upper) @trusted
{
    if (c < 10)
    {
        buf[0] = cast(char)('0' + c);
        return 1;
    }
    import mir.bitop: ctlz;
    immutable hexString = upper ? hexStringUpper : hexStringLower;
    size_t ret = cast(size_t) ctlz(c);
    ret = (ret >> 2) + ((ret & 3) != 0);
    size_t i = ret;
    do
    {
        buf.ptr[--i] = hexStringUpper[c & 0xF];
        c >>= 4;
    }
    while(i);
    return ret;
}

                      size_t printHexAddress(ubyte c, ref char[2] buf, bool upper) { return printHexAddressGen!(ubyte, char)(c, buf, upper); }
                      size_t printHexAddress(ushort c, ref char[4] buf, bool upper) { return printHexAddressGen!(ushort, char)(c, buf, upper); }
pragma(inline, false) size_t printHexAddress(uint c, ref char[8] buf, bool upper) { return printHexAddressGen!(uint, char)(c, buf, upper); }
pragma(inline, false) size_t printHexAddress(ulong c, ref char[16] buf, bool upper) { return printHexAddressGen!(ulong, char)(c, buf, upper); }
static if (is(ucent))
pragma(inline, false) size_t printHexAddress(ucent c, ref char[32] buf, bool upper) { return printHexAddressGen!(ucent, char)(c, buf, upper); }

                      size_t printHexAddress(ubyte c, ref wchar[2] buf, bool upper) { return printHexAddressGen!(ubyte, wchar)(c, buf, upper); }
                      size_t printHexAddress(ushort c, ref wchar[4] buf, bool upper) { return printHexAddressGen!(ushort, wchar)(c, buf, upper); }
pragma(inline, false) size_t printHexAddress(uint c, ref wchar[8] buf, bool upper) { return printHexAddressGen!(uint, wchar)(c, buf, upper); }
pragma(inline, false) size_t printHexAddress(ulong c, ref wchar[16] buf, bool upper) { return printHexAddressGen!(ulong, wchar)(c, buf, upper); }
static if (is(ucent))
pragma(inline, false) size_t printHexAddress(ucent c, ref wchar[32] buf, bool upper) { return printHexAddressGen!(ucent, wchar)(c, buf, upper); }

                      size_t printHexAddress(ubyte c, ref dchar[2] buf, bool upper) { return printHexAddressGen!(ubyte, dchar)(c, buf, upper); }
                      size_t printHexAddress(ushort c, ref dchar[4] buf, bool upper) { return printHexAddressGen!(ushort, dchar)(c, buf, upper); }
pragma(inline, false) size_t printHexAddress(uint c, ref dchar[8] buf, bool upper) { return printHexAddressGen!(uint, dchar)(c, buf, upper); }
pragma(inline, false) size_t printHexAddress(ulong c, ref dchar[16] buf, bool upper) { return printHexAddressGen!(ulong, dchar)(c, buf, upper); }
static if (is(ucent))
pragma(inline, false) size_t printHexAddress(ucent c, ref dchar[32] buf, bool upper) { return printHexAddressGen!(ucent, dchar)(c, buf, upper); }

size_t printHexAddressGen(T, C)(T c, ref C[T.sizeof * 2] buf, bool upper)
{
    static if (T.sizeof == 16)
    {
        printHexAddress(cast(ulong)(c >> 64), buf[0 .. 16], upper);
        printHexAddress(cast(ulong) c, buf[16 .. 32], upper);
    }
    else
    {
        immutable hexString = upper ? hexStringUpper : hexStringLower;
        foreach_reverse(ref e; buf)
        {
            e = hexStringUpper[c & 0xF];
            c >>= 4;
        }
    }
    return buf.length;
}

static immutable hexStringUpper = "0123456789ABCDEF";
static immutable hexStringLower = "0123456789abcdef";

pragma(inline, false) size_t printBufferShift(size_t length, size_t shift, scope char* ptr) { return printBufferShiftGen!char(length, shift, ptr); }
pragma(inline, false) size_t printBufferShift(size_t length, size_t shift, scope wchar* ptr) { return printBufferShiftGen!wchar(length, shift, ptr); }
pragma(inline, false) size_t printBufferShift(size_t length, size_t shift, scope dchar* ptr) { return printBufferShiftGen!dchar(length, shift, ptr); }

size_t printBufferShiftGen(C)(size_t length, size_t shift, scope C* ptr) @trusted
{
    size_t i;
    do ptr[i] = ptr[shift + i];
    while(++i < length);
    return length;
}

pragma(inline, false) size_t printSigned(int c, scope ref char[11] buf, char sign = '\0') { return printSignedGen(c, buf, sign); }
pragma(inline, false) size_t printSigned(long c, scope ref char[21] buf, char sign = '\0') { return printSignedGen(c, buf, sign); }
static if (is(cent))
pragma(inline, false) size_t printSigned(cent c, scope ref char[40] buf, char sign = '\0') { return printSignedGen(c, buf, sign); }

pragma(inline, false) size_t printSigned(int c, scope ref wchar[11] buf, wchar sign = '\0') { return printSignedGen(c, buf, sign); }
pragma(inline, false) size_t printSigned(long c, scope ref wchar[21] buf, wchar sign = '\0') { return printSignedGen(c, buf, sign); }
static if (is(cent))
pragma(inline, false) size_t printSigned(cent c, scope ref wchar[40] buf, wchar sign = '\0') { return printSignedGen(c, buf, sign); }

pragma(inline, false) size_t printSigned(int c, scope ref dchar[11] buf, dchar sign = '\0') { return printSignedGen(c, buf, sign); }
pragma(inline, false) size_t printSigned(long c, scope ref dchar[21] buf, dchar sign = '\0') { return printSignedGen(c, buf, sign); }
static if (is(cent))
pragma(inline, false) size_t printSigned(cent c, scope ref dchar[40] buf, dchar sign = '\0') { return printSignedGen(c, buf, sign); }


pragma(inline, false) size_t printSignedToTail(int c, scope ref char[11] buf, char sign = '\0') { return printSignedToTailGen(c, buf, sign); }
pragma(inline, false) size_t printSignedToTail(long c, scope ref char[21] buf, char sign = '\0') { return printSignedToTailGen(c, buf, sign); }
static if (is(cent))
pragma(inline, false) size_t printSignedToTail(cent c, scope ref char[40] buf, char sign = '\0') { return printSignedToTailGen(c, buf, sign); }

pragma(inline, false) size_t printSignedToTail(int c, scope ref wchar[11] buf, wchar sign = '\0') { return printSignedToTailGen(c, buf, sign); }
pragma(inline, false) size_t printSignedToTail(long c, scope ref wchar[21] buf, wchar sign = '\0') { return printSignedToTailGen(c, buf, sign); }
static if (is(cent))
pragma(inline, false) size_t printSignedToTail(cent c, scope ref wchar[40] buf, wchar sign = '\0') { return printSignedToTailGen(c, buf, sign); }

pragma(inline, false) size_t printSignedToTail(int c, scope ref dchar[11] buf, dchar sign = '\0') { return printSignedToTailGen(c, buf, sign); }
pragma(inline, false) size_t printSignedToTail(long c, scope ref dchar[21] buf, dchar sign = '\0') { return printSignedToTailGen(c, buf, sign); }
static if (is(cent))
pragma(inline, false) size_t printSignedToTail(cent c, scope ref dchar[40] buf, dchar sign = '\0') { return printSignedToTailGen(c, buf, sign); }

size_t printSignedGen(T, C, size_t N)(T c, scope ref C[N] buf, C sign) @trusted
{
    auto ret = printSignedToTail(c, buf, sign);
    if (auto shift =  buf.length - ret)
    {
        return printBufferShift(ret, shift, buf[].ptr);
    }
    return ret;
}

size_t printSignedToTailGen(T, C, size_t N)(T c, scope ref C[N] buf, C sign)
{
    if (c < 0)
    {
        sign = '-';
        c = -c;
    }

    auto ret = printUnsignedToTail(c, buf[1 .. N]);

    if (sign != '\0')
    {
        buf[$ - ++ret] = sign;
    }
    return ret;
}

pragma(inline, false) size_t printUnsigned(uint c, scope ref char[10] buf) { return printUnsignedGen(c, buf); }
pragma(inline, false) size_t printUnsigned(ulong c, scope ref char[20] buf) { return printUnsignedGen(c, buf); }
static if (is(ucent))
pragma(inline, false) size_t printUnsigned(ucent c, scope ref char[39] buf) { return printUnsignedGen(c, buf); }

pragma(inline, false) size_t printUnsigned(uint c, scope ref wchar[10] buf) { return printUnsignedGen(c, buf); }
pragma(inline, false) size_t printUnsigned(ulong c, scope ref wchar[20] buf) { return printUnsignedGen(c, buf); }
static if (is(ucent))
pragma(inline, false) size_t printUnsigned(ucent c, scope ref wchar[39] buf) { return printUnsignedGen(c, buf); }

pragma(inline, false) size_t printUnsigned(uint c, scope ref dchar[10] buf) { return printUnsignedGen(c, buf); }
pragma(inline, false) size_t printUnsigned(ulong c, scope ref dchar[20] buf) { return printUnsignedGen(c, buf); }
static if (is(ucent))
pragma(inline, false) size_t printUnsigned(ucent c, scope ref dchar[39] buf) { return printUnsignedGen(c, buf); }

pragma(inline, false) size_t printUnsignedToTail(uint c, scope ref char[10] buf) { return printUnsignedToTailGen(c, buf); }
pragma(inline, false) size_t printUnsignedToTail(ulong c, scope ref char[20] buf) { return printUnsignedToTailGen(c, buf); }
static if (is(ucent))
pragma(inline, false) size_t printUnsignedToTail(ucent c, scope ref char[39] buf) { return printUnsignedToTailGen(c, buf); }

pragma(inline, false) size_t printUnsignedToTail(uint c, scope ref wchar[10] buf) { return printUnsignedToTailGen(c, buf); }
pragma(inline, false) size_t printUnsignedToTail(ulong c, scope ref wchar[20] buf) { return printUnsignedToTailGen(c, buf); }
static if (is(ucent))
pragma(inline, false) size_t printUnsignedToTail(ucent c, scope ref wchar[39] buf) { return printUnsignedToTailGen(c, buf); }

pragma(inline, false) size_t printUnsignedToTail(uint c, scope ref dchar[10] buf) { return printUnsignedToTailGen(c, buf); }
pragma(inline, false) size_t printUnsignedToTail(ulong c, scope ref dchar[20] buf) { return printUnsignedToTailGen(c, buf); }
static if (is(ucent))
pragma(inline, false) size_t printUnsignedToTail(ucent c, scope ref dchar[39] buf) { return printUnsignedToTailGen(c, buf); }

size_t printUnsignedToTailGen(T, C, size_t N)(T c, scope ref C[N] buf) @trusted
{
    static if (T.sizeof == 4)
    {
        if (c < 10)
        {
            buf[$ - 1] = cast(char)('0' + c);
            return 1;
        }
        static assert(N == 10);
    }
    else
    static if (T.sizeof == 8)
    {
        if (c <= uint.max)
        {
            return printUnsignedToTail(cast(uint)c, buf[$ - 10 .. $]);
        }
        static assert(N == 20);
    }
    else
    static if (T.sizeof == 16)
    {
        if (c <= ulong.max)
        {
            return printUnsignedToTail(cast(ulong)c, buf[$ - 20 .. $]);
        }
        static assert(N == 39);
    }
    else
    static assert(0);
    size_t refLen = buf.length;
    do {
        T nc = c / 10;
        buf[].ptr[--refLen] = cast(C)('0' + c - nc * 10);
        c = nc;
    }
    while(c);
    return buf.length - refLen;
}

size_t printUnsignedGen(T, C, size_t N)(T c, scope ref C[N] buf) @trusted
{
    auto ret = printUnsignedToTail(c, buf);
    if (auto shift =  buf.length - ret)
    {
        return printBufferShift(ret, shift, buf[].ptr);
    }
    return ret;
}

nothrow @trusted
pragma(inline, false) size_t extendASCII(char* from, wchar* to, size_t n)
{
    foreach (i; 0 .. n)
        to[i] = from[i];
    return n;
}

nothrow @trusted
pragma(inline, false) size_t extendASCII(char* from, dchar* to, size_t n)
{
    foreach (i; 0 .. n)
        to[i] = from[i];
    return n;
}

version (mir_test) unittest
{
    import mir.appender;
    import mir.format;

    assert (stringBuf() << 123L << getData == "123");
    static assert (stringBuf() << 123 << getData == "123");
}

ref W printIntegralZeroImpl(C, size_t N, W, I)(scope return ref W w, I c, size_t zeroLen)
{
    static if (__traits(isUnsigned, I))
        alias impl = printUnsignedToTail;
    else
        alias impl = printSignedToTail;
    C[N] buf = void;
    size_t n = impl(c, buf);
    static if (!__traits(isUnsigned, I))
    {
        if (c < 0)
        {
            n--;
            w.put(C('-'));
        }
    }
    sizediff_t zeros = zeroLen - n;
    if (zeros > 0)
    {
        do w.put(C('0'));
        while(--zeros);
    }
    w.put(buf[$ - n ..  $]);
    return w;
}
