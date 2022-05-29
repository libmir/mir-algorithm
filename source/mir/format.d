/++
$(H1 @nogc Formatting Utilities)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko
+/
module mir.format;

import std.traits;
import mir.primitives: isOutputRange;

/// `mir.conv: to` extension.
version(mir_test)
@safe pure @nogc
unittest
{
    import mir.conv: to;
    import mir.small_string;
    alias S = SmallString!32;

    // Floating-point numbers are formatted to
    // the shortest precise exponential notation.
    assert(123.0.to!S == "123.0");
    assert(123.to!(immutable S) == "123");
    assert(true.to!S == "true");
    assert(true.to!string == "true");

    assert((cast(S)"str")[] == "str");
}

/// `mir.conv: to` extension.
version(mir_test)
@safe pure
unittest
{
    import mir.conv: to;
    import mir.small_string;
    alias S = SmallString!32;

    auto str = S("str");
    assert(str.to!(const(char)[]) == "str"); // GC allocated result
    assert(str.to!(char[]) == "str"); // GC allocated result
}

/// ditto
version(mir_test)
@safe pure
unittest
{
    import mir.conv: to;
    import mir.small_string;
    alias S = SmallString!32;

    // Floating-point numbers are formatted to
    // the shortest precise exponential notation.
    assert(123.0.to!string == "123.0");
    assert(123.to!(char[]) == "123");

    assert(S("str").to!string == "str"); // GC allocated result
}

/// Concatenated string results
string text(string separator = "", Args...)(auto ref Args args)
    if (Args.length > 0)
{
    static if (Args.length == 1)
    {
        static if (is(immutable Args[0] == immutable typeof(null)))
        {
            return "null";
        }
        else
        {
            import mir.functional: forward;
            import mir.conv: to;
            return to!string(forward!args);
        }
    }
    else
    {
        import mir.appender: scopedBuffer;
        auto buffer = scopedBuffer!char;
        foreach (i, ref arg; args)
        {
            buffer.print(arg);
            static if (separator.length && i + 1 < args.length)
            {
                buffer.printStaticString!char(separator);
            }
        }
        return buffer.data.idup;
    }
}

///
version(mir_test)
@safe pure nothrow unittest
{
    const i = 100;
    assert(text("str ", true, " ", i, " ", 124.1) == "str true 100 124.1", text("str ", true, " ", 100, " ", 124.1));
    assert(text!" "("str", true, 100, 124.1, null) == "str true 100 124.1 null");
    assert(text(null) == "null", text(null));
}

import mir.format_impl;

///
struct GetData {}

///
enum getData = GetData();

/++
+/
struct StringBuf(C, uint scopeSize = 256)
    if (is(C == char) || is(C == wchar) || is(C == dchar))
{
    import mir.appender: ScopedBuffer;

    ///
    ScopedBuffer!(C, scopeSize) buffer;

    ///
    alias buffer this;

    ///
    mixin StreamFormatOp!C;
}

///ditto
auto stringBuf(C = char, uint scopeSize = 256)()
    @trusted pure nothrow @nogc @property
    if (is(C == char) || is(C == wchar) || is(C == dchar))
{
    StringBuf!(C, scopeSize) buffer = void;
    buffer.initialize;
    return buffer;
}

/++
+/
mixin template StreamFormatOp(C)
{
    ///
    ref typeof(this) opBinary(string op : "<<", T)(ref const T c) scope
    {
        return print!C(this, c);
    }

    ///
    ref typeof(this) opBinary(string op : "<<", T)(const T c) scope
    {
        return print!C(this, c);
    }

    /// ditto
    const(C)[] opBinary(string op : "<<", T : GetData)(const T c) scope
    {
        return buffer.data;
    }
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto name = "D";
    auto ver = 2.0;
    assert(stringBuf << "Hi " << name << ver << "!\n" << getData == "Hi D2.0!\n");
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto name = "D"w;
    auto ver = 2;
    assert(stringBuf!wchar << "Hi "w << name << ver << "!\n"w << getData == "Hi D2!\n"w);
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto name = "D"d;
    auto ver = 2UL;
    assert(stringBuf!dchar << "Hi "d  << name << ver << "!\n"d << getData == "Hi D2!\n"d);
}

@safe pure nothrow @nogc
version (mir_test) unittest
{
    assert(stringBuf << -1234567890 << getData == "-1234567890");
}

/++
Mir's numeric format specification

Note: the specification isn't complete an may be extended in the future.
+/
struct NumericSpec
{
    ///
    enum Format
    {
        /++
        Human-frindly precise output.
        Examples: `0.000001`, `600000.0`, but `1e-7` and `6e7`.
        +/
        human,
        /++
        Precise output with explicit exponent.
        Examples: `1e-6`, `6e6`, `1.23456789e-100`.
        +/
        exponent,
    }

    ///
    Format format;

    /// Default valus is '\0' (no separators)
    char separatorChar = '\0';

    /// Defaults to 'e'
    char exponentChar = 'e';

    /// Adds '+' to positive numbers and `+0`.
    bool plus;

    /// Separator count
    ubyte separatorCount = 3;

    /++
    Precise output with explicit exponent.
    Examples: `1e-6`, `6e6`, `1.23456789e-100`.
    +/
    enum NumericSpec exponent = NumericSpec(Format.exponent);

    /++
    Human-frindly precise output.
    +/
    enum NumericSpec human = NumericSpec(Format.human);
}

// 16-bytes
/// C's compatible format specifier.
struct FormatSpec
{
    ///
    bool dash;
    ///
    bool plus;
    ///
    bool space;
    ///
    bool hash;
    ///
    bool zero;
    ///
    char format = 's';
    ///
    char separator = '\0';
    ///
    ubyte unitSize;
    ///
    int width;
    ///
    int precision = -1;
}

/++
+/
enum SwitchLU : bool
{
    ///
    lower,
    ///
    upper,
}

/++
Wrapper to format floating point numbers using C's library.
+/
struct FormattedFloating(T)
    if(is(T == float) || is(T == double) || is(T == real))
{
    ///
    T value;
    ///
    FormatSpec spec;

    ///
    void toString(C = char, W)(scope ref W w) scope const
    if (isSomeChar!C)
    {
        C[512] buf = void;
        auto n = printFloatingPoint(value, spec, buf);
        w.put(buf[0 ..  n]);
    }
}

/// ditto
FormattedFloating!T withFormat(T)(const T value, FormatSpec spec)
{
    version(LDC) pragma(inline);
    return typeof(return)(value, spec);
}

/++
+/
struct HexAddress(T)
    if (isUnsigned!T && !is(T == enum))
{
    ///
    T value;
    ///
    SwitchLU switchLU = SwitchLU.upper;

    ///
    void toString(C = char, W)(scope ref W w) scope const
        if (isSomeChar!C)
    {
        enum N = T.sizeof * 2;
        static if(isFastBuffer!W)
        {
            w.advance(printHexAddress(value, w.getStaticBuf!N, cast(bool) switchLU));
        }
        else
        {
            C[N] buf = void;
            printHexAddress(value, buf, cast(bool) switchLU);
            w.put(buf[]);
        }
    }
}

/++
Escaped string formats
+/
enum EscapeFormat
{
    /// JSON escaped string format
    json,
    /// Amzn Ion CLOB format
    ionClob,
    /// Amzn Ion symbol format
    ionSymbol,
    /// Amzn Ion string format
    ion,
}

enum escapeFormatQuote(EscapeFormat escapeFormat) = escapeFormat == EscapeFormat.ionSymbol ? '\'' : '\"';

/++
+/
ref W printEscaped(C, EscapeFormat escapeFormat = EscapeFormat.ion, W)(scope return ref W w, scope const(C)[] str)
    if (isOutputRange!(W, C))
{
    import mir.utility: _expect;
    foreach (C c; str)
    {
        if (_expect(c == escapeFormatQuote!escapeFormat || c == '\\', false))
            goto E;
        if (_expect(c < ' ', false))
            goto C;
        static if (escapeFormat == EscapeFormat.ionClob)
        {
            if (c >= 127)
                goto A;
        }
    P:
        w.put(c);
        continue;
    E:
        {
            C[2] pair;
            pair[0] = '\\';
            pair[1] = c;
            w.printStaticString!C(pair);
            continue;
        }
    C:
        switch (c)
        {
            static if (escapeFormat != EscapeFormat.json)
            {
                case '\0':
                    c = '0';
                    goto E;
                case '\a':
                    c = 'a';
                    goto E;
                case '\v':
                    c = 'v';
                    goto E;
            }
            case '\b':
                c = 'b';
                goto E;
            case '\t':
                c = 't';
                goto E;
            case '\n':
                c = 'n';
                goto E;
            case '\f':
                c = 'f';
                goto E;
            case '\r':
                c = 'r';
                goto E;
            default:
    A:
                static if (escapeFormat == EscapeFormat.json)
                    put_uXXXX!C(w, cast(char)c);
                else
                    put_xXX!C(w, cast(char)c);
        }
    }
    return w;
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    import mir.format: stringBuf;
    auto w = stringBuf;
    assert(w.printEscaped("Hi \a\v\0\f\t\b \\\r\n" ~ `"@nogc"`).data == `Hi \a\v\0\f\t\b \\\r\n\"@nogc\"`);
    w.reset;
    assert(w.printEscaped("\x03").data == `\x03`);
}

/++
Decodes `char` `c` to the form `u00XX`, where `XX` is 2 hexadecimal characters.
+/
ref W put_xXX(C = char, W)(scope return ref W w, char c)
    if (isSomeChar!C)
{
    ubyte[2] spl;
    spl[0] = c >> 4;
    spl[1] = c & 0xF;
    C[4] buffer;
    buffer[0] = '\\';
    buffer[1] = 'x';
    buffer[2] = cast(ubyte)(spl[0] < 10 ? spl[0] + '0' : spl[0] - 10 + 'A');
    buffer[3] = cast(ubyte)(spl[1] < 10 ? spl[1] + '0' : spl[1] - 10 + 'A');
    return w.printStaticString(buffer);
}

/++
Decodes `char` `c` to the form `u00XX`, where `XX` is 2 hexadecimal characters.
+/
ref W put_uXXXX(C = char, W)(scope return ref W w, char c)
    if (isSomeChar!C)
{
    ubyte[2] spl;
    spl[0] = c >> 4;
    spl[1] = c & 0xF;
    C[6] buffer;
    buffer[0] = '\\';
    buffer[1] = 'u';
    buffer[2] = '0';
    buffer[3] = '0';
    buffer[4] = cast(ubyte)(spl[0] < 10 ? spl[0] + '0' : spl[0] - 10 + 'A');
    buffer[5] = cast(ubyte)(spl[1] < 10 ? spl[1] + '0' : spl[1] - 10 + 'A');
    return w.printStaticString(buffer);
}

/++
Decodes ushort `c` to the form `uXXXX`, where `XXXX` is 2 hexadecimal characters.
+/
ref W put_uXXXX(C = char, W)(scope return ref W w, ushort c)
    if (isSomeChar!C)
{
    ubyte[4] spl;
    spl[0] = (c >> 12) & 0xF;
    spl[1] = (c >> 8) & 0xF;
    spl[2] = (c >> 4) & 0xF;
    spl[3] = c & 0xF;
    C[6] buffer;
    buffer[0] = '\\';
    buffer[1] = 'u';
    buffer[2] = cast(ubyte)(spl[0] < 10 ? spl[0] + '0' : spl[0] - 10 + 'A');
    buffer[3] = cast(ubyte)(spl[1] < 10 ? spl[1] + '0' : spl[1] - 10 + 'A');
    buffer[4] = cast(ubyte)(spl[2] < 10 ? spl[2] + '0' : spl[2] - 10 + 'A');
    buffer[5] = cast(ubyte)(spl[3] < 10 ? spl[3] + '0' : spl[3] - 10 + 'A');
    return w.printStaticString(buffer);
}

///
ref W printElement(C, EscapeFormat escapeFormat = EscapeFormat.ion, W)(scope return ref W w, scope const(C)[] c)
    if (isSomeChar!C)
{
    static immutable C[1] quote = '\"';
    return w
        .printStaticString!C(quote)
        .printEscaped!(C, escapeFormat)(c)
        .printStaticString!C(quote);
}

///
ref W printElement(C = char, EscapeFormat escapeFormat = EscapeFormat.ion, W, T)(scope return ref W w, scope auto ref const T c)
    if (!isSomeString!T)
{
    return w.print!C(c);
}

/++
Multiargument overload.
+/
ref W print(C = char, W, Args...)(scope return ref W w, scope auto ref const Args args)
    if (isSomeChar!C && Args.length > 1)
{
    foreach(i, ref c; args)
        static if (i < Args.length - 1)
            w.print!C(c);
        else
            return w.print!C(c);
}

/// Prints enums
ref W print(C = char, W, T)(scope return ref W w, const T c)
    if (isSomeChar!C && is(T == enum))
{
    import mir.enums: getEnumIndex, enumStrings;
    import mir.utility: _expect;

    static assert(!is(OriginalType!T == enum));
    uint index = void;
    if (getEnumIndex(c, index)._expect(true))
    {
        w.put(enumStrings!T[index]);
        return w;
    }
    static immutable C[] str = T.stringof ~ "(";
    w.put(str[]);
    print!C(w, cast(OriginalType!T) c);
    w.put(')');
    return w;
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    enum Flag
    {
        no,
        yes,
    }

    import mir.appender: scopedBuffer;
    auto w = scopedBuffer!char;
    w.print(Flag.yes);
    assert(w.data == "yes");
}

/// Prints boolean
ref W print(C = char, W)(scope return ref W w, bool c)
    if (isSomeChar!C)
{
    enum N = 5;
    static if(isFastBuffer!W)
    {
        w.advance(printBoolean(c, w.getStaticBuf!N));
    }
    else
    {
        C[N] buf = void;
        auto n = printBoolean(c, buf);
        w.put(buf[0 .. n]);
    }
    return w;
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    import mir.appender: scopedBuffer;
    auto w = scopedBuffer!char;
    assert(w.print(true).data == `true`);
    w.reset;
    assert(w.print(false).data == `false`);
}

/// Prints associative array
pragma(inline, false)
ref W print(C = char, W, V, K)(scope return ref W w, scope const V[K] c)
    if (isSomeChar!C)
{
    enum C left = '[';
    enum C right = ']';
    enum C[2] sep = ", ";
    enum C[2] mid = ": ";
    w.put(left);
    bool first = true;
    foreach (ref key, ref value; c)
    {
        if (!first)
            w.printStaticString!C(sep);
        first = false;
        w
            .printElement!C(key)
            .printStaticString!C(mid)
            .printElement!C(value);
    }
    w.put(right);
    return w;
}

///
@safe pure
version (mir_test) unittest
{
    import mir.appender: scopedBuffer;
    auto w = scopedBuffer!char;
    w.print(["a": 1, "b": 2]);
    assert(w.data == `["a": 1, "b": 2]` || w.data == `["b": 2, "a": 1]`);
}

/// Prints null
ref W print(C = char, W, V)(scope return ref W w, const V c)
    if (is(V == typeof(null)))
{
    enum C[4] Null = "null";
    return w.printStaticString!C(Null);
}

///
@safe pure @nogc
version (mir_test) unittest
{
    import mir.appender: scopedBuffer;
    auto w = scopedBuffer!char;
    w.print(null);
    assert(w.data == `null`);
}

/// Prints array
pragma(inline, false)
ref W print(C = char, W, T)(scope return ref W w, scope const(T)[] c)
    if (isSomeChar!C && !isSomeChar!T)
{
    enum C left = '[';
    enum C right = ']';
    enum C[2] sep = ", ";
    w.put(left);
    bool first = true;
    foreach (ref e; c)
    {
        if (!first)
            w.printStaticString!C(sep);
        first = false;
        printElement!C(w, e);
    }
    w.put(right);
    return w;
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    import mir.appender: scopedBuffer;
    auto w = scopedBuffer!char;
    string[2] array = ["a\na", "b"];
    assert(w.print(array[]).data == `["a\na", "b"]`);
}

/// Prints escaped character in the form `'c'`.
pragma(inline, false)
ref W print(C = char, W)(scope return ref W w, char c)
    if (isSomeChar!C)
{
    w.put('\'');
    if (c >= 0x20)
    {
        if (c < 0x7F)
        {
            if (c == '\'' || c == '\\')
            {
            L:
                w.put('\\');
            }
            w.put(c);
        }
        else
        {
        M:
            w.printStaticString!C(`\x`);
            w.print!C(HexAddress!ubyte(cast(ubyte)c));
        }
    }
    else
    {
        switch(c)
        {
            case '\n': c = 'n'; goto L;
            case '\r': c = 'r'; goto L;
            case '\t': c = 't'; goto L;
            case '\a': c = 'a'; goto L;
            case '\b': c = 'b'; goto L;
            case '\f': c = 'f'; goto L;
            case '\v': c = 'v'; goto L;
            case '\0': c = '0'; goto L;
            default: goto M;
        }
    }
    w.put('\'');
    return w;
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    import mir.appender: scopedBuffer;
    auto w = scopedBuffer!char;
    assert(w
        .print('\n')
        .print('\'')
        .print('a')
        .print('\xF4')
        .data == `'\n''\'''a''\xF4'`);
}

/// Prints some string
ref W print(C = char, W)(scope return ref W w, scope const(C)[] c)
    if (isSomeChar!C)
{
    w.put(c);
    return w;
}

/// Prints integers
ref W print(C = char, W, I)(scope return ref W w, const I c)
    if (isSomeChar!C && isIntegral!I && !is(I == enum))
{
    static if (I.sizeof == 16)
        enum N = 39;
    else
    static if (I.sizeof == 8)
        enum N = 20;
    else
        enum N = 10;
    C[N + !__traits(isUnsigned, I)] buf = void;
    static if (__traits(isUnsigned, I))
        auto n = printUnsignedToTail(c, buf);
    else
        auto n = printSignedToTail(c, buf);
    w.put(buf[$ - n ..  $]);
    return w;
}

/// Prints floating point numbers
ref W print(C = char, W, T)(scope return ref W w, const T c, NumericSpec spec = NumericSpec.init)
    if(isSomeChar!C && is(T == float) || is(T == double) || is(T == real))
{
    import mir.bignum.decimal;
    auto decimal = Decimal!(T.mant_dig < 64 ? 1 : 2)(c);
    decimal.toString(w, spec);
    return w;
}

/// Human friendly precise output (default)
version(mir_bignum_test)
@safe pure nothrow @nogc
unittest
{
    auto spec = NumericSpec.human;
    auto buffer = stringBuf;

    void check(double num, string value)
    {
        assert(buffer.print(num, spec).data == value, value);
        buffer.reset;
    }

    check(-0.0, "-0.0");
    check(0.0, "0.0");
    check(-0.01, "-0.01");
    check(0.0125, "0.0125");
    check(0.000003, "0.000003");
    check(-3e-7, "-3e-7");
    check(123456.0, "123456.0");
    check(123456.1, "123456.1");
    check(12.3456, "12.3456");
    check(-0.123456, "-0.123456");
    check(0.1234567, "0.1234567");
    check(0.01234567, "0.01234567");
    check(0.001234567, "0.001234567");
    check(1.234567e-4, "1.234567e-4");
    check(-1234567.0, "-1.234567e+6");
    check(123456.7890123, "123456.7890123");
    check(1234567.890123, "1.234567890123e+6");
    check(1234567890123.0, "1.234567890123e+12");
    check(0.30000000000000004, "0.30000000000000004");
    check(0.030000000000000002, "0.030000000000000002");
    check(0.0030000000000000005, "0.0030000000000000005");
    check(3.0000000000000003e-4, "3.0000000000000003e-4");
    check(+double.nan, "nan");
    check(-double.nan, "nan");
    check(+double.infinity, "+inf");
    check(-double.infinity, "-inf");

    spec.separatorChar = ',';

    check(-0.0, "-0.0");
    check(0.0, "0.0");
    check(-0.01, "-0.01");
    check(0.0125, "0.0125");
    check(0.000003, "0.000003");
    check(-3e-7, "-3e-7");
    check(123456.0, "123,456.0");
    check(123456e5, "12,345,600,000.0");
    check(123456.1, "123,456.1");
    check(12.3456, "12.3456");
    check(-0.123456, "-0.123456");
    check(0.1234567, "0.1234567");
    check(0.01234567, "0.01234567");
    check(0.001234567, "0.001234567");
    check(1.234567e-4, "0.0001234567");
    check(-1234567.0, "-1,234,567.0");
    check(123456.7890123, "123,456.7890123");
    check(1234567.890123, "1,234,567.890123");
    check(123456789012.0, "123,456,789,012.0");
    check(1234567890123.0, "1.234567890123e+12");
    check(0.30000000000000004, "0.30000000000000004");
    check(0.030000000000000002, "0.030000000000000002");
    check(0.0030000000000000005, "0.0030000000000000005");
    check(3.0000000000000003e-4, "0.00030000000000000003");
    check(3.0000000000000005e-6, "0.0000030000000000000005");
    check(3.0000000000000004e-7, "3.0000000000000004e-7");
    check(+double.nan, "nan");
    check(-double.nan, "nan");
    check(+double.infinity, "+inf");
    check(-double.infinity, "-inf");

    spec.separatorChar = '_';
    spec.separatorCount = 2;
    check(123456e5, "1_23_45_60_00_00.0");

    spec.plus = true;
    check(0.0125, "+0.0125");
    check(-0.0125, "-0.0125");
}

/// Prints structs and unions
pragma(inline, false)
ref W print(C = char, W, T)(scope return ref W w, ref const T c)
    if (isSomeChar!C && is(T == struct) || is(T == union) && !is(T : NumericSpec))
{
    static if (__traits(hasMember, T, "toString"))
    {
        static if (is(typeof(c.toString!C(w))))
            c.toString!C(w);
        else
        static if (is(typeof(c.toString(w))))
            c.toString(w);
        else
        static if (is(typeof(c.toString((scope const(C)[] s) { w.put(s); }))))
            c.toString((scope const(C)[] s) { w.put(s); });
        else
        static if (is(typeof(w.put(c.toString))))
            w.put(c.toString);
        else static assert(0, T.stringof ~ ".toString definition is wrong: 'const' qualifier may be missing.");
        return w;
    }
    else
    static if (__traits(compiles, { scope const(C)[] string_of_c = c; }))
    {
        scope const(C)[] string_of_c = c;
        return w.print!C(string_of_c);
    }
    else
    static if (hasIterableLightConst!T)
    {
        enum C left = '[';
        enum C right = ']';
        enum C[2] sep = ", ";
        w.put(left);
        bool first = true;
        foreach (ref e; c.lightConst)
        {
            if (!first)
                printStaticString!C(w, sep);
            first = false;
            print!C(w, e);
        }
        w.put(right);
        return w;
    }
    else
    {
        enum C left = '(';
        enum C right = ')';
        enum C[2] sep = ", ";
        w.put(left);
        foreach (i, ref e; c.tupleof)
        {
            static if (i)
                w.printStaticString!C(sep);
            print!C(w, e);
        }
        w.put(right);
        return w;
    }
}

/// ditto
// FUTURE: remove it
pragma(inline, false)
ref W print(C = char, W, T)(scope return ref W w, scope const T c)
    if (isSomeChar!C && is(T == struct) || is(T == union))
{
    return print!(C, W, T)(w, c);
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    static struct A { scope void toString(C, W)(scope ref W w) const { w.put(C('a')); } }
    static struct S { scope void toString(W)(scope ref W w) const { w.put("s"); } }
    static struct D { scope void toString(Dg)(scope Dg sink) const { sink("d"); } }
    static struct F { scope const(char)[] toString()() const return { return "f"; } }
    static struct G { const(char)[] s = "g"; alias s this; }

    import mir.appender: scopedBuffer;
    auto w = scopedBuffer!char;
    assert(stringBuf << A() << S() << D() << F() << G() << getData == "asdfg");
}

/// Prints classes and interfaces
pragma(inline, false)
ref W print(C = char, W, T)(scope return ref W w, scope const T c)
    if (isSomeChar!C && is(T == class) || is(T == interface))
{
    static if (__traits(hasMember, T, "toString") || __traits(compiles, { scope const(C)[] string_of_c = c; }))
    {
        if (c is null)
            return w.print(null);
        else
        static if (is(typeof(c.toString!C(w))))
        {
            c.toString!C(w);
            return w;
        }
        else
        static if (is(typeof(c.toString(w))))
        {
            c.toString(w);
            return w;
        }
        else
        static if (is(typeof(c.toString((scope const(C)[] s) { w.put(s); }))))
        {
            c.toString((scope const(C)[] s) { w.put(s); });
            return w;
        }
        else
        static if (is(typeof(w.put(c.toString))))
        {
            w.put(c.toString);
            return w;
        }
        else
        static if (__traits(compiles, { scope const(C)[] string_of_c = c; }))
        {
            scope const(C)[] string_of_c = c;
            return w.print!C(string_of_c);
        }
        else static assert(0, T.stringof ~ ".toString definition is wrong: 'const scope' qualifier may be missing.");
    }
    else
    static if (hasIterableLightConst!T)
    {
        enum C left = '[';
        enum C right = ']';
        enum C[2] sep = ", ";
        w.put(left);
        bool first = true;
        foreach (ref e; c.lightConst)
        {
            if (!first)
                w.printStaticString!C(sep);
            first = false;
            print!C(w, e);
        }
        w.put(right);
        return w;
    }
    else
    {
        w.put(T.stringof);
        return w;
    }
}

///
@safe pure nothrow
version (mir_test) unittest
{
    static class A { void toString(C, W)(scope ref W w) const { w.put(C('a')); } }
    static class S { void toString(W)(scope ref W w) const { w.put("s"); } }
    static class D { void toString(Dg)(scope Dg sink) const { sink("d"); } }
    static class F { const(char)[] toString()() const return { return "f"; } }
    static class G { const(char)[] s = "g"; alias s this; }

    assert(stringBuf << new A() << new S() << new D() << new F() << new G() << getData == "asdfg");
}

///
ref W printStaticString(C, size_t N, W)(scope return ref W w, ref scope const C[N] c)
    if (isSomeChar!C && is(C == char) || is(C == wchar) || is(C == dchar))
{
    static if (isFastBuffer!W)
    {
        enum immutable(ForeachType!(typeof(w.getBuffer(size_t.init))))[] value = c;
        w.getStaticBuf!(value.length) = value;
        w.advance(c.length);
    }
    else
    {
        w.put(c[]);
    }
    return w;
}

private template hasIterableLightConst(T)
{
    static if (__traits(hasMember, T, "lightConst"))
    {
        enum hasIterableLightConst = isIterable!(ReturnType!((const T t) => t.lightConst));
    }
    else
    {
        enum hasIterableLightConst = false;
    }
}

private ref C[N] getStaticBuf(size_t N, C, W)(scope return ref W w)
    if (isFastBuffer!W)
{
    auto buf = w.getBuffer(N);
    assert(buf.length >= N);
    return buf.ptr[0 .. N];
}

private @trusted ref C[N] getStaticBuf(size_t N, C)(scope return ref C[] buf)
{
    assert(buf.length >= N);
    return buf.ptr[0 .. N];
}

template isFastBuffer(W)
{
    enum isFastBuffer = __traits(hasMember, W, "getBuffer") && __traits(hasMember, W, "advance");
}

///
ref W printZeroPad(C = char, W, I)(scope return ref W w, const I c, size_t minimalLength)
    if (isSomeChar!C && isIntegral!I && !is(I == enum))
{
    static if (I.sizeof == 16)
        enum N = 39;
    else
    static if (I.sizeof == 8)
        enum N = 20;
    else
        enum N = 10;
    C[N + !__traits(isUnsigned, I)] buf = void;
    static if (__traits(isUnsigned, I))
        auto n = printUnsignedToTail(c, buf);
    else
        auto n = printSignedToTail(c, buf);
    sizediff_t zeros = minimalLength - n;

    if (zeros > 0)
    {
        static if (!__traits(isUnsigned, I))
        {
            if (c < 0)
            {
                n--;
                w.put(C('-'));
            }
        }
        do w.put(C('0'));
        while(--zeros);
    }
    w.put(buf[$ - n ..  $]);
    return w;
}

///
version (mir_test) unittest
{
    import mir.appender;
    auto w = scopedBuffer!char;

    w.printZeroPad(-123, 5);
    w.put(' ');
    w.printZeroPad(123, 5);

    assert(w.data == "-0123 00123");
}

///
size_t printBoolean(C)(bool c, ref C[5] buf)
    if(is(C == char) || is(C == wchar) || is(C == dchar))
{
    version(LDC) pragma(inline, true);
    if (c)
    {
        buf[0] = 't';
        buf[1] = 'r';
        buf[2] = 'u';
        buf[3] = 'e';
        return 4;
    }
    else
    {
        buf[0] = 'f';
        buf[1] = 'a';
        buf[2] = 'l';
        buf[3] = 's';
        buf[4] = 'e';
        return 5;
    }
}
