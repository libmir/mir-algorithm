/++
$(H1 @nogc Formatting Utilities)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors:   Ilya Yaroshenko
+/
module mir.format;

/// `mir.conv: to` extension.
version(mir_test)
@safe pure @nogc
unittest
{
    import mir.conv: to;
    import mir.small_string;
    alias S = SmallString!32;

    assert(123.0.to!S == "123");
    assert(123.to!(immutable S) == "123");
    assert(true.to!S == "true");
    assert(true.to!string == "true");

    assert((cast(S)"str")[] == "str");

    assert(S("str").to!(const(char)[]) == "str"); // scope result
    assert(S("str").to!(char[]) == "str"); // scope result
}

/// ditto
version(mir_test)
@safe pure
unittest
{
    import mir.conv: to;
    import mir.small_string;
    alias S = SmallString!32;

    assert(123.0.to!string == "123");
    assert(123.to!(char[]) == "123");

    assert(S("str").to!string == "str"); // GC allocated result
}

import std.traits;

/// Concatenated string results
string text(string separator = "", A...)(auto ref A args)
        if (A.length > 0)
{
    static if (A.length == 1)
    {
        import mir.functional: forward;
        import mir.conv: to;
        return to!string(forward!args);
    }
    else
    {
        import mir.appender: ScopedBuffer;
        ScopedBuffer!char buffer;
        foreach (i, ref arg; args)
        {
            buffer.print(arg);
            static if (separator.length && i + 1 < args.length)
                buffer.printStaticStringInternal!(char, separator);
        }
        return buffer.data.idup;
    }
}

///
@safe pure nothrow unittest
{
    assert(text("str ", true, " ", 100, " ", 124.1) == "str true 100 124.1");
    assert(text!" "("str", true, 100, 124.1) == "str true 100 124.1");
}

import mir.format_impl;

///
struct GetData {}

///
enum getData = GetData();

/++
+/
struct _stringBuf(C)
{
    import mir.appender: ScopedBuffer;

    ///
    ScopedBuffer!C buffer;

    ///
    alias buffer this;

    ///
    mixin StreamFormatOp!C;
}

///ditto
alias stringBuf = _stringBuf!char;
///ditto
alias wstringBuf = _stringBuf!wchar;
///ditto
alias dstringBuf = _stringBuf!dchar;

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
    assert(stringBuf() << "Hi " << name << ver << "!\n" << getData == "Hi D2!\n");
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto name = "D"w;
    auto ver = 2;
    assert(wstringBuf() << "Hi "w << name << ver << "!\n"w << getData == "Hi D2!\n"w);
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto name = "D"d;
    auto ver = 2;
    assert(dstringBuf() << "Hi "d  << name << ver << "!\n"d << getData == "Hi D2!\n");
}

@safe pure nothrow @nogc
version (mir_test) unittest
{
    assert(stringBuf() << -1234567890 << getData == "-1234567890");
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
    {
        enum N = T.sizeof * 2;
        static if(isFastBuffer!W)
        {
            w.advance(printHexAddress(value, w.getBuffer(N).getStaticBuf!N, cast(bool) switchLU));
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
Note: Non-ASCII Unicode characters are encoded as sequence of \xXX bytes. This may be fixed in the future.
+/
pragma(inline, false)
ref W printEscaped(C = char, W)(scope return ref W w, scope const(char)[] str)
{
    // TODO: replace with Mir implementation.
    w.put('\"');
    foreach (char c; str[])
    {
        if (c >= 0x20)
        {
            if (c < 0x7F)
            {
                if (c == '\"' || c == '\\')
                {
                L:
                    w.put('\\');
                }
                w.put(c);
            }
            else
            {
            M:
                printStaticStringInternal!(C, "\\x")(w);
                print!C(w, HexAddress!ubyte(cast(ubyte)c));
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
    }
    w.put('\"');
    return w;
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    assert(w.printEscaped("Hi\t" ~ `"@nogc"`).data == `"Hi\t\"@nogc\""`, w.data);
    w.reset;
    assert(w.printEscaped("\xF3").data == `"\xF3"`, w.data);
}

///
ref W printElement(C = char, W, T)(scope return ref W w, scope auto ref const T c)
{
    static if (isSomeString!T)
    {
        return printEscaped!C(w, c);
    }
    else
    {
        return print!C(w, c);
    }
}

/++
Multiargument overload.
+/
ref W print(C = char, W, Args...)(scope return ref W w, scope auto ref const Args args)
    if (Args.length > 1)
{
    foreach(i, ref c; args)
        static if (i < Args.length - 1)
            print!C(w, c);
        else
            return print!C(w, c);
}

///
ref W print(C = char, W, T)(scope return ref W w, const T c)
    if (is(T == enum))
{
    static assert(!is(OriginalType!T == enum));
    string s;
    S: switch (c)
    {
        static foreach(member; __traits(allMembers, T))
        {
            case __traits(getMember, T, member):
            s = member;
            break S;
        }
        default:
            static immutable C[] str = T.stringof;
            w.put(str[]);
            w.put('(');
            print(w, cast(OriginalType!T) c);
            w.put(')');
            return w;
    }
    w.put(s);
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

    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    w.print(Flag.yes);
    assert(w.data == "yes", w.data);
}

/// ditto
ref W print(C = char, W)(scope return ref W w, bool c)
{
    enum N = 5;
    static if(isFastBuffer!W)
    {
        w.advance(printBoolean(c, w.getBuffer(N).getStaticBuf!N));
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
    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    assert(w.print(true).data == `true`, w.data);
    w.reset;
    assert(w.print(false).data == `false`, w.data);
}

/// ditto
pragma(inline, false)
ref W print(C = char, W, V, K)(scope return ref W w, scope const V[K] c)
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
            printStaticStringInternal!(C, sep)(w);
        first = false;
        printElement!C(w, key);
        printStaticStringInternal!(C, mid)(w);
        printElement!C(w, value);
    }
    w.put(right);
    return w;
}

///
@safe pure
version (mir_test) unittest
{
    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    w.print(["a": 1, "b": 2]);
    assert(w.data == `["a": 1, "b": 2]` || w.data == `["b": 2, "a": 1]`, w.data);
}

/// ditto
pragma(inline, false)
ref W print(C = char, W, T)(scope return ref W w, scope const(T)[] c)
    if (!isSomeChar!T)
{
    enum C left = '[';
    enum C right = ']';
    enum C[2] sep = ", ";
    w.put(left);
    bool first = true;
    foreach (ref e; c)
    {
        if (!first)
            printStaticStringInternal!(C, sep)(w);
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
    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    string[2] array = ["a\ta", "b"];
    assert(w.print(array[]).data == `["a\ta", "b"]`, w.data);
}

/// ditto
pragma(inline, false)
ref W print(C = char, W)(scope return ref W w, char c)
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
            printStaticStringInternal!(C, "\\x")(w);
            print!C(w, HexAddress!ubyte(cast(ubyte)c));
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
    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    assert(w
        .print('\n')
        .print('\'')
        .print('a')
        .print('\xF4')
        .data == `'\n''\'''a''\xF4'`);
}

/// ditto
ref W print(C = char, W)(scope return ref W w, scope const(C)[] c)
    if (isSomeChar!C)
{
    w.put(c);
    return w;
}

/// ditto
ref W print(C = char, W, I)(scope return ref W w, const I c)
    if (isIntegral!I && !is(I == enum))
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

/// ditto
ref W print(C = char, W, T)(scope return ref W w, const T c)
    if(is(T == float) || is(T == double) || is(T == real))
{
    auto ff = FormattedFloating!T(c);
    return print!C(w, ff);
}

/// ditto
pragma(inline, false)
ref W print(C = char, W, T)(scope return ref W w, ref const T c)
    if (is(T == struct) || is(T == union))
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
        return print(w, string_of_c);
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
                printStaticStringInternal!(C, sep)(w);
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
                printStaticStringInternal!(C, sep)(w);
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
    if (is(T == struct) || is(T == union))
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

    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    assert(stringBuf() << A() << S() << D() << F() << G() << getData == "asdfg");
}

/// ditto
pragma(inline, false)
ref W print(C = char, W, T)(scope return ref W w, scope const T c)
    if (is(T == class) || is(T == interface))
{
    static if (__traits(hasMember, T, "toString") || __traits(compiles, { scope const(C)[] string_of_c = c; }))
    {
        if (c is null)
            printStaticStringInternal!(C, "null")(w);
        else
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
        else
        static if (__traits(compiles, { scope const(C)[] string_of_c = c; }))
        {
            scope const(C)[] string_of_c = c;
            return print(w, string_of_c);
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
                printStaticStringInternal!(C, sep)(w);
            first = false;
            print!C(w, e);
        }
        w.put(right);
    }
    else
    {
        w.put(T.stringof);
    }
    return w;
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

    import mir.appender: ScopedBuffer;
    ScopedBuffer!char w;
    assert(stringBuf() << new A() << new S() << new D() << new F() << new G() << getData == "asdfg");
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

private ref W printStaticStringInternal(C, immutable(C)[] c, W)(scope return ref W w)
    if (C.sizeof * c.length <= 512)
{
    static if (isFastBuffer!W)
    {
        printStaticString!c(w.getBuffer(c.length).getStaticBuf!(c.length));
        w.advance(c.length);
    }
    else
    static if (c.length <= 4)
    {
        static foreach(i; 0 .. c.length)
            w.put(c[i]);
    }
    else
    {
        w.put(c[]);
    }
    return w;
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
    if (isIntegral!I && !is(I == enum))
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
    ScopedBuffer!char w;

    w.printZeroPad(-123, 5);
    w.put(' ');
    w.printZeroPad(123, 5);

    assert(w.data == "-0123 00123", w.data);
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

///
size_t printStaticString(string str, C)(scope ref C[str.length] buf)
    if((is(C == char) || is(C == wchar) || is(C == dchar)) && (C[str.length]).sizeof <= 512)
{
    version(LDC) pragma(inline, true);
    static foreach (i, e; str) buf[i] = e;
    return buf.length;
}

/// ditto
size_t printStaticString(wstring str, C)(scope ref C[str.length] buf)
    if((is(C == wchar) || is(C == dchar)) && (C[str.length]).sizeof <= 512)
{
    version(LDC) pragma(inline, true);
    static foreach (i, e; str) buf[i] = e;
    return buf.length;
}

/// ditto
size_t printStaticString(dstring str)(scope ref dchar[str.length] buf)
    if((dchar[str.length]).sizeof <= 512)
{
    version(LDC) pragma(inline, true);
    static foreach (i, e; str) buf[i] = e;
    return buf.length;
}
