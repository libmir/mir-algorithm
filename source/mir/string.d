/++
$(H1 String routines)

The module contains SIMD-accelerated string routines.

Copyright: 2022 Ilia Ki, Symmetry Investments

Authors: Ilia Ki
+/
module mir.string;

import std.traits: isSomeChar;

private alias Representation(T :  char) = byte;
private alias Representation(T : wchar) = short;
private alias Representation(T : dchar) = int;

private enum size_t ScanVecSize = 16;

///
bool containsAny(C, size_t L)
    (scope const(C)[] str, const C[L] chars...)
    @trusted pure nothrow @nogc
    if (isSomeChar!C && L)
{
    enum size_t N = ScanVecSize / C.sizeof;

    alias U = Representation!C;

    // version(none)
    version (LittleEndian)
    version (LDC)
    static if (N <= 8)
    static if (is(__vector(U[N])))
    {
        alias V = __vector(U[N]);
        pragma(msg, V);
        V[L] charsv;
        static foreach (i; 0 .. L)
            charsv[i] = chars[i];

        while (str.length >= N)
        {
            auto a = cast(V) *cast(const U[N]*) str.ptr;

            import ldc.simd: mask = equalMask;

            V[L] masked;
            static foreach (i; 0 .. L)
                masked[i] = mask!(__vector(U[N]))(a, charsv[i]);

            static foreach (i; 0 .. L)
                static if (i == 0)
                    V m = masked[i];
                else
                    m |= masked[i];

            if (m != V.init)
                return true;

            str = str[N .. $];
        }
    }

    foreach (C c; str)
        static foreach (i; 0 .. L)
            if (c == chars[i])
                return true;
    return false;
}

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.test: should;

    assert("     hello world     ".containsAny('w'));
    assert(!"     hello world     ".containsAny('W'));
    assert("     hello world     ".containsAny('W', 'e'));
    assert("     hello world     ".containsAny("We"));
}

///
template scanLeftAny(string op = "==")
    if (op == "==" || op == "!=")
{
    ///
    inout(C)[]
        scanLeftAny(C, size_t L)
        (return scope inout(C)[] str, const C[L] chars...)
        @trusted pure nothrow @nogc
        if (isSomeChar!C && L)
    {
        enum size_t N = ScanVecSize / C.sizeof;

        alias U = Representation!C;

        // version(none)
        version (LittleEndian)
        version (LDC)
        static if (N <= 8)
        static if (is(__vector(U[N])))
        {
            import mir.bitop: cttz;

            alias V = __vector(U[N]);
            pragma(msg, V);
            V[L] charsv;
            static foreach (i; 0 .. L)
                charsv[i] = chars[i];

            while (str.length >= N)
            {
                auto a = cast(V) *cast(const U[N]*) str.ptr;

                import ldc.simd: mask = equalMask;

                V[L] masked;
                static foreach (i; 0 .. L)
                    masked[i] = mask!(__vector(U[N]))(a, charsv[i]);

                static foreach (i; 0 .. L)
                    static if (i == 0)
                        V m = masked[i];
                    else
                        m |= masked[i];

                static if (op == "!=")
                    m = ~m;

                auto words = (cast(__vector(size_t[U[N].sizeof / size_t.sizeof])) m).array;

                static foreach (i; 0 .. words.length)
                {
                    if (words[i])
                    {
                        enum p = i * size_t.sizeof / U.sizeof;
                        return str[p + (cttz(words[i]) / (U.sizeof * 8)) .. $];
                    }
                }
                str = str[N .. $];
            }
        }

        Loop: for (; str.length; str = str[1 .. $])
        {
            auto c = str[0];
            static foreach (i; 0 .. L)
            {
                if (c == chars[i])
                {
                    static if (op == "==")
                        break Loop;
                    else
                        continue Loop;
                }
            }
            static if (op == "==")
                continue Loop;
            else
                break Loop;
        }
        return str;
    }
}

///
alias stripLeft = scanLeftAny!"!=";

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.test: should;

    "     hello world     ".stripLeft(' ').should == "hello world     ";
    "     hello world     ".scanLeftAny('w').should == "world     ";
    "     hello world     ".scanLeftAny('!').should == "";
    "\t\n\thello world\n\t___".stripLeft('\n', '\t').should == "hello world\n\t___";
    "hello world".stripLeft(' ').should == "hello world";
    "hello world           ".stripLeft(' ').should == "hello world           ";

    "        _____________              hello world     "
        .stripLeft(' ', '_').should == "hello world     ";
}

///
template scanRightAny(string op = "==")
    if (op == "==" || op == "!=")
{
    ///
    inout(C)[]
        scanRightAny(C, size_t L)
        (return scope inout(C)[] str, const C[L] chars...)
        @trusted pure nothrow @nogc
        if (isSomeChar!C && L)
    {
        enum size_t N = ScanVecSize / C.sizeof;

        alias U = Representation!C;

        // version(none)
        version (LittleEndian)
        version (LDC)
        static if (N <= 8)
        static if (is(__vector(U[N])))
        {
            import mir.bitop: ctlz;

            alias V = __vector(U[N]);
            pragma(msg, V);
            V[L] charsv;
            static foreach (i; 0 .. L)
                charsv[i] = chars[i];

            while (str.length >= N)
            {
                auto a = cast(V) *cast(const U[N]*) (str.ptr + str.length - N);

                import ldc.simd: mask = equalMask;

                V[L] masked;
                static foreach (i; 0 .. L)
                    masked[i] = mask!(__vector(U[N]))(a, charsv[i]);

                static foreach (i; 0 .. L)
                    static if (i == 0)
                        V m = masked[i];
                    else
                        m |= masked[i];

                static if (op == "!=")
                    m = ~m;

                auto words = (cast(__vector(size_t[U[N].sizeof / size_t.sizeof])) m).array;

                static foreach (i; 0 .. words.length)
                {
                    if (words[$ - 1 - i])
                    {
                        enum p = i * size_t.sizeof / U.sizeof;
                        return str[0 .. $ - (p + (ctlz(words[$ - 1 - i]) / (U.sizeof * 8)))];
                    }
                }
                str = str[0 .. $ - N];
            }
        }

        Loop: for (; str.length; str = str[0 .. $ - 1])
        {
            auto c = str[$ - 1];
            static foreach (i; 0 .. L)
            {
                if (c == chars[i])
                {
                    static if (op == "==")
                        break Loop;
                    else
                        continue Loop;
                }
            }
            static if (op == "==")
                continue Loop;
            else
                break Loop;
        }
        return str;
    }
}

///
alias stripRight = scanRightAny!"!=";

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.test: should;

    "     hello world     ".stripRight(' ').should == "     hello world";
    "     hello world     ".scanRightAny('w').should == "     hello w";
    "     hello world     ".scanRightAny('!').should == "";
    "___\t\n\thello world\n\t".stripRight('\n', '\t').should == "___\t\n\thello world";
    "hello world".stripRight(' ').should == "hello world";
    "           hello world".stripRight(' ').should == "           hello world";

    "     hello world        _____________              "
        .stripRight(' ', '_').should == "     hello world";
}

///
inout(C)[]
    strip(C, size_t L)
    (return scope inout(C)[] str, const C[L] chars...)
    @trusted pure nothrow @nogc
    if (isSomeChar!C && L)
{
    return str.stripLeft(chars).stripRight(chars);
}

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.test: should;

    "     hello world!     ".strip(' ')     .should == "hello world!";
    "     hello world!!!   ".strip(" !").should == "hello world";
}
