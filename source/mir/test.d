/++
Testing utilities

Authors: Ilya Yaroshenko
+/
module mir.test;

import mir.exception: MirError;

private noreturn assumeAllAttrAndCall(scope const void delegate() t)
    @nogc pure nothrow @trusted {
    (cast(const void delegate() @safe pure nothrow @nogc) t)();
    assert(0);
}

///
struct ShouldApprox(T)
    if (__traits(isFloating, T))
{
    ///
    T value;
    ///
    T maxRelDiff = 0x1p-20f;
    ///
    T maxAbsDiff = 0x1p-20f;

    ///
    void opEquals(T expected, string file = __FILE__, int line = __LINE__) @safe pure nothrow @nogc
    {
        import mir.format: stringBuf, getData;
        import mir.math.common: approxEqual;
        if (value.approxEqual(expected, maxRelDiff, maxAbsDiff))
            return;
        auto buf = stringBuf;
        assumeAllAttrAndCall({
            throw new MirError(buf
                << "expected approximately " << expected
                << ", got " << value
                << ", maxRelDiff = " << maxRelDiff
                << ", maxAbsDiff = " << maxAbsDiff
                << getData, file, line);
        });
        assert(0);
    }
}

/// ditto
ShouldApprox!T shouldApprox(T)(const T value, const T maxRelDiff = T(0x1p-20f), const T maxAbsDiff = T(0x1p-20f))
    if (__traits(isFloating, T))
{
    return typeof(return)(value, maxRelDiff, maxAbsDiff);
}

///
version(mir_test)
unittest
{
    1.0.shouldApprox == 1 + 9e-7;
    shouldApprox(1 + 9e-7, 1e-6, 1e-6) == 1;
}

///
struct Should(T)
{
    ///
    T value;

    static if(!is(immutable T == immutable ubyte[]))
        ///
    void opEquals(R)(const R expected, string file = __FILE__, int line = __LINE__)
    {
        import mir.format: stringBuf, getData;
        static if (__traits(isFloating, R))
        {
            if (expected != expected && value != value)
                return;
        }
        if (value == expected)
            return;
        auto buf = stringBuf;
        buf << "mir.test.should:\n";
            buf << "expected " << expected << "\n"
                << "     got " << value;
        assumeAllAttrAndCall({ throw new MirError(buf << getData, file, line); });
    }
    else
    /// ditto
    void opEquals(scope const ubyte[] expected, string file = __FILE__, int line = __LINE__)
        @safe pure nothrow @nogc
    {
        import mir.format: stringBuf, getData;
        if (value == expected)
            return;
        auto buf = stringBuf;
        import mir.format: printHexArray;
        import mir.ndslice.topology: map;
        buf << "mir.test.should:\n";
        buf << "expected ";
        buf.printHexArray(expected);
        buf << "\n";
        buf << "     got ";
        buf.printHexArray(   value);
        assumeAllAttrAndCall({ throw new MirError(buf << getData, file, line); });
    }
}

/// ditto
Should!T should(T)(T value)
{
    return typeof(return)(value);
}

///
version(mir_test)
unittest
{
    1.0.should == 1;
    should(1) == 1;

    ubyte[] val = [0, 2, 3];
    val.should = [0, 2, 3];
}

///
void should(alias fun, T, R)(const T value, const R expected, string file = __FILE__, int line = __LINE__)
{
    import mir.functional;
    import mir.format: stringBuf, getData;
    if (naryFun!fun(value, expected))
        return;
    auto buf = stringBuf;
    buf << fun.stringof
        << " returns false"
        << " for a = " << value
        << ", b = " << expected;
    throw new MirError(buf << getData, file, line);
}

///
version(mir_test)
unittest
{
    1.0.should!"a < b"(1.3);
}
