/++
Testing utilities

Authors: Ilya Yaroshenko
+/
module mir.test;

import mir.exception: MirException;

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
    bool opEquals(T expected, string file = __FILE__, int line = __LINE__) const
    {
        import mir.format: stringBuf, getData;
        import mir.math.common: approxEqual;
        if (value.approxEqual(expected, maxRelDiff, maxAbsDiff))
            return true;
        stringBuf buf;
        throw new MirException(buf
            << "expected approximately " << expected
            << ", got " << value
            << ", maxRelDiff = " << maxRelDiff
            << ", maxAbsDiff = " << maxAbsDiff
            << getData, file, line);
    }
}

/// ditto
ShouldApprox!T shouldApprox(T)(const T value, const T maxRelDiff = T(0x1p-20f), const T maxAbsDiff = T(0x1p-20f))
    if (__traits(isFloating, T))
{
    return typeof(return)(value, maxRelDiff, maxAbsDiff);
}

///
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

    ///
    bool opEquals(R)(const R expected, string file = __FILE__, int line = __LINE__) const
    {
        import mir.format: stringBuf, getData;
        if (value == expected)
            return true;
        stringBuf buf;
        throw new MirException(buf
            << "expected " << expected
            << ", got " << value
            << getData, file, line);
    }
}

/// ditto
Should!T should(T)(T value)
{
    return typeof(return)(value);
}

///
unittest
{
    1.0.should == 1;
    should(1) == 1;
}

///
bool should(alias fun, T, R)(const T value, const R expected, string file = __FILE__, int line = __LINE__)
{
    import mir.functional;
    import mir.format: stringBuf, getData;
    if (naryFun!fun(value, expected))
        return true;
    stringBuf buf;
    buf << fun.stringof
        << " returns false"
        << " for a = " << value
        << ", b = " << expected;
    throw new MirException(buf << getData, file, line);
}

///
unittest
{
    1.0.should!"a < b"(1.3);
}
