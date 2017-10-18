/++
$(H1 Interpolation Algorithms)

$(BOOKTABLE $(H2 Interpolation modules),
$(TR $(TH Module) $(TH Interpolation kind))
$(T2M linear, Linear Interpolation)
$(T2M pchip, Cubic Hermite Interpolation)
)

Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolation, $1)$(NBSP)
T2M=$(TR $(TDNW $(MREF mir,interpolation,$1)) $(TD $+))
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolation;

import mir.primitives;

/++
Lazy interpolation shell with linear complexity.

Params:
    range = sorted range
    interpolation = interpolation structure with `._points` and `.opCall(x, interval)` methods.
Complexity:
    `O(range.length + interpolation._points.length)` to evaluate all elements.
Returns:
    Lazy input range.
See_also:
    $(SUBREF linear, linearSpline),
    $(SUBREF pchip, pchip).
+/
auto interp1(Range, Interpolation)(Range range, Interpolation interpolation, size_t interval = 0)
{
    return Interp1!(Range, Interpolation)(range, interpolation, interval);
}

/// ditto
struct Interp1(Range, Interpolation)
{
    /// Sorted range (descending)
    Range _range;
    ///  Interpolation structure
    Interpolation _interpolation;
    /// Current interpolation interval
    size_t _interval;

    static if (hasLength!Range)
    /// Length (optional)
    size_t length()() @property  { return _range.length; }
    /// Save primitive (optional)
    auto save()() @property
    {
        auto ret = this;
        ret._range = _range.save;
        return ret;
    }
    /// Input range primitives
    bool   empty ()() @property  { return _range.empty;  }
    /// ditto
    void popFront()() { _range.popFront; }
    /// ditto
    auto front()() @property
        
    {
        assert(!empty);
        auto x = _range.front;
        return (x) @trusted {
            while (x > _interpolation._points[_interval + 1] && _interpolation._length > _interval + 2)
                _interval++;
            return _interpolation(x, _interval);
        } (x);
    }
}

/++
PCHIP interpolation.
+/
version(mir_test)
@safe unittest
{
    import std.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: slice;
    import mir.interpolation: interp1;
    import mir.interpolation.pchip;

    auto x = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].sliced;
    auto y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].sliced;
    auto interpolation = x.pchip(y);

    auto xs = slice(x[0 .. $ - 1] + 0.5);

    auto ys = xs.interp1(interpolation);

    assert(ys.approxEqual([
        5.333333333333334,
        2.500000000000000,
        10.000000000000000,
        4.288971807628524,
        11.202580845771145,
        16.250000000000000,
        17.962962962962962,
        5.558593750000000,
        17.604662698412699,
        ]));

}

@safe unittest
{
    import mir.interpolation.linear;
    import mir.ndslice;
    import std.math: approxEqual;

    auto x = [0, 1, 2, 3, 5.00274, 7.00274, 10.0055, 20.0137, 30.0192];
    auto y = [0.0011, 0.0011, 0.0030, 0.0064, 0.0144, 0.0207, 0.0261, 0.0329, 0.0356,];
    auto xs = [1, 2, 3, 4.00274, 5.00274, 6.00274, 7.00274, 8.00548, 9.00548, 10.0055, 11.0055, 12.0082, 13.0082, 14.0082, 15.0082, 16.011, 17.011, 18.011, 19.011, 20.0137, 21.0137, 22.0137, 23.0137, 24.0164, 25.0164, 26.0164, 27.0164, 28.0192, 29.0192, 30.0192];

    auto interpolation = linearSpline(x.sliced, y.sliced);

    auto data = [0.0011, 0.0030, 0.0064, 0.0104, 0.0144, 0.0176, 0.0207, 0.0225, 0.0243, 0.0261, 0.0268, 0.0274, 0.0281, 0.0288, 0.0295, 0.0302, 0.0309, 0.0316, 0.0322, 0.0329, 0.0332, 0.0335, 0.0337, 0.0340, 0.0342, 0.0345, 0.0348, 0.0350, 0.0353, 0.0356];

    assert(approxEqual(xs.interp1(interpolation), data, 1e-4, 1e-4));
}

extern(C++) interface InterpolationI(T)
{
@system pure nothrow @nogc:

    T opCall(T x, size_t interval);
    T[2] withDerivative(T x, size_t interval);
    T[3] withDerivatives(T x, size_t interval);

@safe:

    T opCall(T x);
    T[2] withDerivative(T x);
    T[3] withDerivatives(T x);

    Slice!(Contiguous, [1], const(T)*) points(size_t index);

    size_t intervalIndex(T x) @property;
}
