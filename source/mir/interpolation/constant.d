/++
$(H2 Constant Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolation)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolation, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolation.constant;

import std.traits;
import mir.array.primitives;
import mir.ndslice.slice;
import mir.utility: fastmath;

@fastmath:

/++
Unbounded constant interpolation.
+/
struct ZeroSpline(bool vec, IG, IV = IG)
{
    private
    {
        size_t _length;
        static if (vec)
        size_t _vectorLength;
        IG _points;
        IV _values;

        alias G = Unqual!(typeof(IG.init[0]));
        alias V = Unqual!(typeof(IV.init[0]));
    }

@trusted @fastmath:

    ///
    auto points()() @property
    {
        return _points.sliced(_length);
    }

    ///
    auto values()() @property
    {
        static if (vec)
            return _values.sliced(_length, _vectorLength);
        else
            return _values.sliced(_length);
    }

    ///
    this()(Slice!(Contiguous, [1], IG) points, Slice!(Contiguous, [1], IV) values) @system
    {
        assert (points.length >= 1);
        assert (points.length == values.length);
        this._length = points.length;
        this._points   = points._iterator;
        this._values = values._iterator;
    }

    /++
    Interval index for x.
    +/
    size_t interval(T)(in T x)
    {
        import std.range: assumeSorted;
        return _length - 1 -_points.sliced(_length)[1 .. $]
            .assumeSorted
            .upperBound(x)
            .length;
    }

    /++
    `(x)` and `[x]` operators.
    Complexity:
        `O(log(_points.length))`
    +/
    auto opCall(uint derivative = 0, T)(T x)
    {
        return opCall(x, interval(x));
    }

    /++
    `(x, interval)` and `[x, interval]` operators.
    Complexity:
        `O(1)`
    +/
    auto opCall(uint derivative = 0, T)(in T x, size_t interval) @system
    {
        assert(interval < _length);

        auto y = _values[interval];

        static if (derivative == 0)
        {
            return y;
        }
        else
        {
            typeof(y)[derivative + 1] ret = 0;
            ret[0] = y;
            return ret;
        }
    }


    /// opIndex is alias for opCall
    alias opIndex = opCall;
    ///
    alias withDerivative() = opCall!1;
    ///
    alias withDerivatives() = opCall!2;
}

/++
Constant interpolation.

Params:
    points = `x` values for interpolation
    values = `f(x)` values for interpolation

Constraints:
    `points`, `values` must have the same length >= 3

Returns: $(LREF ZeroSpline)
+/
ZeroSpline!(false, IG, IV) zeroSpline(IG, IV)(Slice!(Contiguous, [1], IG) points, Slice!(Contiguous, [1], IV) values) @trusted
{
    if (points.length == 0)
        assert(0);
    if (points.length != values.length)
        assert(0);
    return typeof(return)(points, values);
}

///
version(mir_test)
@safe unittest
{
    import mir.ndslice;
    import std.math: approxEqual;

    auto x = [0, 1, 2, 3];
    auto y = [10, 20, 30, 40];

    auto interpolation = zeroSpline(x.sliced, y.sliced);

    assert(interpolation(-1) == 10);
    assert(interpolation(0) == 10);
    assert(interpolation(0.5) == 10);

    assert(interpolation(1) == 20);
    
    assert(interpolation(3) == 40);
    assert(interpolation(4) == 40);
}
