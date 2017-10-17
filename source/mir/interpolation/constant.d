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
struct ZeroSpline(IG, IV)
{
    ///
    size_t _length;
    ///
    IG _grid;
    ///
    IV _values;

    private alias G = Unqual!(typeof(IG.init[0]));
    private alias V = Unqual!(typeof(IV.init[0]));

@trusted @fastmath:

    this()(Slice!(Contiguous, [1], IG) grid, Slice!(Contiguous, [1], IV) values) @system
    {
        assert (grid.length >= 1);
        assert (grid.length == values.length);
        this._length = grid.length;
        this._grid   = grid._iterator;
        this._values = values._iterator;
    }

    /++
    Interval index for x.
    +/
    size_t interval(T)(in T x)
    {
        import std.range: assumeSorted;
        return _length - 1 -_grid.sliced(_length)[1 .. $]
            .assumeSorted
            .upperBound(x)
            .length;
    }

    /++
    `(x)` and `[x]` operators.
    Complexity:
        `O(log(_grid.length))`
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
    grid = `x` values for interpolation
    values = `f(x)` values for interpolation

Constraints:
    `grid`, `values` must have the same length >= 3

Returns: $(LREF ZeroSpline)
+/
ZeroSpline!(IG, IV) constantInterpolation(IG, IV)(Slice!(Contiguous, [1], IG) grid, Slice!(Contiguous, [1], IV) values) @trusted
{
    if (grid.length == 0)
        assert(0);
    if (grid.length != values.length)
        assert(0);
    return typeof(return)(grid, values);
}

///
version(mir_test)
@safe unittest
{
    import mir.ndslice;
    import std.math: approxEqual;

    auto x = [0, 1, 2, 3];
    auto y = [10, 20, 30, 40];

    auto interpolation = constantInterpolation(x.sliced, y.sliced);

    assert(interpolation(-1) == 10);
    assert(interpolation(0) == 10);
    assert(interpolation(0.5) == 10);

    assert(interpolation(1) == 20);
    
    assert(interpolation(3) == 40);
    assert(interpolation(4) == 40);
}
