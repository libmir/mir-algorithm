/++
$(H2 Cubic Spline Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolation)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolation, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolation.cubic;

import std.traits;
import mir.ndslice.slice;
import mir.array.primitives;
import mir.utility: fastmath;

@fastmath:

/++
Structure for unbounded cubic spline in symmetrical form.
+/
struct CubicSpline(T)
    if (is(Unqual!T == T))
{
    ///
    const size_t _length;
    ///
    const T* _grid;
    ///
    const T* _values;
    ///
    const T* _slopes;

@trusted @fastmath:

    this()(
        Slice!(Contiguous, [1], const(T)*) grid,
        Slice!(Contiguous, [1], const(T)*) values,
        Slice!(Contiguous, [1], const(T)*)  slopes) @system
    {
        assert (grid.length >= 2);
        assert (grid.length == values.length);
        assert (grid.length == slopes.length);
        this._length = grid.length;
        this._grid   = grid._iterator;
        this._values = values._iterator;
        this._slopes = slopes._iterator;
    }

    /++
    Interval index for x.
    +/
    size_t interval(T)(in T x)
    {
        import std.range: assumeSorted;
        return _grid.sliced(_length)[1 .. $ - 1]
            .assumeSorted
            .lowerBound(x)
            .length;
    }

    /++
    `(x)` and `[x]` operators.
    Complexity:
        `O(log(_grid.length))`
    +/
    T opCall()(T x)
    {
        return opCall(x, interval(x));
    }

    /++
    `(x, interval)` and `[x, interval]` operators.
    Complexity:
        `O(1)`
    +/
    T opCall()(T x, size_t interval) @system
    {
        assert(interval + 1 < _length);

        auto x0 = _grid  [interval + 0];
        auto x1 = _grid  [interval + 1];
        auto y0 = _values[interval + 0];
        auto y1 = _values[interval + 1];
        auto s0 = _slopes[interval + 0];
        auto s1 = _slopes[interval + 1];

        return opCall(x0, x1, y0, y1, s0, s1, x);
    }

    ///
    static T opCall()(T x0, T x1, T y0, T y1, T s0, T s1, T x)
    {
        auto step = x1 - x0;
        auto diff = y1 - y0;
        s0 *= step;
        s1 *= step;
        auto w0 = x - x0;
        auto w1 = x1 - x;
        auto d0 = diff - s0;
        auto d1 = diff - s1;
        w0 /= step;
        w1 /= step;
        auto b_ = d0 + d1;
        d0 += w1 * b_;
        d1 += w0 * b_;
        d0 *= w0;
        d1 *= w1;
        d0 += s0;
        d1 += s1;
        d0 *= w0;
        d1 *= w1;
        y0 += d0;
        y1 -= d1;
        y0 *= w1;
        y1 *= w0;

        return y0 + y1;
    }

    /// ditto
    alias opIndex = opCall;
}
