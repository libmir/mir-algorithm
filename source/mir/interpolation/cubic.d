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
struct CubicSpline(IG, IV, IS)
{
    ///
    size_t _length;
    ///
    IG _grid;
    ///
    IV _values;
    ///
    IS _slopes;

    private alias G = Unqual!(typeof(IG.init[0]));
    private alias V = Unqual!(typeof(IV.init[0]));
    private alias S = Unqual!(typeof(IS.init[0]));

@trusted @fastmath:

    this()(Slice!(Contiguous, [1], IG) grid, Slice!(Contiguous, [1], IV) values, Slice!(Contiguous, [1], IS) slopes) @system
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
    auto opCall(uint derivative = 0, T)(in T x)
    {
        return opCall!derivative(x, interval(x));
    }

    /++
    `(x, interval)` and `[x, interval]` operators.
    Complexity:
        `O(1)`
    +/
    auto opCall(uint derivative = 0, T)(in T x, size_t interval) @system
    {
        assert(interval + 1 < _length);

        auto x0 = _grid  [interval + 0];
        auto x1 = _grid  [interval + 1];
        auto y0 = _values[interval + 0];
        auto y1 = _values[interval + 1];
        auto s0 = _slopes[interval + 0];
        auto s1 = _slopes[interval + 1];

        return opCall!derivative(x0, x1, y0, y1, s0, s1, x);
    }

    ///
    static auto opCall(uint derivative = 0, T)(G x0, G x1, V y0, V y1, S s0, S s1, in T x)
        if (derivative <= 6)
    {
        immutable step = x1 - x0;
        immutable diff = y1 - y0;
        immutable c0 = x - x0;
        immutable c1 = x1 - x;
        immutable w0 = c0 / step;
        immutable w1 = c1 / step;
        immutable z0 = s0 * step - diff;
        immutable z1 = s1 * step - diff;
        immutable wq = w0 * w1;
        immutable pr = z0 * w1 - z1 * w0;
        immutable y = w0 * y1 + w1 * y0 + wq * pr;
        static if (derivative == 0)
        {
            return y;
        }
        else
        {
            typeof(y)[derivative + 1] ret = 0;
            ret[0] = y;
            immutable wd = w2 - w1;
            immutable zd = z1 + z0;
            ret[1] = (diff + wd * pr - wq * zd) / step;
            static if (derivative > 1)
            ret[2] = zd * (1 -   3 * wd) / (step * step);
            return ret;
        }
    }

    /// ditto
    alias opIndex = opCall;
}
