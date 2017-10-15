/++
$(H2 Piecewise Cubic Hermite Interpolating Polynomial)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolation)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolation, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolation.pchip;

import std.traits;
import mir.ndslice.slice;
import mir.array.primitives;
import mir.utility: fastmath;

@fastmath:

/++
Structure for unbounded piecewise cubic hermite interpolating polynomial.
+/
struct Pchip(T)
{
    import std.range: assumeSorted;

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

/++
Unbounded piecewise cubic hermite interpolating polynomial.
Params:
    grid = `x` values for interpolation
    values = `f(x)` values for interpolation
Constraints:
    `grid` and `values` must have the same length >= 3
Returns: $(LREF Pchip)
Allocation: Allocates slopes using GC.
+/
auto pchip(T)(
    Slice!(Contiguous, [1], const(T)*) grid,
    Slice!(Contiguous, [1], const(T)*) values)
{
    import mir.ndslice.allocation: uninitSlice;
    return pchip(grid, values, uninitSlice!T(grid.length));
}

/++
Piecewise cubic hermite interpolating polynomial.
Params:
    grid = `x` values for interpolation
    values = `f(x)` values for interpolation
    slopes = uninitialized ndslice to write slopes into
Constraints:
    `grid`, `values`, and `slopes` must have the same length >= 3
Returns: $(LREF Pchip)
+/
Pchip!T pchip(T)(
    Slice!(Contiguous, [1], const(T)*) grid,
    Slice!(Contiguous, [1], const(T)*) values,
    Slice!(Contiguous, [1], T*)  slopes) @trusted
{
    if (grid.length < 3)
        assert(0);
    if (grid.length != values.length)
        assert(0);
    if (grid.length != slopes.length)
        assert(0);

    T step0 = grid  [1] - grid  [0];
    T step1 = grid  [2] - grid  [1];
    T diff0 = values[1] - values[0];
    T diff1 = values[2] - values[1];
    diff0 /= step0;
    diff1 /= step1;

    slopes.front = pchipTail(step0, step1, diff0, diff1);
    for(size_t i = 1;;)
    {
        import mir.math.common: copysign;
        if (diff0 && diff1 && copysign(1f, diff0) == copysign(1f, diff1))
        {
            auto w0 = step1 * 2 + step0;
            auto w1 = step0 * 2 + step1;
            slopes[i] = (w0 + w1) / (w0 / diff0 + w1 / diff1);
        }
        else
        {
            slopes[i] = 0;
        }
        if (++i == slopes.length - 1)
        {
            break;
        }
        step0 = step1;
        diff0 = diff1;
        step1 = grid  [i + 1] - grid  [i + 0];
        diff1 = values[i + 1] - values[i + 0];
        diff1 /= step1;
    }
    slopes.back = pchipTail(step1, step0, diff1, diff0);

    return typeof(return)(grid, values, slopes);
}

///
version(mir_test)
@safe unittest
{
    import std.math: approxEqual;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: map, indexed;
    
    auto x   = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].sliced;
    auto y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].sliced;
    auto interpolation = x.pchip(y);

    auto xs = x[0 .. $ - 1] + 0.5;
    auto ys = xs.map!interpolation;
    
    auto ys2 = interpolation.indexed(xs); // alternative to map
    version(X86_64)
        assert(ys == ys2);

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

// Check direction equality
version(mir_test)
@safe unittest
{
    import std.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: retro, map;

    auto grid   = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].sliced;
    auto values = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].sliced;

    auto results = [
        5.333333333333334,
        2.500000000000000,
        10.000000000000000,
        4.288971807628524,
        11.202580845771145,
        16.250000000000000,
        17.962962962962962,
        5.558593750000000,
        17.604662698412699,
        ];
    auto interpolation = grid.pchip(values);

    auto gridR = slice(-grid.retro);
    auto valuesR = values.retro.slice;
    auto interpolationR = gridR.pchip(valuesR);

    version(X86_64)
    assert(map!interpolation(grid[0 .. $ - 1] +  0.5) == map!interpolationR(gridR.retro[0 .. $ - 1] - 0.5));
}

auto pchipTail(T)(in T step0, in T step1, in T diff0, in T diff1)
{
    import mir.math.common: copysign, fabs;
    if (!diff0)
    {
        return 0;
    }
    auto slope = ((step0 * 2 + step1) * diff0 - step0 * diff1) / (step0 + step1);
    if (copysign(1f, slope) != copysign(1f, diff0))
    {
        return 0;
    }
    if ((copysign(1f, diff0) != copysign(1f, diff1)) && (fabs(slope) > fabs(diff0 * 3)))
    {
        return diff0 * 3;
    }
    return slope;
}
