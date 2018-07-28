/++
$(H2 Piecewise Cubic Hermite Interpolating Polynomial)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.pchip;

public import mir.interpolate.spline: Spline;

import std.traits;
import std.meta: AliasSeq;
import mir.ndslice.slice;
import mir.array.primitives;
import mir.math.common: fmamath;
import mir.ndslice.internal: ConstIfPointer;

@fmamath:

/++
Constructs piecewise cubic hermite interpolating polynomial with nodes on rectilinear grid.
+/
template pchip(T, size_t N = 1, FirstGridIterator = immutable(T)*, NextGridIterators = Repeat!(N - 1, FirstGridIterator))
    if (isFloatingPoint!T && is(T == Unqual!T) && N <= 6)
{
    static assert (N == 1, "multivariate PCHIP is not implemented.");

    private alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    private alias GridVectors = Spline!(T, N, GridIterators).GridVectors;

    /++
    Unbounded piecewise spline hermite interpolating polynomial.
    Params:
        grid = `x` values for interpolant
        values = `f(x)` values for interpolant
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(SUBREF spline, Spline)
    +/
    @fmamath Spline!(T, N, GridIterators) pchip(yIterator, Kind ykind)(
        GridVectors grid,
        scope Slice!(yIterator, N, ykind) values) @safe
    {
        import std.algorithm.mutation: move;
        auto ret = Spline!T(grid);
        ret._values = values;
        pchipSlopes(grid, values, typeof(return).pickDataSubslice(ret._data, 1));
        return ret.move;
    }
}

///
version(mir_test)
@safe nothrow unittest
{
    import std.math: approxEqual;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: vmap;

    auto x = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].idup.sliced;
    auto y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].idup.sliced;
    auto interpolant = pchip!double(x, y);

    auto xs = x[0 .. $ - 1] + 0.5;
    auto ys = xs.vmap(interpolant);

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

    auto points = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].idup.sliced;
    auto values = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].idup.sliced;

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
    auto interpolant = pchip!double(points, values);

    auto pointsR = slice(-points.retro);
    auto valuesR = values.retro.slice;
    auto interpolantR = pchip!double(pointsR, valuesR);

    version(X86_64)
    assert(map!interpolant(points[0 .. $ - 1] +  0.5) == map!interpolantR(pointsR.retro[0 .. $ - 1] - 0.5));
}


/++
Computes slopes for piecewise spline hermite interpolating polynomial.
Params:
    points = `x` values for interpolant
    values = `f(x)` values for interpolant
    slopes = uninitialized ndslice to write slopes into
Constraints:
    `points`, `values`, and `slopes` must have the same length >= 3
+/
void pchipSlopes(IG, IV, IS, Kind gkind, Kind vkind, Kind skind)(
    scope Slice!(IG, 1, gkind) points,
    scope Slice!(IV, 1, vkind) values,
    scope Slice!(IS, 1, skind) slopes) @trusted
{
    if (points.length < 3)
        assert(0);
    if (points.length != values.length)
        assert(0);
    if (points.length != slopes.length)
        assert(0);

    auto step0 = cast()(points[1] - points[0]);
    auto step1 = cast()(points[2] - points[1]);
    auto diff0 = cast()(values[1] - values[0]);
    auto diff1 = cast()(values[2] - values[1]);
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
        step1 = points[i + 1] - points[i + 0];
        diff1 = values[i + 1] - values[i + 0];
        diff1 /= step1;
    }
    slopes.back = pchipTail(step1, step0, diff1, diff0);
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

template Repeat(ulong n, L...)
{
    static if (n)
    {
        import std.meta: Repeat;
        alias Repeat = std.meta.Repeat!(n, L);
    }
    else
        alias Repeat = L[0 .. 0];
}
