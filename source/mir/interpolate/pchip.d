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
deprecated
module mir.interpolate.pchip;

public import mir.interpolate.spline: Spline;
import mir.interpolate;
import mir.interpolate.spline;
import mir.math.common: fmamath;
import mir.ndslice.slice;
import mir.primitives;
import std.traits;

private alias AliasSeq(T...) = T;

@fmamath:

/++
Constructs piecewise cubic hermite interpolating polynomial with nodes on rectilinear grid.
+/
deprecated
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
    @fmamath Spline!(T, N, GridIterators) pchip(yIterator, SliceKind ykind)(
        GridVectors grid,
        Slice!(yIterator, N, ykind) values) @safe
    {
        return spline!T(grid, values, SplineKind.monotone);
    }
}

///
version(mir_test)
@safe unittest
{
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: vmap;

    auto x = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].idup.sliced;
    auto y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].idup.sliced;
    auto interpolant = pchip!double(x, y);

    auto xs = x[0 .. $ - 1] + 0.5;

    () @trusted {
        auto ys = xs.vmap(interpolant);

        assert(ys.all!approxEqual([
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
    }();
}

// Check direction equality
version(mir_test)
@safe unittest
{
    import mir.math.common: approxEqual;
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
