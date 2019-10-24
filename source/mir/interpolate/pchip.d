/+
$(H2 Piecewise Cubic Hermite Interpolating Polynomial)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
deprecated("The PCHIP API was changed, the new one looks like spline!double(xSlice, ySlice, SplineType.monotone)")
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
        return spline!T(grid, values, SplineType.monotone);
    }
}
