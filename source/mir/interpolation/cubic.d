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
import mir.ndslice.internal;

@fastmath:

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

CubicSpline!(packs == [2], const(T)*) cubicInterpolation(T, size_t[] packs)(
    Slice!(Contiguous, [1], const(T)*) grid,
    Slice!(Contiguous, packs, const(T)*) values,
    SplineBoundaryType typeOfBondaries = SplineBoundaryType.notAKnot,
    T valueOfBondaryConditions = 0,
    )
    if (packs == [1] || packs == [2])
{
    return .cubicInterpolation(grid, values, SplineBoundaryCondition!T(typeOfBondaries, valueOfBondaryConditions));
}

CubicSpline!(packs == [2], const(T)*) cubicInterpolation(T, size_t[] packs)(
    Slice!(Contiguous, [1], const(T)*) grid,
    Slice!(Contiguous, packs, const(T)*) values,
    SplineBoundaryCondition!T bondaries,
    )
    if (packs == [1] || packs == [2])
{
    return .cubicInterpolation(grid, values, bondaries, bondaries);
}

CubicSpline!(packs == [2], const(T)*) cubicInterpolation(T, size_t[] packs)(
    Slice!(Contiguous, [1], const(T)*) grid,
    Slice!(Contiguous, packs, const(T)*) values,
    SplineBoundaryCondition!T rBoundary,
    SplineBoundaryCondition!T lBoundary,
    )
    if (packs == [1] || packs == [2])
{
    import mir.ndslice.allocation: uninitSlice;
    return .cubicInterpolation(grid, values, 
        values.shape.uninitSlice!T,
        values.length.uninitSlice!T,
        rBoundary,
        lBoundary,
    );
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
CubicSpline!(packs == [2],
    ConstIfPointer!IG,
    ConstIfPointer!IV,
    ConstIfPointer!IS)
cubicInterpolation(IG, IV, IS, IT, BT, size_t[] packs)(
    Slice!(Contiguous, [1], IG) grid,
    Slice!(Contiguous, [1], IV) values,
    Slice!(Contiguous, packs, IS) slopes,
    Slice!(Contiguous, [1], IT) temp,
    SplineBoundaryCondition!BT lbc,
    SplineBoundaryCondition!BT rbc,
    ) @trusted
    if (packs == [1] || packs == [2])
{
    import mir.ndslice.topology: diff, ipack;

    enum vec = packs == [2];

    if (grid.length < 2)
        assert(0);
    if (grid.length != values.length)
        assert(0);
    if (grid.length != slopes.length)
        assert(0);
    if (temp.length + 1 < grid.length)
        assert(0);
    
    static if (packs == [2])
    {
        if (slopes.length!1 != values.length!1)
            assert(0);
        if (values.empty!1)
            goto ret;
    }

    immutable n = grid.length;

    auto gd = grid.diff;
    static if (packs == [2])
        auto vd = values.ipack!1.diff;
    else
        auto vd = values.diff;

    auto xd = cast() gd.front;
    auto yd = cast() vd.front;
    auto dd = yd / xd;

    /// special case
    static assert(SplineBoundaryType.notAKnot == 0);
    with(SplineBoundaryType)
    if (_expect(n == 3 && (rbc.type | lbc.type) == 0, false))
    {
        import mir.interpolation.utility;
        auto parabolaDerivative = ParabolaKernel!(Unqual!(typeof(dd)), 1)(grid[0], grid[1], grid[2], values[0], values[1], values[2]);
        slopes[0].ndassign = parabolaDerivative(grid[0]);
        slopes[1].ndassign = parabolaDerivative(grid[1]);
        slopes[2].ndassign = parabolaDerivative(grid[2]);
        goto ret;
    }

    with(SplineBoundaryType) switch(lbc.type)
    {
    case periodic:
        if (n > 2)
        {
            assert(0);
        }
        goto lsimple;
    case notAKnot:
        if (n > 2)
        {
            auto b = gd[0];
            auto c = grid.diff!2[0];
            auto d = ((xd + 2 * c) * b * dd + xd * xd * (vd[1] / b)) / c;
            auto r = b;
            temp[0] = c / r;
            slopes[0].ndassign = d / r;
            break;
        }
    lsimple:

        temp.front = 0;
        slopes.front.ndassign = dd;
        break;
    
    case firstDerivative:

        temp.front = 0;
        slopes.front.ndassign = lbc.value;
        break;

    case secondDerivative:

        temp[0] = 0.5f;
        slopes[0].ndassign = 1.5f * dd - 0.25f * lbc.value * xd;
        break;

    case parabolic:
        if (n > 2 || rbc.type == SplineBoundaryType.periodic)
        {
            temp[0] = 1;
            slopes[0].ndassign = 2 * dd;
            break;
        }
        slopes[0].ndassign = slopes[1].ndassign = dd;
    
        goto ret;

    default: assert(0);
    }

    foreach (i; 1 .. n - 1)
    {
        auto xq = gd[i];
        auto a = xq;
        auto b = 2 * (xd + xq);
        auto c = xd;
        auto r = b - a * temp[i - 1];
        temp[i] = c / r;
        auto yq = vd[i];
        auto dq = yq / xq;
        auto d = 3 * (dq * xd + dd * xq);
        slopes[i].ndassign = (d - a * slopes[i - 1]) / r;
        xd = xq;
        yd = yq;
        dd = dq;
    }

    with(SplineBoundaryType) switch(rbc.type)
    {
    case periodic:
        if (n > 2)
        {
            assert(0);
        }
        rbc.value = dd;
        goto case firstDerivative;
    case notAKnot:
        if (n > 2)
        {
            auto a = gd[n - 3];
            auto b = grid.diff!2[n - 3];
            auto r = b - a * temp[n - 2];
            auto d = ((xd + 2 * b) * a * dd + xd * xd * (vd[n - 3] / a)) / b;
            slopes[n - 1].ndassign = (d - a * slopes[n - 2]) / r;
        }
        rbc.value = dd;
        goto case firstDerivative;
        assert(0);

    case firstDerivative:

        slopes[n - 1] = rbc.value;
        break;

    case secondDerivative:

        slopes[n - 1].ndassign = (3 * dd + 0.5f * rbc.value * xd - slopes[n - 2]) / (2 - temp[n - 2]);
        break;

    case parabolic:
        slopes[n - 1].ndassign = (2 * dd - slopes[n - 2]) / (1 - temp[n - 2]);
        break;

    default: assert(0);
    }

    foreach_reverse (i; 0 .. n - 1)
    {
        slopes[i].ndassign !"-"= temp[i] * slopes[i + 1];
    }
ret:
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

    auto x = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].sliced;
    auto y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].sliced;
    auto interpolation = x.cubicInterpolation(y, SplineBoundaryType.secondDerivative);

    auto xs = x[0 .. $ - 1] + 0.5;
    auto ys = xs.map!interpolation;

    auto ys2 = interpolation.indexed(xs); // alternative to map
    version(X86_64)
        assert(ys == ys2);

    assert(ys.approxEqual([  6.20760827,   1.4508169 ,  11.13640756,  -0.15788353,
        12.00598131,  16.43904823,  17.59838292,   4.8612784 ,  17.8570522 ]));
}

/++
Structure for unbounded cubic spline in symmetrical form.
+/
struct CubicSpline(bool vec, IG, IV = IG, IS = IV)
{
    ///
    size_t _length;
    static if (vec)
    ///
    size_t _vectorLength;
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

    ///
    this()(Slice!(Contiguous, [1], IG) grid, Slice!(Contiguous, [1 + vec], IV) values, Slice!(Contiguous, [1 + vec], IS) slopes) @system
    {
        assert (grid.length >= 2);
        assert (grid.length == values.length);
        assert (grid.length == slopes.length);
        this._length = grid.length;
        static if (vec)
        {
            assert(values.length!1 == slopes.length!1);
            this._vectorLength = values.length!1;
        }
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
        return _length - 2 -_grid.sliced(_length)[1 .. $ - 1]
            .assumeSorted
            .upperBound(x)
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

        auto kernel = CubicSplineKernel!(Unqual!(typeof(x - x0)), derivative)(x0, x1, x);
        return kernel(y0, y1, s0, s1);
    }

    /// opIndex is alias for opCall
    alias opIndex = opCall;

    ///
    alias withDerivative() = opCall!1;
    ///
    alias withDerivatives() = opCall!2;
}

struct CubicSplineKernel(T, uint derivative)
    if (derivative <= 3)
{
    T step = 0;
    T w0 = 0;
    T w1 = 0;
    T wq = 0;

    this()(T x0, T x1, T x)
    {
        step = x1 - x0;
        immutable c0 = x - x0;
        immutable c1 = x1 - x;
        w0 = c0 / step;
        w1 = c1 / step;
        wq = w0 * w1;
    }

    ///
    auto opCall(V)(in V y0, in V y1, in V s0, in V s1)
        if (!isSlice!V)
    {
        immutable diff = y1 - y0;
        immutable z0 = s0 * step - diff;
        immutable z1 = s1 * step - diff;
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
            ret[2] = zd * ((1 - 3 * wd) / (step * step));
            return ret;
        }
    }

    ///
    auto opCall(VI, SI)(
        Slice!(Contiguous, [1], VI) y0,
        Slice!(Contiguous, [1], VI) y1,
        Slice!(Contiguous, [1], SI) s0,
        Slice!(Contiguous, [1], SI) s1,
        )
    {
        import mir.ndslice.topology: indexed;
        return this.indexed(zip(y0, y1, s0, s1));
    }

    ///
    alias opIndex = opCall;
}

@fastmath:


enum SplineBoundaryType
{
    /// not implemented
    periodic = -1,
    ///
    notAKnot,
    /// 
    firstDerivative,
    /// 
    secondDerivative,
    ///
    parabolic,
}

struct SplineBoundaryCondition(T)
{
    /// type
    SplineBoundaryType type = SplineBoundaryType.notAKnot;
    /// value (optional)
    T value = 0;
}
