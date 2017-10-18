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
    points = `x` values for interpolation
    values = `f(x)` values for interpolation
Constraints:
    `points` and `values` must have the same length >= 3
Returns: $(LREF Pchip)
Allocation: Allocates slopes using GC.
+/
CubicSpline!(packs == [2], const(T)*) cubicSpline(T, size_t[] packs)(
    Slice!(Contiguous, [1], const(T)*) points,
    Slice!(Contiguous, packs, const(T)*) values,
    SplineBoundaryType typeOfBondaries = SplineBoundaryType.notAKnot,
    T valueOfBondaryConditions = 0,
    )
    if (packs == [1] || packs == [2])
{
    return .cubicSpline(points, values, SplineBoundaryCondition!T(typeOfBondaries, valueOfBondaryConditions));
}

CubicSpline!(packs == [2], const(T)*) cubicSpline(T, size_t[] packs)(
    Slice!(Contiguous, [1], const(T)*) points,
    Slice!(Contiguous, packs, const(T)*) values,
    SplineBoundaryCondition!T bondaries,
    )
    if (packs == [1] || packs == [2])
{
    return .cubicSpline(points, values, bondaries, bondaries);
}

CubicSpline!(packs == [2], const(T)*) cubicSpline(T, size_t[] packs)(
    Slice!(Contiguous, [1], const(T)*) points,
    Slice!(Contiguous, packs, const(T)*) values,
    SplineBoundaryCondition!T rBoundary,
    SplineBoundaryCondition!T lBoundary,
    )
    if (packs == [1] || packs == [2])
{
    import mir.ndslice.allocation: uninitSlice;
    return .cubicSpline(
        points,
        values, 
        values.shape.uninitSlice!T,
        values.length.uninitSlice!T,
        rBoundary,
        lBoundary,
    );
}

/++
Piecewise cubic hermite interpolating polynomial.
Params:
    points = `x` values for interpolation
    values = `f(x)` values for interpolation
    slopes = uninitialized ndslice to write slopes into
Constraints:
    `points`, `values`, and `slopes` must have the same length >= 3
Returns: $(LREF Pchip)
+/
CubicSpline!(packs == [2],
    ConstIfPointer!IG,
    ConstIfPointer!IV,
    ConstIfPointer!IS)
cubicSpline(IG, IV, IS, IT, BT, size_t[] packs)(
    Slice!(Contiguous, [1], IG) points,
    Slice!(Contiguous, packs, IV) values,
    Slice!(Contiguous, packs, IS) slopes,
    Slice!(Contiguous, [1], IT) temp,
    SplineBoundaryCondition!BT lbc,
    SplineBoundaryCondition!BT rbc,
    ) @trusted
    if (packs == [1] || packs == [2])
{
    import mir.ndslice.topology: diff, ipack;

    enum vec = packs == [2];

    if (points.length < 2)
        assert(0);
    if (points.length != values.length)
        assert(0);
    if (points.length != slopes.length)
        assert(0);
    if (temp.length + 1 < points.length)
        assert(0);

    immutable n = points.length;

    auto pd = points.diff;
    static if (packs == [2])
        auto vd = values.ipack!1.diff;
    else
        auto vd = values.diff;

    auto xd = cast() pd.front;
    auto yd = cast() vd.front;
    auto dd = yd / xd;

    static if (packs == [2])
    {
        if (slopes.length!1 != values.length!1)
            assert(0);
        if (values.empty!1)
            goto ret;
    }

    /// special case
    static assert(SplineBoundaryType.notAKnot == 0);
    with(SplineBoundaryType)
    if (_expect(n == 3 && (rbc.type | lbc.type) == 0, false))
    {
        import mir.interpolation.utility;
        static if (packs == [1])
        {
            auto parabolaDerivative = parabolaKernel!1(points[0], points[1], points[2], values[0], values[1], values[2]);
            slopes[0] = parabolaDerivative(points[0]);
            slopes[1] = parabolaDerivative(points[1]);
            slopes[2] = parabolaDerivative(points[2]);
        }
        else
        {
            foreach (i; 0 .. values.length!1)
            {
                auto parabolaDerivative = parabolaKernel!1(points[0], points[1], points[2], values[0][i], values[1][i], values[2][i]);
                slopes[0][i] = parabolaDerivative(points[0]);
                slopes[1][i] = parabolaDerivative(points[1]);
                slopes[2][i] = parabolaDerivative(points[2]);
            }
        }
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
            auto b = pd[1];
            auto c = points.diff!2.front;
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
        auto xq = pd[i];
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
        goto rsimple;

    case notAKnot:
        if (n > 2)
        {
            auto a = points.diff!2[n - 3];
            auto b = pd[n - 3];
            auto r = b - a * temp[n - 2];
            auto d = ((xd + 2 * a) * b * dd + xd * xd * (vd[n - 3] / b)) / a;
            slopes[n - 1].ndassign = (d - a * slopes[n - 2]) / r;
            break;
        }

    rsimple:

        slopes[n - 1].ndassign = dd;
        break;

    case firstDerivative:

        slopes[n - 1].ndassign = rbc.value;
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
    return typeof(return)(points, values, slopes);
}

///
version(mir_test) @safe unittest
{
    import std.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: map, indexed;
    import mir.ndslice.algorithm: all;

    auto x = [-1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].sliced;
    auto y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].sliced;

    auto interpolation = cubicSpline(x, y); // constructs CubicSpline
    auto xs = x + 0.5;                     // input X values for cubic spline
    auto ys1 = xs.map!interpolation;       // lazy
    auto ys2 = interpolation.indexed(xs);  // alternative to `map`
    version(D_LP64)
        assert(ys1 == ys2);
    else
        assert(all!(all!approxEqual)(ys1, ys2));

    /// not-a-knot (default)
    assert(interpolation.indexed(xs).approxEqual([
        -0.68361541,   7.28568719,  10.490694  ,   0.36192032,
        11.91572713,  16.44546433,  17.66699525,   4.52730869,
        19.22825394,  -2.3242592 ]));

    /// natural cubic spline
    assert(cubicSpline(x, y, SplineBoundaryType.secondDerivative).indexed(xs).approxEqual([
        10.85298372,   5.26255911,  10.71443229,   0.1824536 ,
        11.94324989,  16.45633939,  17.59185094,   4.86340188,
        17.8565408 ,   2.81856494]));

    /// set both boundary derivatives to 3
    assert(cubicSpline(x, y, SplineBoundaryType.firstDerivative, 3).indexed(xs).approxEqual([
        16.45728263,   4.27981687,  10.82295092,   0.09610695,
        11.95252862,  16.47583126,  17.49964521,   5.26561539,
        16.21803478,   8.96104974]));

    /// different boundary conditions
    assert(cubicSpline(x, y,
            SplineBoundaryCondition!double(SplineBoundaryType.firstDerivative, 3),
            SplineBoundaryCondition!double(SplineBoundaryType.secondDerivative, -5))
        .indexed(xs)
        .approxEqual([
            16.45730084,   4.27966112,  10.82337171,   0.09403945,
            11.96265209,  16.44067375,  17.6374694 ,   4.67438921,
            18.6234452 ,  -0.05582876]));
    // ditto
    assert(cubicSpline(x, y,
            SplineBoundaryCondition!double(SplineBoundaryType.secondDerivative, -5),
            SplineBoundaryCondition!double(SplineBoundaryType.firstDerivative, 3))
        .indexed(xs)
        .approxEqual([
            12.37135558,   4.99638066,  10.74362441,   0.16008641,
            11.94073593,  16.47908148,  17.49841853,   5.26600921,
            16.21796051,   8.96102894]));
}

///
version(mir_test) unittest
{
    import std.math: approxEqual;
    import mir.ndslice.allocation: uninitSlice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: map, indexed, ipack;
    import mir.ndslice.algorithm: all;

    auto x = [-1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].sliced;
    auto y = uninitSlice!double(x.length, 4);
    y[]=
      [[ 8.77842512,  9.35433533,  1.23622769,  9.63950644],
       [ 7.96429686,  6.52520151,  2.69801767,  6.03236534],
       [ 7.77074363,  6.18805592,  9.64534176,  2.99776641],
       [ 1.10838032,  9.66832754,  3.42751538,  2.42539904],
       [ 2.69925191,  2.90739707,  4.18292592,  2.32656545],
       [ 1.84922654,  0.81465573,  8.38517033,  8.73043383],
       [ 1.48167283,  4.87488473,  1.27045556,  6.53941633],
       [ 2.8267636 ,  6.00230712,  5.38994909,  1.93718846],
       [ 0.40200172,  4.55388547,  2.27161086,  6.61117172],
       [ 7.78980608,  6.14148674,  3.23963855,  1.43811135]];
    
    auto interpolation = x.cubicSpline(y); // default boundary condition is 'not-a-knot'

    auto xs = x + 0.5;
    auto ys = xs.map!interpolation;

    auto ys2 = interpolation.indexed(xs); // alternative to map
    version(D_LP64)
        assert(ys1 == ys2);
    else
        assert(all!(all!approxEqual)(ys1, ys2));

    auto r =
      [[  5.56971848,  10.28636866,  -3.97903583,   9.59840221],
       [  9.30342403,   5.57939666,   6.18596012,   5.09632059],
       [  4.44139761,   8.00863926,   6.81880242,   2.6979041 ],
       [ -0.74740285,  10.19266461,   1.1564622 ,   2.00643585],
       [  3.00994108,   1.61645073,   6.00624788,   3.89687189],
       [  1.50750417,   1.57410287,   7.08130342,   9.04067189],
       [  1.73144979,   5.62005721,   0.67273232,   5.383684  ],
       [  2.64860361,   5.7813131 ,   5.96224749,   2.07796141],
       [  0.64413911,   4.56888621,   1.624089  ,   6.84250849],
       [ 10.81768928,   6.83993473,   5.10460598,  -1.49345532]];

    assert(all!(all!approxEqual)(ys, r));
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
    IG _points;
    ///
    IV _values;
    ///
    IS _slopes;

    private alias G = Unqual!(typeof(IG.init[0]));
    private alias V = Unqual!(typeof(IV.init[0]));
    private alias S = Unqual!(typeof(IS.init[0]));

@trusted @fastmath:

    ///
    auto points()
    {
        return _points.sliced(_length);
    }

    ///
    auto values()
    {
        static if (vec)
            return _values.sliced(_length, _vectorLength);
        else
            return _values.sliced(_length);
    }

    ///
    auto slopes()
    {
        static if (vec)
            return _slopes.sliced(_length, _vectorLength);
        else
            return _slopes.sliced(_length);
    }

    ///
    this()(Slice!(Contiguous, [1], IG) points, Slice!(Contiguous, [1 + vec], IV) values, Slice!(Contiguous, [1 + vec], IS) slopes) @system
    {
        assert (points.length >= 2);
        assert (points.length == values.length);
        assert (points.length == slopes.length);
        this._length = points.length;
        static if (vec)
        {
            assert(values.length!1 == slopes.length!1);
            this._vectorLength = values.length!1;
        }
        this._points  = points._iterator;
        this._values = values._iterator;
        this._slopes = slopes._iterator;
    }

    /++
    Interval index for x.
    +/
    size_t interval(T)(in T x)
    {
        import std.range: assumeSorted;
        return _length - 2 -_points.sliced(_length)[1 .. $ - 1]
            .assumeSorted
            .upperBound(x)
            .length;
    }

    /++
    `(x)` and `[x]` operators.
    Complexity:
        `O(log(_points.length))`
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

        auto x0 = points[interval + 0];
        auto x1 = points[interval + 1];
        auto y0 = values[interval + 0];
        auto y1 = values[interval + 1];
        auto s0 = slopes[interval + 0];
        auto s1 = slopes[interval + 1];

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
        import mir.ndslice.topology: indexed, zip;
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
