/++
$(H2 Cubic Spline Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited and Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.spline;

import core.lifetime: move; 
import mir.functional;
import mir.internal.utility;
import mir.interpolate;
import mir.interpolate: Repeat;
import mir.math.common;
import mir.ndslice.slice;
import mir.primitives;
import mir.rc.array;
import mir.utility: min, max;
import std.meta: AliasSeq, staticMap;
import std.traits: Unqual;
public import mir.interpolate: atInterval;

@optmath:

///
@safe pure @nogc version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: rcslice;
    import mir.ndslice.topology: vmap;

    static immutable xdata = [-1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22];
    auto x = xdata.rcslice;
    static immutable ydata = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6];
    auto y = ydata.sliced;

    auto interpolant = spline!double(x, y); // constructs Spline
    auto xs = x + 0.5;                     // input X values for cubic spline

    static immutable test_data0 = [
        -0.68361541,   7.28568719,  10.490694  ,   0.36192032,
        11.91572713,  16.44546433,  17.66699525,   4.52730869,
        19.22825394,  -2.3242592 ];
    /// not-a-knot (default)
    assert(xs.vmap(interpolant).all!approxEqual(test_data0));

    static immutable test_data1 = [
        10.85298372,   5.26255911,  10.71443229,   0.1824536 ,
        11.94324989,  16.45633939,  17.59185094,   4.86340188,
        17.8565408 ,   2.81856494];
    /// natural cubic spline
    interpolant = spline!double(x, y, SplineBoundaryType.secondDerivative);
    assert(xs.vmap(interpolant).all!approxEqual(test_data1));

    static immutable test_data2 = [
        9.94191781,  5.4223652 , 10.69666392,  0.1971149 , 11.93868415,
        16.46378847, 17.56521661,  4.97656997, 17.39645585, 4.54316446];
    /// set both boundary second derivatives to 3
    interpolant = spline!double(x, y, SplineBoundaryType.secondDerivative, 3);
    assert(xs.vmap(interpolant).all!approxEqual(test_data2));

    static immutable test_data3 = [
        16.45728263,   4.27981687,  10.82295092,   0.09610695,
        11.95252862,  16.47583126,  17.49964521,   5.26561539,
        16.21803478,   8.96104974];
    /// set both boundary derivatives to 3
    interpolant = spline!double(x, y, SplineBoundaryType.firstDerivative, 3);
    assert(xs.vmap(interpolant).all!approxEqual(test_data3));

    static immutable test_data4 = [
            16.45730084,   4.27966112,  10.82337171,   0.09403945,
            11.96265209,  16.44067375,  17.6374694 ,   4.67438921,
            18.6234452 ,  -0.05582876];
    /// different boundary conditions
    interpolant = spline!double(x, y,
            SplineBoundaryCondition!double(SplineBoundaryType.firstDerivative, 3),
            SplineBoundaryCondition!double(SplineBoundaryType.secondDerivative, -5));
    assert(xs.vmap(interpolant).all!approxEqual(test_data4));
    

    static immutable test_data5 = [
            12.37135558,   4.99638066,  10.74362441,   0.16008641,
            11.94073593,  16.47908148,  17.49841853,   5.26600921,
            16.21796051,   8.96102894];
    // ditto
    interpolant = spline!double(x, y,
            SplineBoundaryCondition!double(SplineBoundaryType.secondDerivative, -5),
            SplineBoundaryCondition!double(SplineBoundaryType.firstDerivative, 3));
    assert(xs.vmap(interpolant).all!approxEqual(test_data5));
    
    static immutable test_data6 = [
        11.40871379,  2.64278898,  9.55774317,  4.84791141, 11.24842121,
        16.16794267, 18.58060557,  5.2531411 , 17.45509005,  1.86992521];
    /// Akima spline
    interpolant = spline!double(x, y, SplineType.akima);
    assert(xs.vmap(interpolant).all!approxEqual(test_data6));

    /// Double Quadratic spline
    interpolant = spline!double(x, y, SplineType.doubleQuadratic);
    import mir.interpolate.utility: ParabolaKernel;
    auto kernel1 = ParabolaKernel!double(x[2], x[3], x[4],        y[2], y[3], y[4]);
    auto kernel2 = ParabolaKernel!double(      x[3], x[4], x[5],        y[3], y[4], y[5]);
    // weighted sum of quadratic functions
    auto c = 0.35; // from [0 .. 1]
    auto xp = c * x[3] + (1 - c) * x[4];
    auto yp = c * kernel1(xp) + (1 - c) * kernel2(xp);
    assert(interpolant(xp).approxEqual(yp));
    // check parabolic extrapolation of the boundary intervals
    kernel1 = ParabolaKernel!double(x[0], x[1], x[2], y[0], y[1], y[2]);
    kernel2 = ParabolaKernel!double(x[$ - 3], x[$ - 2], x[$ - 1], y[$ - 3], y[$ - 2], y[$ - 1]);
    assert(interpolant(x[0] - 23.421).approxEqual(kernel1(x[0] - 23.421)));
    assert(interpolant(x[$ - 1] + 23.421).approxEqual(kernel2(x[$ - 1] + 23.421)));
}

///
@safe pure version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.functional: aliasCall;
    import mir.math.common: approxEqual;
    import mir.ndslice.allocation: uninitSlice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: vmap, map;

    auto x = rcarray!(immutable double)(-1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22).asSlice;
    auto y = rcarray(
       8.77842512,
       7.96429686,
       7.77074363,
       1.10838032,
       2.69925191,
       1.84922654,
       1.48167283,
       2.8267636 ,
       0.40200172,
       7.78980608).asSlice;

    auto interpolant = x.spline!double(y); // default boundary condition is 'not-a-knot'

    auto xs = x + 0.5;

    auto ys = xs.vmap(interpolant);

    auto r =
    [ 5.56971848,
        9.30342403,
        4.44139761,
        -0.74740285,
        3.00994108,
        1.50750417,
        1.73144979,
        2.64860361,
        0.64413911,
        10.81768928];

    assert(all!approxEqual(ys, r));

    // first derivative
    auto d1 = xs.vmap(interpolant.aliasCall!"withDerivative").map!"a[1]";
    auto r1 =
    [-4.51501279,
        2.15715986,
        -7.28363308,
        -2.14050449,
        0.03693092,
        -0.49618999,
        0.58109933,
        -0.52926703,
        0.7819035 ,
        6.70632693];
    assert(all!approxEqual(d1, r1));

    // second derivative
    auto d2 = xs.vmap(interpolant.aliasCall!"withTwoDerivatives").map!"a[2]";
    auto r2 =
    [ 7.07104751,
        -2.62293241,
        -0.01468508,
        5.70609505,
        -2.02358911,
        0.72142061,
        0.25275483,
        -0.6133589 ,
        1.26894416,
        2.68067146];
    assert(all!approxEqual(d2, r2));

    // third derivative (6 * a)
    auto d3 = xs.vmap(interpolant.aliasCall!("opCall", 3)).map!"a[3]";
    auto r3 =
    [-3.23132664,
        -3.23132664,
        14.91047457,
        -3.46891432,
        1.88520325,
        -0.16559031,
        -0.44056064,
        0.47057577,
        0.47057577,
        0.47057577];
    assert(all!approxEqual(d3, r3));
}

/// R -> R: Cubic interpolation
version(mir_test)
@safe unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice;

    static immutable x = [0, 1, 2, 3, 5.00274, 7.00274, 10.0055, 20.0137, 30.0192];
    static immutable y = [0.0011, 0.0011, 0.0030, 0.0064, 0.0144, 0.0207, 0.0261, 0.0329, 0.0356,];
    auto xs = [1, 2, 3, 4.00274, 5.00274, 6.00274, 7.00274, 8.00548, 9.00548, 10.0055, 11.0055, 12.0082, 13.0082, 14.0082, 15.0082, 16.011, 17.011, 18.011, 19.011, 20.0137, 21.0137, 22.0137, 23.0137, 24.0164, 25.0164, 26.0164, 27.0164, 28.0192, 29.0192, 30.0192];

    auto interpolation = spline!double(x.rcslice, y.sliced);

    auto data = 
      [ 0.0011    ,  0.003     ,  0.0064    ,  0.01042622,  0.0144    ,
        0.01786075,  0.0207    ,  0.02293441,  0.02467983,  0.0261    ,
        0.02732764,  0.02840225,  0.0293308 ,  0.03012914,  0.03081002,
        0.03138766,  0.03187161,  0.03227637,  0.03261468,  0.0329    ,
        0.03314357,  0.03335896,  0.03355892,  0.03375674,  0.03396413,
        0.03419436,  0.03446018,  0.03477529,  0.03515072,  0.0356    ];

    assert(all!approxEqual(xs.sliced.vmap(interpolation), data));
}

/// R^2 -> R: Bicubic interpolation
version(mir_test)
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice;
    alias appreq = (a, b) => approxEqual(a, b, 10e-10, 10e-10);

    ///// set test function ////
    const double y_x0 = 2;
    const double y_x1 = -7;
    const double y_x0x1 = 3;

    // this function should be approximated very well
    alias f = (x0, x1) => y_x0 * x0 + y_x1 * x1 + y_x0x1 * x0 * x1 - 11;

    ///// set interpolant ////
    static immutable x0 = [-1.0, 2, 8, 15];
    static immutable x1 = [-4.0, 2, 5, 10, 13];
    auto grid = cartesian(x0, x1);

    auto interpolant = spline!(double, 2)(x0.rcslice, x1.rcslice, grid.map!f);

    ///// compute test data ////
    auto test_grid = cartesian(x0.sliced + 1.23, x1.sliced + 3.23);
    // auto test_grid = cartesian(x0 + 0, x1 + 0);
    auto real_data = test_grid.map!f;
    auto interp_data = test_grid.vmap(interpolant);

    ///// verify result ////
    assert(all!appreq(interp_data, real_data));

    //// check derivatives ////
    auto z0 = 1.23;
    auto z1 = 3.21;
    // writeln("-----------------");
    // writeln("-----------------");
    auto d = interpolant.withDerivative(z0, z1);
    assert(appreq(interpolant(z0, z1), f(z0, z1)));
    // writeln("d = ", d);
    // writeln("interpolant.withTwoDerivatives(z0, z1) = ", interpolant.withTwoDerivatives(z0, z1));
    // writeln("-----------------");
    // writeln("-----------------");
    // writeln("interpolant(z0, z1) = ", interpolant(z0, z1));
    // writeln("y_x0 + y_x0x1 * z1 = ", y_x0 + y_x0x1 * z1);
    // writeln("y_x1 + y_x0x1 * z0 = ", y_x1 + y_x0x1 * z0);
    // writeln("-----------------");
    // writeln("-----------------");
    // assert(appreq(d[0][0], f(z0, z1)));
    // assert(appreq(d[1][0], y_x0 + y_x0x1 * z1));
    // assert(appreq(d[0][1], y_x1 + y_x0x1 * z0));
    // assert(appreq(d[1][1], y_x0x1));
}

/// R^3 -> R: Tricubic interpolation
version(mir_test)
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice;
    alias appreq = (a, b) => approxEqual(a, b, 10e-10, 10e-10);

    ///// set test function ////
    enum y_x0 = 2;
    enum y_x1 = -7;
    enum y_x2 = 5;
    enum y_x0x1 = 10;
    enum y_x0x1x2 = 3;

    // this function should be approximated very well
    alias f = (x0, x1, x2) => y_x0 * x0 + y_x1 * x1 + y_x2 * x2
         + y_x0x1 * x0 * x1 + y_x0x1x2 * x0 * x1 * x2 - 11;

    ///// set interpolant ////
    static immutable x0 = [-1.0, 2, 8, 15];
    static immutable x1 = [-4.0, 2, 5, 10, 13];
    static immutable x2 = [3, 3.7, 5];
    auto grid = cartesian(x0, x1, x2);

    auto interpolant = spline!(double, 3)(x0.rcslice, x1.rcslice, x2.rcslice, grid.map!f);

    ///// compute test data ////
    auto test_grid = cartesian(x0.sliced + 1.23, x1.sliced + 3.23, x2.sliced - 3);
    auto real_data = test_grid.map!f;
    auto interp_data = test_grid.vmap(interpolant);

    ///// verify result ////
    assert(all!appreq(interp_data, real_data));

    //// check derivatives ////
    auto z0 = 1.23;
    auto z1 = 3.23;
    auto z2 = -3;
    auto d = interpolant.withDerivative(z0, z1, z2);
    assert(appreq(interpolant(z0, z1, z2), f(z0, z1, z2)));
    assert(appreq(d[0][0][0], f(z0, z1, z2)));

    // writeln("-----------------");
    // writeln("-----------------");
    // auto d = interpolant.withDerivative(z0, z1);
    assert(appreq(interpolant(z0, z1, z2), f(z0, z1, z2)));
    // writeln("interpolant(z0, z1, z2) = ", interpolant(z0, z1, z2));
    // writeln("d = ", d);
    // writeln("interpolant.withTwoDerivatives(z0, z1, z2) = ", interpolant.withTwoDerivatives(z0, z1, z2));
    // writeln("-----------------");
    // writeln("-----------------");
    // writeln("interpolant(z0, z1) = ", interpolant(z0, z1));
    // writeln("y_x0 + y_x0x1 * z1 = ", y_x0 + y_x0x1 * z1);
    // writeln("y_x1 + y_x0x1 * z0 = ", y_x1 + y_x0x1 * z0);
    // writeln("-----------------");
    // writeln("-----------------");

    // writeln("y_x0 + y_x0x1 * z1 + y_x0x1x2 * z1 * z2 = ", y_x0 + y_x0x1 * z1 + y_x0x1x2 * z1 * z2);
    // assert(appreq(d[1][0][0], y_x0 + y_x0x1 * z1 + y_x0x1x2 * z1 * z2));
    // writeln("y_x1 + y_x0x1 * z0 + y_x0x1x2 * z0 * z2 = ", y_x1 + y_x0x1 * z0 + y_x0x1x2 * z0 * z2);
    // assert(appreq(d[0][1][0], y_x1 + y_x0x1 * z0 + y_x0x1x2 * z0 * z2));
    // writeln("y_x0x1 + y_x0x1x2 * z2 = ", y_x0x1 + y_x0x1x2 * z2);
    // assert(appreq(d[1][1][0], y_x0x1 + y_x0x1x2 * z2));
    // writeln("y_x0x1x2 = ", y_x0x1x2);
    // assert(appreq(d[1][1][1], y_x0x1x2));
}


/// Monotone PCHIP
version(mir_test)
@safe unittest
{
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;
    import mir.ndslice.allocation: rcslice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: vmap;

    static immutable x = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22];
    static immutable y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6];
    auto interpolant = spline!double(x.rcslice, y.sliced, SplineType.monotone);

    auto xs = x[0 .. $ - 1].sliced + 0.5;

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
}

// Check direction equality
version(mir_test)
@safe unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: rcslice;
    import mir.ndslice.topology: retro, map;

    static immutable points = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22];
    static immutable values = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6];

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
    auto interpolant = spline!double(points.rcslice, values.sliced, SplineType.monotone);

    auto pointsR = rcslice(-points.retro);
    auto valuesR = values.retro.rcslice;
    auto interpolantR = spline!double(pointsR, valuesR, SplineType.monotone);

    version(X86_64)
    assert(map!interpolant(points[0 .. $ - 1].sliced +  0.5) == map!interpolantR(pointsR.retro[0 .. $ - 1] - 0.5));
}

/++
Cubic Spline types.

The first derivatives are guaranteed to be continuous for all cubic splines.
+/
enum SplineType
{
    /++
    Spline with contiguous second derivative.
    +/
    c2,
    /++
    $(HTTPS en.wikipedia.org/wiki/Cubic_Hermite_spline#Cardinal_spline, Cardinal) and Catmull–Rom splines.
    +/
    cardinal,
    /++
    The interpolant preserves monotonicity in the interpolation data and does not overshoot if the data is not smooth.
    It is also known as   $(HTTPS docs.scipy.org/doc/scipy-0.18.1/reference/generated/scipy.interpolate.PchipInterpolator.html, PCHIP)
    in numpy and Matlab.
    +/
    monotone,
    /++
    Weighted sum of two nearbor quadratic functions.
    It is used in $(HTTPS s3-eu-west-1.amazonaws.com/og-public-downloads/smile-interpolation-extrapolation.pdf, financial analysis).
    +/
    doubleQuadratic,
    /++
    $(HTTPS en.wikipedia.org/wiki/Akima_spline, Akima spline).
    +/
    akima,
}

/++
Constructs multivariate cubic spline in symmetrical form with nodes on rectilinear grid.
Result has continues second derivatives throughout the curve / nd-surface.
+/
template spline(T, size_t N = 1, X = T)
    if (isFloatingPoint!T && is(T == Unqual!T) && N <= 6)
{
    /++
    Params:
        grid = immutable `x` values for interpolant
        values = `f(x)` values for interpolant
        typeOfBoundaries = $(LREF SplineBoundaryType) for both tails (optional).
        valueOfBoundaryConditions = value of the boundary type (optional). 
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(LREF Spline)
    +/
    Spline!(T, N, X) spline(yIterator, SliceKind ykind)(
        Repeat!(N, Slice!(RCI!(immutable X))) grid,
        Slice!(yIterator, N, ykind) values,
        SplineBoundaryType typeOfBoundaries = SplineBoundaryType.notAKnot,
        in T valueOfBoundaryConditions = 0,
        )
    {
        return spline(grid, values, SplineType.c2, 0, typeOfBoundaries, valueOfBoundaryConditions);
    }

    Spline!(T, N, X) spline(yIterator, SliceKind ykind)(
        Repeat!(N, Slice!(RCI!(immutable X))) grid,
        Slice!(yIterator, N, ykind) values,
        SplineType kind,
        in T param = 0,
        SplineBoundaryType typeOfBoundaries = SplineBoundaryType.notAKnot,
        in T valueOfBoundaryConditions = 0,
        )
    {
        return spline(grid, values, SplineBoundaryCondition!T(typeOfBoundaries, valueOfBoundaryConditions), kind, param);
    }

    /++
    Params:
        grid = immutable `x` values for interpolant
        values = `f(x)` values for interpolant
        boundaries = $(LREF SplineBoundaryCondition) for both tails.
        kind = $(LREF SplineType) type of cubic spline.
        param = tangent power parameter for cardinal $(LREF SplineType) (ignored by other spline types).
            Use `1` for zero derivatives at knots and `0` for Catmull–Rom spline.
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(LREF Spline)
    +/
    Spline!(T, N, X) spline(yIterator, SliceKind ykind)(
        Repeat!(N, Slice!(RCI!(immutable X))) grid,
        Slice!(yIterator, N, ykind) values,
        SplineBoundaryCondition!T boundaries,
        SplineType kind = SplineType.c2,
        in T param = 0,
        )
    {
        return spline(grid, values, boundaries, boundaries, kind, param);
    }

    /++
    Params:
        grid = immutable `x` values for interpolant
        values = `f(x)` values for interpolant
        rBoundary = $(LREF SplineBoundaryCondition) for left tail.
        lBoundary = $(LREF SplineBoundaryCondition) for right tail.
        kind = $(LREF SplineType) type of cubic spline.
        param = tangent power parameter for cardinal $(LREF SplineType) (ignored by other spline types).
            Use `1` for zero derivatives at knots and `0` for Catmull–Rom spline.
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(LREF Spline)
    +/
    Spline!(T, N, X) spline(yIterator, SliceKind ykind)(
        Repeat!(N, Slice!(RCI!(immutable X))) grid,
        Slice!(yIterator, N, ykind) values,
        SplineBoundaryCondition!T rBoundary,
        SplineBoundaryCondition!T lBoundary,
        SplineType kind = SplineType.c2,
        in T param = 0,
        )
    {
        auto ret = typeof(return)(forward!grid);
        ret._values = values;
        ret._computeDerivatives(kind, param, rBoundary, lBoundary);
        return ret;
    }
}

/++
Cubic Spline Boundary Condition Type.

See_also: $(LREF SplineBoundaryCondition) $(LREF SplineType)
+/
enum SplineBoundaryType
{
    /++
    Not implemented.
    +/
    periodic = -1,
    /++
    Not-a-knot (or cubic) boundary condition.
    It is an aggresive boundary condition that is used only for C2 splines and is default for all API calls.
    For other then C2 splines, `notAKnot` is changed internally to
    a default boundary type for used $(LREF SplineType).
    +/
    notAKnot,
    /++
    Set the first derivative.
    +/
    firstDerivative,
    /++
    Set the second derivative.
    +/
    secondDerivative,
    /++
    Default for Cardinal and Double-Quadratic splines.
    +/
    parabolic,
    /++
    Default for monotone (aka PHCIP ) splines.
    +/
    monotone,
    /++
    Default for Akima splines.
    +/
    akima,
}

/++
Cubic Spline  Boundary Condition

See_also: $(LREF SplineBoundaryType)
+/
struct SplineBoundaryCondition(T)
{
    /// type (default is $(LREF SplineBoundaryType.notAKnot))
    SplineBoundaryType type = SplineBoundaryType.notAKnot;
    /// value (default is 0)
    T value = 0;
}

/++
Multivariate cubic spline with nodes on rectilinear grid.
+/
struct Spline(F, size_t N = 1, X = F)
    if (N && N <= 6)
{
    import mir.rc.array;

    /// Aligned buffer allocated with `mir.internal.memory`. $(RED For internal use.)
    Slice!(RCI!(F[2 ^^ N]), N) _data;
    /// Grid iterators. $(RED For internal use.)
    RCI!(immutable X)[N] _grid;

@optmath extern(D):

    /++
    +/
    this(Repeat!(N, Slice!(RCI!(immutable X))) grid) @safe @nogc
    {
        size_t length = 1;
        size_t[N] shape;
        enum  msg =  "spline interpolant: minimal allowed length for the grid equals 2.";
        version(D_Exceptions)
            static immutable exc = new Exception(msg);
        foreach(i, ref x; grid)
        {
            if (x.length < 2)
            {
                version(D_Exceptions) throw exc;
                else assert(0, msg);
            }
            length *= shape[i] = x.length;
            this._grid[i] = x._iterator.move;
        }
        import mir.ndslice.allocation: rcslice;
        this._data = shape.rcslice!(F[2 ^^ N]);
    }

    package static auto pickDataSubslice(D)(auto scope ref D data, size_t index) @trusted
    {
        auto strides = data.strides;
        foreach (i; Iota!(strides.length))
            strides[i] *= DeepElementType!D.length;
        return Slice!(F*, strides.length, Universal)(data.shape, strides, data._iterator._iterator.ptr + index);
    }

    /++
    Assigns function values to the internal memory.
    $(RED For internal use.)
    +/
    void _values(SliceKind kind, Iterator)(Slice!(Iterator, N, kind) values) scope @property @trusted
    {
        assert(values.shape == _data.shape, "'values' should have the same shape as the .gridShape");
        pickDataSubslice(_data, 0)[] = values;
    }

    /++
    Computes derivatives and stores them in `_data`.
    `_data` is assumed to be preinitialized with function values filled in `F[2 ^^ N][0]`.
    Params:
        lbc = left boundary condition
        rbc = right boundary condition
        temp = temporal buffer length points count (optional)

    $(RED For internal use.)
    +/
    void _computeDerivatives(SplineType kind, F param, SplineBoundaryCondition!F lbc, SplineBoundaryCondition!F rbc) scope @trusted nothrow @nogc
    {
        import mir.algorithm.iteration: maxLength;
        auto ml = this._data.maxLength;
        auto temp = RCArray!F(ml);
        auto tempSlice = temp[].sliced;
        _computeDerivativesTemp(kind, param, lbc, rbc, tempSlice);
    }

    /// ditto
    pragma(inline, false)
    void _computeDerivativesTemp(SplineType kind, F param, SplineBoundaryCondition!F lbc, SplineBoundaryCondition!F rbc, Slice!(F*) temp) scope @system nothrow @nogc
    {
        import mir.algorithm.iteration: maxLength, each;
        import mir.ndslice.topology: map, byDim, evertPack;

        assert(temp.length >= _data.maxLength);

        static if (N == 1)
        {
            splineSlopes!(F, F)(_grid[0].lightConst.sliced(_data._lengths[0]), pickDataSubslice(_data, 0), pickDataSubslice(_data, 1), temp[0 .. _data._lengths[0]], kind, param, lbc, rbc);
        }
        else
        foreach_reverse(i; Iota!N)
        {
            // if (i == _grid.length - 1)
            _data
                .byDim!i
                .evertPack
                .each!((d){
                    enum L = 2 ^^ (N - 1 - i);
                    foreach(l; Iota!L)
                    {
                        auto y = pickDataSubslice(d, l);
                        auto s = pickDataSubslice(d, L + l);
                        // debug printf("ptr = %ld, stride = %ld, stride = %ld, d = %ld i = %ld l = %ld\n", d.iterator, d._stride!0, y._stride!0, d.length, i, l);
                        splineSlopes!(F, F)(_grid[i].sliced(_data._lengths[i]), y, s, temp[0 .. _data._lengths[i]], kind, param, lbc, rbc);
                        // debug{
                        //     (cast(void delegate() @nogc)(){
                        //     writeln("y = ", y);
                        //     writeln("s = ", s);
                        //     })();
                        // }
                    }
            });
        }
    }

@trusted:

    ///
    Spline lightConst() const @property { return *cast(Spline*)&this; }
    ///
    Spline lightImmutable() immutable @property { return *cast(Spline*)&this; }

    ///
    Slice!(RCI!(immutable X)) grid(size_t dimension = 0)() scope return const @property
        if (dimension < N)
    {
        return _grid[dimension].lightConst.sliced(_data._lengths[dimension]);
    }

    /++
    Returns: intervals count.
    +/
    size_t intervalCount(size_t dimension = 0)() scope const @property
    {
        assert(_data._lengths[dimension] > 1);
        return _data._lengths[dimension] - 1;
    }

    ///
    size_t[N] gridShape() scope const @property
    {
        return _data.shape;
    }

    ///
    alias withDerivative = opCall!1;
    ///
    alias withTwoDerivatives = opCall!2;

    ///
    enum uint derivativeOrder = 3;

    ///
    template opCall(uint derivative : 2)
    {
         auto opCall(X...)(in X xs) scope const
            if (X.length == N)
            // @FUTURE@
            // X.length == N || derivative == 0 && X.length && X.length <= N
        {
            auto d4 = this.opCall!3(xs);
            SplineReturnType!(F, N, 3) d3;
            void fun(size_t d, A, B)(ref A a, ref B b)
            {
                static if (d)
                    foreach(i; Iota!3)
                        fun!(d - 1)(a[i], b[i]);
                else
                    b = a;
            }
            fun!N(d4, d3);
            return d3;
        }
    }

    ///
    template opCall(uint derivative = 0)
        if (derivative == 0 || derivative == 1 || derivative == 3)
    {
        static if (N > 1 && derivative) pragma(msg, "Warning: multivariate cubic spline with derivatives was not tested!!!");
        
        /++
        `(x)` operator.
        Complexity:
            `O(log(points.length))`
        +/
        auto opCall(X...)(in X xs) scope const @trusted
            if (X.length == N)
            // @FUTURE@
            // X.length == N || derivative == 0 && X.length && X.length <= N
        {
            import mir.ndslice.topology: iota;
            alias Kernel = AliasCall!(SplineKernel!F, "opCall", derivative);
            enum rp2d = derivative == 3 ? 2 : derivative;

            size_t[N] indexes = void;
            Kernel[N] kernels = void;

            foreach(i; Iota!N)
            {
                static if (isInterval!(typeof(xs[i])))
                {
                    indexes[i] = xs[i][1];
                    auto x = xs[i][0];
                }
                else
                {
                    alias x = xs[i];
                    indexes[i] = this.findInterval!i(x);
                }
                kernels[i] = SplineKernel!F(_grid[i][indexes[i]], _grid[i][indexes[i] + 1], x);
            }

            align(64) F[2 ^^ N * 2 ^^ N][2] local = void;

            void load(sizediff_t i)(const(F[2 ^^ N])* from, F[2 ^^ N]* to)
            {
                version(LDC) pragma(inline, true);
                static if (i == -1)
                {
                    // copyvec(*from, *to);
                    // not aligned:
                    *to = *from;
                }
                else
                {
                    from += strides[i] * indexes[i];
                    load!(i - 1)(from, to);
                    from += strides[i];
                    enum s = 2 ^^ (N - 1 - i);
                    to += s;
                    load!(i - 1)(from, to);
                }
            }

            immutable strides = _data._lengths.iota.strides;
            load!(N - 1)(_data.ptr, cast(F[2 ^^ N]*) local[0].ptr);

                // debug{

                //         printf("0local[0] = ");
                //         foreach(ref e; local[0][])
                //             printf("%f ", e);
                //         printf("\n");
                // }

            foreach(i; Iota!N)
            {
                enum P = 2 ^^ (N - 1 - i) * 2 ^^ (i * rp2d);
                enum L = (2 ^^ N) ^^ 2 / (2 ^^ (i * (2 - rp2d))) / 4;
                shuffle2!P(local[0][0 * L .. 1 * L], local[0][1 * L .. 2 * L], local[1][0 * L .. 1 * L], local[1][1 * L .. 2 * L]);
                shuffle2!P(local[0][2 * L .. 3 * L], local[0][3 * L .. 4 * L], local[1][2 * L .. 3 * L], local[1][3 * L .. 4 * L]);
                // debug
                // {
                //         printf("0local[1] = ");
                //         foreach(ref e; local[1][0 ..  L* 4])
                //             printf("%f ", e);
                //         printf("\n");
                // }
                local[0][] = F.init;
                vectorize(
                    kernels[i],
                    local[1][0 * L .. 1 * L], local[1][2 * L .. 3 * L],
                    local[1][1 * L .. 2 * L], local[1][3 * L .. 4 * L],
                    *cast(F[L][2 ^^ rp2d]*) local[0].ptr,
                    );

                // debug{

                //         printf("1local[0] = ");
                //         foreach(ref e; local[0][0 .. L* 2 ^^ rp2d])
                //             printf("%f ", e);
                //         printf("\n");
                // }
                // printf("local[0][0]", local[0][0]);
                static if (i + 1 == N)
                {
                    return *cast(SplineReturnType!(F, N, 2 ^^ rp2d)*) local[0].ptr;
                }
                else
                {
                    static if (rp2d == 1)
                    {
                        shuffle3!1(local[0][0 .. L], local[0][L .. 2 * L], local[1][0 .. L], local[1][L .. 2 * L]);
                        copyvec(local[1][0 .. 1 * L], local[0][0 .. 1 * L]);
                        copyvec(local[1][L .. 2 * L], local[0][L .. 2 * L]);
                    }
                    else
                    static if (rp2d == 2)
                    {
                        shuffle3!1(local[0][0 * L .. 1 * L], local[0][1 * L .. 2 * L], local[1][0 * L .. 1 * L], local[1][1 * L .. 2 * L]);
                        shuffle3!1(local[0][2 * L .. 3 * L], local[0][3 * L .. 4 * L], local[1][2 * L .. 3 * L], local[1][3 * L .. 4 * L]);
                        shuffle3!2(local[1][0 * L .. 1 * L], local[1][2 * L .. 3 * L], local[0][0 * L .. 1 * L], local[0][2 * L .. 3 * L]);
                        shuffle3!2(local[1][1 * L .. 2 * L], local[1][3 * L .. 4 * L], local[0][1 * L .. 2 * L], local[0][3 * L .. 4 * L]);
                    }

                // debug{

                //         printf("2local[0] = ");
                //         foreach(ref e; local[0][0 .. L * 2 ^^ rp2d])
                //             printf("%f ", e);
                //         printf("\n");
                // }

                }
            }
        }
    }
}

/++
Piecewise cubic hermite interpolating polynomial.
Params:
    points = `x` values for interpolant
    values = `f(x)` values for interpolant
    slopes = uninitialized ndslice to write slopes into
    temp = uninitialized temporary ndslice
    kind = $(LREF SplineType) type of cubic spline.
    param = tangent power parameter for cardinal $(LREF SplineType) (ignored by other spline types).
        Use `1` for zero derivatives at knots and `0` for Catmull–Rom spline.
    lbc = left boundary condition
    rbc = right boundary condition
Constraints:
    `points`, `values`, and `slopes`, must have the same length > 3;
    `temp` must have length greater or equal to points less minus one.
+/
void splineSlopes(F, T, IP, IV, IS, SliceKind gkind, SliceKind vkind, SliceKind skind)(
    Slice!(IP, 1, gkind) points,
    Slice!(IV, 1, vkind) values,
    Slice!(IS, 1, skind) slopes,
    Slice!(T*) temp,
    SplineType kind,
    F param,
    SplineBoundaryCondition!F lbc,
    SplineBoundaryCondition!F rbc,
    ) @trusted
{
    import mir.ndslice.topology: diff, zip, slide;

    assert (points.length >= 2);
    assert (points.length == values.length);
    assert (points.length == slopes.length);
    assert (temp.length == points.length);

    auto n = points.length;


    typeof(slopes[0]) first, last;

    auto xd = points.diff;
    auto yd = values.diff;
    auto dd = yd / xd;
    auto dd2 = points.zip(values).slide!(3, "(c[1] - a[1]) / (c[0] - a[0])");

    with(SplineType) final switch(kind)
    {
        case c2:
            break;
        case cardinal:
            if (lbc.type == SplineBoundaryType.notAKnot)
                lbc.type = SplineBoundaryType.parabolic;
            if (rbc.type == SplineBoundaryType.notAKnot)
                rbc.type = SplineBoundaryType.parabolic;
            break;
        case monotone:
            if (lbc.type == SplineBoundaryType.notAKnot)
                lbc.type = SplineBoundaryType.monotone;
            if (rbc.type == SplineBoundaryType.notAKnot)
                rbc.type = SplineBoundaryType.monotone;
            break;
        case doubleQuadratic:
            if (lbc.type == SplineBoundaryType.notAKnot)
                lbc.type = SplineBoundaryType.parabolic;
            if (rbc.type == SplineBoundaryType.notAKnot)
                rbc.type = SplineBoundaryType.parabolic;
            break;
        case akima:
            if (lbc.type == SplineBoundaryType.notAKnot)
                lbc.type = SplineBoundaryType.akima;
            if (rbc.type == SplineBoundaryType.notAKnot)
                rbc.type = SplineBoundaryType.akima;
            break;
    }

    if (n <= 3)
    {
        if (lbc.type == SplineBoundaryType.notAKnot)
            lbc.type = SplineBoundaryType.parabolic;
        if (rbc.type == SplineBoundaryType.notAKnot)
            rbc.type = SplineBoundaryType.parabolic;

        if (n == 2)
        {
            if (lbc.type == SplineBoundaryType.monotone
             || lbc.type == SplineBoundaryType.akima)
                lbc.type = SplineBoundaryType.parabolic;
            if (rbc.type == SplineBoundaryType.monotone
             || rbc.type == SplineBoundaryType.akima)
                rbc.type = SplineBoundaryType.parabolic;
        }
        /// special case
        if (rbc.type == SplineBoundaryType.parabolic
         && lbc.type == SplineBoundaryType.parabolic)
        {
            import mir.interpolate.utility;
            if (n == 3)
            {
                auto derivatives = parabolaDerivatives(points[0], points[1], points[2], values[0], values[1], values[2]);
                slopes[0] = derivatives[0];
                slopes[1] = derivatives[1];
                slopes[2] = derivatives[2];
            }
            else
            {
                assert(slopes.length == 2);
                slopes.back = slopes.front = yd.front / xd.front;
            }
            return;
        }
    }

    with(SplineBoundaryType) final switch(lbc.type)
    {
    case periodic:

        assert(0);

    case notAKnot:

        auto dx0 = xd[0];
        auto dx1 = xd[1];
        auto dy0 = yd[0];
        auto dy1 = yd[1];
        auto dd0 = dy0 / dx0;
        auto dd1 = dy1 / dx1;

        slopes.front = dx1;
        first = dx0 + dx1;
        temp.front = ((dx0 + 2 * first) * dx1 * dd0 + dx0 ^^ 2 * dd1) / first;
        break;
    
    case firstDerivative:

        slopes.front = 1;
        first = 0;
        temp.front = lbc.value;
        break;

    case secondDerivative:

        slopes.front = 2;
        first = 1;
        temp.front = 3 * dd.front - 0.5 * lbc.value * xd.front;
        break;

    case parabolic:

        slopes.front = 1;
        first = 1;
        temp.front = 2 * dd.front;
        break;
    
    case monotone:

        slopes.front = 1;
        first = 0;
        temp.front = pchipTail(xd[0], xd[1], dd[0], dd[1]);
        break;

    case akima:

        slopes.front = 1;
        first = 0;
        temp.front = akimaTail(dd[0], dd[1]);
        break;

    }

    with(SplineBoundaryType) final switch(rbc.type)
    {
    case periodic:
        assert(0);

    case notAKnot:

        auto dx0 = xd[$ - 1];
        auto dx1 = xd[$ - 2];
        auto dy0 = yd[$ - 1];
        auto dy1 = yd[$ - 2];
        auto dd0 = dy0 / dx0;
        auto dd1 = dy1 / dx1;
        slopes.back = dx1;
        last = dx0 + dx1;
        temp.back = ((dx0 + 2 * last) * dx1 * dd0 + dx0 ^^ 2 * dd1) / last;
        break;
    
    case firstDerivative:

        slopes.back = 1;
        last = 0;
        temp.back = rbc.value;
        break;

    case secondDerivative:

        slopes.back = 2;
        last = 1;
        temp.back = 3 * dd.back + 0.5 * rbc.value * xd.back;
        break;

    case parabolic:

        slopes.back = 1;
        last = 1;
        temp.back = 2 * dd.back;
        break;

    case monotone:

        slopes.back = 1;
        last = 0;
        temp.back = pchipTail(xd[$ - 1], xd[$ - 2], dd[$ - 1], dd[$ - 2]);
        break;

    case akima:

        slopes.back = 1;
        last = 0;
        temp.back = akimaTail(dd[$ - 1], dd[$ - 2]);
        break;

    }

    with(SplineType) final switch(kind)
    {
        case c2:

            foreach (i; 1 .. n - 1)
            {
                auto dx0 = xd[i - 1];
                auto dx1 = xd[i - 0];
                auto dy0 = yd[i - 1];
                auto dy1 = yd[i - 0];
                slopes[i] = 2 * (dx0 + dx1);
                temp[i] = 3 * (dy0 / dx0 * dx1 + dy1 / dx1 * dx0);
            }
            break;

        case cardinal:

            foreach (i; 1 .. n - 1)
            {
                slopes[i] = 1;
                temp[i] = (1 - param) * dd2[i - 1];
            }
            break;

        case monotone:
            {
                auto step0 = cast()xd[0];
                auto step1 = cast()xd[1];
                auto diff0 = cast()yd[0];
                auto diff1 = cast()yd[1];
                diff0 /= step0;
                diff1 /= step1;

                for(size_t i = 1;;)
                {
                    slopes[i] = 1;
                    if (diff0 && diff1 && copysign(1f, diff0) == copysign(1f, diff1))
                    {
                        auto w0 = step1 * 2 + step0;
                        auto w1 = step0 * 2 + step1;
                        temp[i] = (w0 + w1) / (w0 / diff0 + w1 / diff1);
                    }
                    else
                    {
                        temp[i] = 0;
                    }
                    if (++i == n - 1)
                    {
                        break;
                    }
                    step0 = step1;
                    diff0 = diff1;
                    step1 = xd[i];
                    diff1 = yd[i];
                    diff1 /= step1;
                }
            }
            break;

        case doubleQuadratic:

            foreach (i; 1 .. n - 1)
            {
                slopes[i] = 1;
                temp[i] = dd[i - 1] + dd[i] - dd2[i - 1];
            }
            break;

        case akima:
            {
                auto d3 = dd[1];
                auto d2 = dd[0];
                auto d1 = 2 * d2 - d3;
                auto d0 = d1;
                foreach (i; 1 .. n - 1)
                {
                    d0 = d1;
                    d1 = d2;
                    d2 = d3;
                    d3 = i == n - 2 ? 2 * d2 - d1 : dd[i + 1];
                    slopes[i] = 1;
                    temp[i] = akimaSlope(d0, d1, d2, d3);
                }
                break;
            }
    }

    foreach (i; 0 .. n - 1)
    {
        auto c = i ==     0 ? first : kind == SplineType.c2 ? xd[i - 1] : 0;
        auto a = i == n - 2 ?  last : kind == SplineType.c2 ? xd[i + 1] : 0;
        auto w = slopes[i] == 1 ? a : a / slopes[i];
        slopes[i + 1] -= w * c;
        temp[i + 1] -= w * temp[i];
    }

    slopes.back = temp.back / slopes.back;

    foreach_reverse (i; 0 .. n - 1)
    {
        auto c = i ==     0 ? first : kind == SplineType.c2 ? xd[i - 1] : 0;
        auto v = temp[i] - c * slopes[i + 1];
        slopes[i] = slopes[i]  == 1 ? v : v / slopes[i];
    }
}

private F akimaTail(F)(in F d2, in F d3)
{
    auto d1 = 2 * d2 - d3;
    auto d0 = 2 * d1 - d2;
    return akimaSlope(d0, d1, d2, d3);
}

private F akimaSlope(F)(in F d0, in F d1, in F d2, in F d3)
{
    if (d1 == d2)
        return d1;
    if (d0 == d1 && d2 == d3)
        return (d1 + d2) * 0.5f;
    if (d0 == d1)
        return d1;
    if (d2 == d3)
        return d2;
    auto w0 = fabs(d1 - d0);
    auto w1 = fabs(d3 - d2);
    auto ws = w0 + w1;
    w0 /= ws;
    w1 /= ws;
    return w0 * d2 + w1 * d1;
}

///
struct SplineKernel(X)
{
    X step = 0;
    X w0 = 0;
    X w1 = 0;
    X wq = 0;

    ///
    this(X x0, X x1, X x)
    {
        step = x1 - x0;
        auto c0 = x - x0;
        auto c1 = x1 - x;
        w0 = c0 / step;
        w1 = c1 / step;
        wq = w0 * w1;
    }

    ///
    template opCall(uint derivative = 0)
        if (derivative <= 3)
    {
        ///
        auto opCall(Y)(in Y y0, in Y y1, in Y s0, in Y s1) const
        {
            auto diff = y1 - y0;
            auto z0 = s0 * step - diff;
            auto z1 = s1 * step - diff;
            auto a0 = z0 * w1;
            auto a1 = z1 * w0;
            auto pr = a0 - a1;
            auto b0 = y0 * w1;
            auto b1 = y1 * w0;
            auto pl = b0 + b1;
            auto y = pl + wq * pr;
            static if (derivative)
            {
                Y[derivative + 1] ret = 0;
                ret[0] = y;
                auto wd = w1 - w0;
                auto zd = z1 + z0;
                ret[1] = (diff + (wd * pr - wq * zd)) / step;
                static if (derivative > 1)
                {
                    auto astep = zd / (step * step);
                    ret[2] = -3 * wd * astep + (s1 - s0) / step;
                    static if (derivative > 2)
                        ret[3] = 6 * astep / step;
                }
                return ret;
            }
            else
            {
                return y;
            }
        }
    }

    ///
    alias withDerivative = opCall!1;
    ///
    alias withTwoDerivatives = opCall!2;
}

package T pchipTail(T)(in T step0, in T step1, in T diff0, in T diff1)
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
