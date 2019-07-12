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

public import mir.interpolate: atInterval;
import mir.interpolate;
import mir.interpolate: Repeat;

// Rectilinear grid - default
// Regular grid - linspace
// Cartesian grid with uniblocks - iota

import std.traits;
import std.meta;
import mir.primitives;
import mir.functional;
import mir.internal.utility: Iota;
import mir.math.common: fmamath;
import mir.ndslice.internal;
import mir.ndslice.slice;
import mir.ndslice.traits;

@fmamath:

///
@trusted pure version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: vmap;

    auto x = [-1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].idup.sliced;
    auto y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6].idup.sliced;

    auto interpolant = spline!double(x, y); // constructs Spline
    auto xs = x + 0.5;                     // input X values for cubic spline

    /// not-a-knot (default)
    assert(xs.vmap(interpolant).all!approxEqual([
        -0.68361541,   7.28568719,  10.490694  ,   0.36192032,
        11.91572713,  16.44546433,  17.66699525,   4.52730869,
        19.22825394,  -2.3242592 ]));

    /// natural cubic spline
    interpolant = spline!double(x, y, SplineBoundaryType.secondDerivative);
    assert(xs.vmap(interpolant).all!approxEqual([
        10.85298372,   5.26255911,  10.71443229,   0.1824536 ,
        11.94324989,  16.45633939,  17.59185094,   4.86340188,
        17.8565408 ,   2.81856494]));

    /// set both boundary derivatives to 3
    interpolant = spline!double(x, y, SplineBoundaryType.firstDerivative, 3);
    assert(xs.vmap(interpolant).all!approxEqual([
        16.45728263,   4.27981687,  10.82295092,   0.09610695,
        11.95252862,  16.47583126,  17.49964521,   5.26561539,
        16.21803478,   8.96104974]));

    /// different boundary conditions
    interpolant = spline!double(x, y,
            SplineBoundaryCondition!double(SplineBoundaryType.firstDerivative, 3),
            SplineBoundaryCondition!double(SplineBoundaryType.secondDerivative, -5));
    assert(xs.vmap(interpolant).all!approxEqual([
            16.45730084,   4.27966112,  10.82337171,   0.09403945,
            11.96265209,  16.44067375,  17.6374694 ,   4.67438921,
            18.6234452 ,  -0.05582876]));
    // ditto
    interpolant = spline!double(x, y,
            SplineBoundaryCondition!double(SplineBoundaryType.secondDerivative, -5),
            SplineBoundaryCondition!double(SplineBoundaryType.firstDerivative, 3));
    assert(xs.vmap(interpolant).all!approxEqual([
            12.37135558,   4.99638066,  10.74362441,   0.16008641,
            11.94073593,  16.47908148,  17.49841853,   5.26600921,
            16.21796051,   8.96102894]));
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

    auto x = [-1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22].idup.sliced;
    auto y = [
       8.77842512,
       7.96429686,
       7.77074363,
       1.10838032,
       2.69925191,
       1.84922654,
       1.48167283,
       2.8267636 ,
       0.40200172,
       7.78980608].sliced;
    
    auto interpolant = x.spline!double(y); // default boundary condition is 'not-a-knot'

    auto xs = x + 0.5;

    ()@trusted{

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
    }();
}

/// R -> R: Cubic interpolation
version(mir_test)
@safe unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice;

    immutable x = [0, 1, 2, 3, 5.00274, 7.00274, 10.0055, 20.0137, 30.0192];
    auto y = [0.0011, 0.0011, 0.0030, 0.0064, 0.0144, 0.0207, 0.0261, 0.0329, 0.0356,];
    auto xs = [1, 2, 3, 4.00274, 5.00274, 6.00274, 7.00274, 8.00548, 9.00548, 10.0055, 11.0055, 12.0082, 13.0082, 14.0082, 15.0082, 16.011, 17.011, 18.011, 19.011, 20.0137, 21.0137, 22.0137, 23.0137, 24.0164, 25.0164, 26.0164, 27.0164, 28.0192, 29.0192, 30.0192];

    auto interpolation = spline!double(x.sliced, y.sliced);

    auto data = 
      [ 0.0011    ,  0.003     ,  0.0064    ,  0.01042622,  0.0144    ,
        0.01786075,  0.0207    ,  0.02293441,  0.02467983,  0.0261    ,
        0.02732764,  0.02840225,  0.0293308 ,  0.03012914,  0.03081002,
        0.03138766,  0.03187161,  0.03227637,  0.03261468,  0.0329    ,
        0.03314357,  0.03335896,  0.03355892,  0.03375674,  0.03396413,
        0.03419436,  0.03446018,  0.03477529,  0.03515072,  0.0356    ];

    ()@trusted{
        assert(all!approxEqual(xs.sliced.vmap(interpolation), data));
    }();
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
    auto x0 = [-1.0, 2, 8, 15].idup.sliced;
    auto x1 = [-4.0, 2, 5, 10, 13].idup.sliced;
    auto grid = cartesian(x0, x1);

    auto interpolant = spline!(double, 2)(x0, x1, grid.map!f);

    ///// compute test data ////
    auto test_grid = cartesian(x0 + 1.23, x1 + 3.23);
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
    const y_x0 = 2;
    const y_x1 = -7;
    const y_x2 = 5;
    const y_x0x1 = 10;
    const y_x0x1x2 = 3;

    // this function should be approximated very well
    alias f = (x0, x1, x2) => y_x0 * x0 + y_x1 * x1 + y_x2 * x2
         + y_x0x1 * x0 * x1 + y_x0x1x2 * x0 * x1 * x2 - 11;

    ///// set interpolant ////
    auto x0 = [-1.0, 2, 8, 15].idup.sliced;
    auto x1 = [-4.0, 2, 5, 10, 13].idup.sliced;
    auto x2 = [3, 3.7, 5].idup.sliced;
    auto grid = cartesian(x0, x1, x2);

    auto interpolant = spline!(double, 3)(x0, x1, x2, grid.map!f);

    ///// compute test data ////
    auto test_grid = cartesian(x0 + 1.23, x1 + 3.23, x2 - 3);
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

/++
Constructs multivariate cubic spline in symmetrical form with nodes on rectilinear grid.
Result has continues second derivatives throughout the curve / nd-surface.
+/
template spline(T, size_t N = 1, FirstGridIterator = immutable(T)*, NextGridIterators = Repeat!(N - 1, FirstGridIterator))
    if (isFloatingPoint!T && is(T == Unqual!T) && N <= 6)
{
    private alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    private alias GridVectors = Spline!(T, N, GridIterators).GridVectors;

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
    Spline!(T, N, GridIterators) spline(yIterator, SliceKind ykind)(
        GridVectors grid,
        Slice!(yIterator, N, ykind) values,
        SplineBoundaryType typeOfBoundaries = SplineBoundaryType.notAKnot,
        in T valueOfBoundaryConditions = 0,
        )
    {
        return spline(grid, values, SplineBoundaryCondition!T(typeOfBoundaries, valueOfBoundaryConditions));
    }

    /++
    Params:
        grid = immutable `x` values for interpolant
        values = `f(x)` values for interpolant
        boundaries = $(LREF SplineBoundaryCondition) for both tails.
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(LREF Spline)
    +/
    Spline!(T, N, GridIterators) spline(yIterator, SliceKind ykind)(
        GridVectors grid,
        Slice!(yIterator, N, ykind) values,
        SplineBoundaryCondition!T boundaries,
        )
    {
        return spline(grid, values, boundaries, boundaries);
    }

    /++
    Params:
        grid = immutable `x` values for interpolant
        values = `f(x)` values for interpolant
        rBoundary = $(LREF SplineBoundaryCondition) for left tail.
        lBoundary = $(LREF SplineBoundaryCondition) for right tail.
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(LREF Spline)
    +/
    Spline!(T, N, GridIterators) spline(yIterator, SliceKind ykind)(
        GridVectors grid,
        Slice!(yIterator, N, ykind) values,
        SplineBoundaryCondition!T rBoundary,
        SplineBoundaryCondition!T lBoundary,
        )
    {
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        auto ret = typeof(return)(grid);
        ret._values = values;
        ret._computeDerivatives(rBoundary, lBoundary);
        return ret.move;
    }
}

/++
Cubic Spline  Boundary Condition Type

See_also: $(LREF SplineBoundaryCondition)
+/
enum SplineBoundaryType
{
    /// not implemented
    periodic = -1,
    /// (default)
    notAKnot,
    /// set the first derivative
    firstDerivative,
    /// set the second derivative
    secondDerivative,
    ///
    parabolic,
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

// private auto iter(alias s) = s.iterator;

/++
Multivariate cubic spline with nodes on rectilinear grid.
+/
struct Spline(F, size_t N = 1, FirstGridIterator = immutable(F)*, NextGridIterators...)
    if (N && N <= 6 && NextGridIterators.length == N - 1)
{
    import mir.rc.array;

    package alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    package alias GridVectors = staticMap!(GridVector, GridIterators);

@fmamath:

    /// Aligned buffer allocated with `mir.internal.memory`. $(RED For internal use.)
    mir_slice!(mir_rci!(F[2 ^^ N]), N) _data;
    /// Grid iterators. $(RED For internal use.)
    GridIterators _grid;

    import mir.utility: min, max;
    package enum alignment = min(64u, F[2 ^^ N].sizeof).max(size_t.sizeof);

    /++
    +/
    this(GridVectors grid) @safe @nogc
    {
        size_t length = 1;
        size_t[N] shape;
        enum  msg =  "spline/pchip interpolant: minimal allowed length for the grid equals 2.";
        version(D_Exceptions)
            static immutable exc = new Exception(msg);
        foreach(i, ref x; grid)
        {
            if (x.length < 2)
            {
                version(D_Exceptions)
                    throw exc;
                else
                    assert(0, msg);
            }
            length *= shape[i] = x.length;
        }

        auto rca = mir_rcarray!(F[2 ^^ N])(length);
        this._data = rca.asSlice.sliced(shape);
        this._grid = staticMap!(iter, grid);
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

    $(RED For internal use.)
    +/
    void _computeDerivatives()(SplineBoundaryCondition!F lbc, SplineBoundaryCondition!F rbc) scope @trusted nothrow @nogc
    {
        import mir.internal.memory;
        import mir.algorithm.iteration: maxLength;
        auto ml = this._data.maxLength;
        auto temp_ptr = cast(F*) alignedAllocate(F[2 ^^ (N - 1)].sizeof * ml, alignment);
        if (temp_ptr is null)
            assert(0);
        debug
        {
            temp_ptr.sliced(ml)[] = F.init;
        }
        _computeDerivativesTemp(lbc, rbc, temp_ptr.sliced(ml));
        alignedFree(temp_ptr);
    }

    /// ditto
    pragma(inline, false)
    void _computeDerivativesTemp()(SplineBoundaryCondition!F lbc, SplineBoundaryCondition!F rbc, Slice!(F*) temp) scope @system nothrow @nogc
    {
        import mir.internal.memory;
        import mir.algorithm.iteration: maxLength, each;
        import mir.ndslice.topology: map, byDim, evertPack;

        assert(temp.length >= _data.maxLength);

        static if (N == 1)
        {
            splineSlopes!(F, F)(_grid.sliced(_data._lengths[0]), pickDataSubslice(_data, 0), pickDataSubslice(_data, 1), temp, lbc, rbc);
        }
        else
        foreach_reverse(i, ref x; _grid)
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
                        splineSlopes!(F, F)(x.sliced(_data._lengths[i]), y, s, temp, lbc, rbc);
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
    Spline lightConst()() const @property { return *cast(Spline*)&this; }
    ///
    Spline lightImmutable()() immutable @property { return *cast(Spline*)&this; }

    ///
    GridVectors[dimension] grid(size_t dimension = 0)() scope return const @property
        if (dimension < N)
    {
        return _grid[dimension].sliced(_data._lengths[dimension]);
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
    size_t[N] gridShape()() scope const @property
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
        `(x)` and `[x]` operators.
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
    SplineBoundaryCondition!F lbc,
    SplineBoundaryCondition!F rbc,
    ) @trusted
{
    import mir.ndslice.topology: diff, ipack;

    assert (points.length >= 2);
    assert (points.length == values.length);
    assert (points.length == slopes.length);
    assert (temp.length + 1 >= points.length);

    auto n = points.length;

    auto pd = points.diff;
    auto vd = values.diff;

    auto xd = cast() pd.front;
    auto yd = cast() vd.front;
    auto dd = yd / xd;

    // static if (N == 2)
    // {
    //     if (slopes.length!1 != values.length!1)
    //         assert(0);
    //     if (values.empty!1)
    //         return;
    // }

    /// special case
    static assert(SplineBoundaryType.notAKnot == 0);
    with(SplineBoundaryType)
    if (_expect(n == 3 && (rbc.type | lbc.type) == 0, false))
    {
        import mir.interpolate.utility;
        // static if (N == 1)
        {
            auto parabola = parabolaKernel(points[0], points[1], points[2], values[0], values[1], values[2]);
            slopes[0] = parabola.withDerivative(points[0])[1];
            slopes[1] = parabola.withDerivative(points[1])[1];
            slopes[2] = parabola.withDerivative(points[2])[1];
        }
        // else
        // {
        //     foreach (i; 0 .. values.length!1)
        //     {
        //         auto parabolaDerivative = parabolaKernel!1(points[0], points[1], points[2], values[0][i], values[1][i], values[2][i]);
        //         slopes[0][i] = parabolaDerivative(points[0]);
        //         slopes[1][i] = parabolaDerivative(points[1]);
        //         slopes[2][i] = parabolaDerivative(points[2]);
        //     }
        // }
        return;
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
        return;

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
}

///
struct SplineKernel(X)
{
    X step = 0;
    X w0 = 0;
    X w1 = 0;
    X wq = 0;

    ///
    this()(X x0, X x1, X x)
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
