/++
$(H2 Linear Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.linear;

import std.traits;
import std.meta: AliasSeq, staticMap;
import mir.array.primitives;
import mir.ndslice.slice;
import mir.math.common: optmath;
import mir.internal.utility;

public import mir.interpolate: atInterval;
import mir.interpolate;

@optmath:

/++
Constructs multivariate linear interpolant with nodes on rectilinear grid.

Params:
    T = element floating point type
    N = arity (dimension) number
    grid = N `x` values for interpolation
    values = `f(x)` values for interpolation

Constraints:
    `grid`, `values` must have the same length >= 2

Returns: $(LREF Linear)
+/
template linear(T, size_t N = 1, FirstGridIterator = immutable(T)*, NextGridIterators = Repeat!(N - 1, FirstGridIterator))
    // if (isFloatingPoint!T && is(T == Unqual!T) && N <= 6)
{
    private alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    private alias GridVectors = Linear!(T, N, GridIterators).GridVectors;

@optmath:

    /++
    Params:
        grid = immutable `x` values for interpolant
        values = `f(x)` values for interpolant
        forceCopyValues = always copy `values` if set
    Constraints:
        `grid` and `values` must have the same length >= 2
    Returns: $(LREF Spline)
    +/
    Linear!(T, N, GridIterators) linear(yIterator, Kind ykind)(
        GridVectors grid,
        scope Slice!(yIterator, N, ykind) values,
        bool forceCopyValues = false
        )
    {
        static if (__traits(compiles, typeof(return)(grid, values)))
        {
            if (!forceCopyValues)
            {
                return typeof(return)(grid, values);
            }
        }
        import std.algorithm.mutation: move;
        auto ret = typeof(return)(grid);
        ret._data[] = values;
        return ret.move;
    }
}


/// R -> R: Linear interpolation
version(mir_test)
@safe pure unittest
{
    import mir.ndslice;
    import std.math: approxEqual;

    immutable x = [0, 1, 2, 3, 5.00274, 7.00274, 10.0055, 20.0137, 30.0192];
    immutable y = [0.0011, 0.0011, 0.0030, 0.0064, 0.0144, 0.0207, 0.0261, 0.0329, 0.0356,];
    auto xs = [1, 2, 3, 4.00274, 5.00274, 6.00274, 7.00274, 8.00548, 9.00548, 10.0055, 11.0055, 12.0082, 13.0082, 14.0082, 15.0082, 16.011, 17.011, 18.011, 19.011, 20.0137, 21.0137, 22.0137, 23.0137, 24.0164, 25.0164, 26.0164, 27.0164, 28.0192, 29.0192, 30.0192];

    auto interpolation = linear!double(x.sliced, y.sliced);

    auto data = [0.0011, 0.0030, 0.0064, 0.0104, 0.0144, 0.0176, 0.0207, 0.0225, 0.0243, 0.0261, 0.0268, 0.0274, 0.0281, 0.0288, 0.0295, 0.0302, 0.0309, 0.0316, 0.0322, 0.0329, 0.0332, 0.0335, 0.0337, 0.0340, 0.0342, 0.0345, 0.0348, 0.0350, 0.0353, 0.0356];

    assert(approxEqual(xs.sliced.map!interpolation, data, 1e-4, 1e-4));
}

/// R^2 -> R: Bilinear interpolation
version(mir_test)
@safe pure unittest
{
    import std.math: approxEqual;
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

    auto interpolant = linear!(double, 2)(x0, x1, grid.map!f);

    ///// compute test data ////
    auto test_grid = cartesian(x0 + 1.23, x1 + 3.23);
    auto real_data = test_grid.map!f;
    auto interp_data = test_grid.vmap(interpolant);

    ///// verify result ////
    assert(all!appreq(interp_data, real_data));

    //// check derivatives ////
    auto z0 = 1.23;
    auto z1 = 3.21;
    auto d = interpolant.withDerivative(z0, z1);
    assert(appreq(interpolant(z0, z1), f(z0, z1)));
    assert(appreq(d[0][0], f(z0, z1)));
    assert(appreq(d[1][0], y_x0 + y_x0x1 * z1));
    assert(appreq(d[0][1], y_x1 + y_x0x1 * z0));
    assert(appreq(d[1][1], y_x0x1));
}

/// R^3 -> R: Trilinear interpolation
version(mir_test)
@safe pure unittest
{
    import std.math: approxEqual;
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

    auto interpolant = linear!(double, 3)(x0, x1, x2, grid.map!f);

    ///// compute test data ////
    auto test_grid = cartesian(x0 + 1.23, x1 + 3.23, x2 - 3);
    auto real_data = test_grid.map!f;
    auto interp_data = test_grid.vmap(interpolant);

    ///// verify result ////
    assert(all!appreq(interp_data, real_data));

    //// check derivatives ////
    auto z0 = 1.23;
    auto z1 = 3.21;
    auto z2 = 4;
    auto d = interpolant.withDerivative(z0, z1, z2);
    assert(appreq(interpolant(z0, z1, z2), f(z0, z1, z2)));
    assert(appreq(d[0][0][0], f(z0, z1, z2)));
    assert(appreq(d[1][0][0], y_x0 + y_x0x1 * z1 + y_x0x1x2 * z1 * z2));
    assert(appreq(d[0][1][0], y_x1 + y_x0x1 * z0 + y_x0x1x2 * z0 * z2));
    assert(appreq(d[1][1][0], y_x0x1 + y_x0x1x2 * z2));
    assert(appreq(d[1][1][1], y_x0x1x2));
}

/++
Multivariate linear interpolant with nodes on rectilinear grid.
+/
struct Linear(F, size_t N = 1, FirstGridIterator = immutable(F)*, NextGridIterators...)
    if (N && N <= 6 && NextGridIterators.length == N - 1)
{
    package alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    package alias GridVectors = staticMap!(GridVector, GridIterators);

    /// $(RED For internal use.)
    Slice!(F*, N) _data;
    /// Grid iterators. $(RED For internal use.)
    GridIterators _grid;
    ///
    bool _ownsData;

    import mir.utility: min, max;
    package enum alignment = min(64u, F.sizeof).max(size_t.sizeof);

    package ref shared(sizediff_t) counter() @trusted @property
    {
        assert(_ownsData);
        auto p = cast(shared sizediff_t*) _data.ptr;
        return *(p - 1);
    }

    ///
    this(this) @safe nothrow @nogc
    {
        import core.atomic: atomicOp;
        if (_ownsData)
            counter.atomicOp!"+="(1);
    }

    /++
    Frees _data if $(LREF Spline._freeData) is true.
    +/
    ~this() @trusted nothrow @nogc
    {
        import mir.internal.memory;
        import core.atomic: atomicOp;

        if (_ownsData)
            if (counter.atomicOp!"-="(1) <= 0)
                alignedFree(cast(void*)(_data.ptr) - alignment);
    }

    /++
    +/
    this()(GridVectors grid) @trusted nothrow @nogc
    {
        import mir.internal.memory;
        import mir.ndslice.topology: iota;

        size_t[N] shape;
        foreach(i, ref x; grid)
        {
            assert(x.length >= 2, "linear interpolation: minimal allowed length for the grid equals 2.");
            shape[i] = x.length;
        }

        auto data_ptr = cast(F*) (alignedAllocate(F.sizeof * shape.iota.elementsCount + alignment, alignment) + alignment);
        if(data_ptr is null)
            assert(0, "No memory");

        this._data = data_ptr.sliced(shape);
        this._grid = staticMap!(iter, grid);
        this._ownsData = true;
        this.counter = 1;
    }

    /++
    +/
    this()(GridVectors grid, Slice!(immutable(F)*, N) values) @trusted nothrow @nogc
    {
        import mir.internal.memory;
        import mir.ndslice.topology: iota;

        foreach(i, ref x; grid)
        {
            assert(x.length >= 2, "linear interpolation: minimal allowed length for the grid equals 2.");
            assert(values.length!i == x.length, "grid length should mutch to the values length");
        }

        this._data = values;
        this._grid = staticMap!(iter, grid);
        this._ownsData = false;
    }

@trusted:

    ///
    GridVectors[dimension] grid(size_t dimension = 0)() const @property
        if (dimension < N)
    {
        return _grid[dimension].sliced(_data._lengths[dimension]);
    }

    /++
    Returns: intervals count.
    +/
    size_t intervalCount(size_t dimension = 0)() const @property
    {
        assert(_data._lengths[dimension] > 1);
        return _data._lengths[dimension] - 1;
    }

    ///
    size_t[N] gridShape()() const @property
    {
        return _data.shape;
    }

    ///
    enum uint derivativeOrder = 1;

    ///
    template opCall(uint derivative = 0)
        if (derivative <= derivativeOrder)
    {
        /++
        `(x)` and `[x]` operators.
        Complexity:
            `O(log(grid.length))`
        +/
        auto opCall(X...)(in X xs) const @trusted
            if (X.length == N)
            // @FUTURE@
            // X.length == N || derivative == 0 && X.length && X.length <= N
        {
            import mir.functional: AliasCall;
            import mir.ndslice.topology: iota;
            alias Kernel = AliasCall!(LinearKernel!F, "opCall", derivative);

            size_t[N] indexes = void;
            Kernel[N] kernels = void;

            enum rp2d = derivative;

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
                kernels[i] = LinearKernel!F(_grid[i][indexes[i]], _grid[i][indexes[i] + 1], x);
            }

            align(64) F[2 ^^ N][derivative + 1] local = void;
            immutable strides = _data._lengths.iota.strides;

            void load(sizediff_t i)(F* from, F* to)
            {
                version(LDC) pragma(inline, true);
                static if (i == -1)
                {
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

            load!(N - 1)(cast(F*) _data.ptr, cast(F*)local[0].ptr);

            foreach(i; Iota!N)
            {
                enum P = 2 ^^ (N - 1 - i);
                enum L = 2 ^^ (N - i * (1 - rp2d)) / 2;
                vectorize(kernels[i], local[0][0 * L .. 1 * L], local[0][1 * L .. 2 * L], *cast(F[L][2 ^^ rp2d]*)local[rp2d].ptr);
                static if (rp2d == 1)
                    shuffle3!1(local[1][0 .. L], local[1][L .. 2 * L], local[0][0 .. L], local[0][L .. 2 * L]);
                static if (i + 1 == N)
                    return *cast(SplineReturnType!(F, N, 2 ^^ rp2d)*) local[0].ptr;
            }
        }
    }

    ///
    alias withDerivative = opCall!1;
}

///
struct LinearKernel(X)
{
    X step = 0;
    X w0 = 0;
    X w1 = 0;

    ///
    auto lightConst()() const @property
    {
        return LinearKernel!X(step, w0, w1);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return LinearKernel!X(step, w0, w1);
    }

    ///
    this()(X x0, X x1, X x)
    {
        step = x1 - x0;
        auto c0 = x - x0;
        auto c1 = x1 - x;
        w0 = c0 / step;
        w1 = c1 / step;
    }

    ///
    template opCall(uint derivative = 0)
        if (derivative <= 1)
    {
        ///
        auto opCall(Y)(in Y y0, in Y y1)
        {
            auto r0 = y0 * w1;
            auto r1 = y1 * w0;
            auto y = r0 + r1;
            static if (derivative)
            {
                auto diff = y1 - y0;
                Y[derivative + 1] ret = 0;
                ret[0] = y;
                ret[1] = diff / step;
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
}
