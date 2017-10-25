/++
$(H2 Constant Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.constant;

///
version(mir_test)
@safe unittest
{
    import mir.ndslice;
    import std.math: approxEqual;

    auto x = [0, 1, 2, 3];
    auto y = [10, 20, 30, 40];

    auto interpolant = constant!int(x.sliced, y.sliced);

    assert(interpolant(-1) == 10);
    assert(interpolant(0) == 10);
    assert(interpolant(0.5) == 10);

    assert(interpolant(1) == 20);
    
    assert(interpolant(3) == 40);
    assert(interpolant(4) == 40);
}



import std.traits;
import std.meta: AliasSeq, staticMap;
import mir.array.primitives;
import mir.ndslice.slice;
import mir.internal.utility;
import mir.math.common: optmath;

public import mir.interpolate: atInterval;
import mir.interpolate;

/++
Constructs multivariate constant interpolant with nodes on rectilinear grid.

Params:
    grid = `x` values for interpolant
    values = `f(x)` values for interpolant

Constraints:
    `grid`, `values` must have the same length >= 3

Returns: $(LREF Constant)
+/
template constant(T, size_t N = 1, FirstGridIterator = T*, NextGridIterators = Repeat!(N - 1, FirstGridIterator))
    if (is(T == Unqual!T) && N <= 6)
{
    static if (N > 1) pragma(msg, "Warning: multivariate constant interplant was not tested.");

    private alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    private alias GridVectors = Constant!(T, N, GridIterators).GridVectors;

    /++
    Params:
        grid = `x` values for interpolant
        values = `f(x)` values for interpolant
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(LREF Spline)
    +/
    Constant!(T, N, GridIterators) constant(SliceKind ykind, yIterator)(
        GridVectors grid,
        scope Slice!(ykind, [1], yIterator) values,
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

/++
Multivariate constant interpolant with nodes on rectilinear grid.
+/
struct Constant(F, size_t N = 1, FirstGridIterator = F*, NextGridIterators = Repeat!(N - 1, FirstGridIterator))
    if (N && N <= 6 && NextGridIterators.length == N - 1)
{
    import mir.ndslice.internal: ConstIfPointer;

    package alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    package alias GridVectors = staticMap!(GridVector, staticMap!(ConstIfPointer, GridIterators));

    /// Aligned buffer allocated with `mir.internal.memory`. $(RED For internal use.)
    Slice!(Contiguous, [N], F*) _data;
    /// Grid iterators. $(RED For internal use.)
    staticMap!(ConstIfPointer, GridIterators) _grid;
    ///
    bool _ownsData;

    import mir.utility: min, max;
    package enum alignment = min(64u, F.sizeof).max(size_t.sizeof);

    ///
    this(this) @safe nothrow @nogc
    {
        import core.atomic: atomicOp;
        if (_ownsData)
            counter.atomicOp!"+="(1);
    }

    ///
    GridVectors[dimension] grid(size_t dimension = 0)() @property
        if (dimension < N)
    {
        return _grid[dimension].sliced(_data._lengths[dimension]);
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

    package ref shared(sizediff_t) counter() @trusted @property
    {
        assert(_ownsData);
        auto p = cast(shared sizediff_t*) _data.ptr;
        return *(p - 1);
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
            assert(x.length >= 2, "linear interpolant: minimal allowed length for the grid equals 2.");
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
    this()(GridVectors grid, Slice!(Contiguous, [N], const(F)*) values) @trusted nothrow @nogc
    {
        foreach(i, ref x; grid)
        {
            assert(x.length >= 2, "linear interpolant: minimal allowed length for the grid equals 2.");
            assert(values.length!i == x.length, "grid length should mutch to the values length");
        }

        this._data = values;
        this._grid = staticMap!(iter, grid);
        this._ownsData = false;
    }

    ///
    size_t[N] dataShape()() @property
    {
        return _data.shape;
    }

    /++
    Interval index for x.
    +/
    size_t interval(size_t dimension = 0, X)(in X x)
    {
        import std.range: assumeSorted;
        return _data._lengths[dimension] - 1 - _grid[dimension].sliced(_data._lengths[dimension])[1 .. $]
            .assumeSorted
            .upperBound(x)
            .length;
    }

    ///
    enum uint maxDerivative = 0;

    ///
    template opCall(uint derivative = 0)
        if (derivative <= maxDerivative)
    {
        @trusted:
        /++
        `(x)` and `[x]` operators.
        Complexity:
            `O(log(grid.length))`
        +/
        auto opCall(X...)(in X xs)
            if (X.length == N)
            // @FUTURE@
            // X.length == N || derivative == 0 && X.length && X.length <= N
        {
            import mir.ndslice.topology: iota;

            size_t[N] indexes = void;

            enum rp2d = derivative;

            foreach(i; Iota!N)
            {
                static if (isInterval!(typeof(xs[i])))
                    indexes[i] = xs[i][1];
                else
                    indexes[i] = interval!i(xs[i]);
            }
            return _data[indexes];
        }
    }
}
