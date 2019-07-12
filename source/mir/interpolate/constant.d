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

@optmath:

///
version(mir_test)
@safe pure unittest
{
    import mir.ndslice;
    import mir.math.common: approxEqual;

    immutable x = [0, 1, 2, 3];
    immutable y = [10, 20, 30, 40];

    auto interpolant = constant!int(x.sliced, y.sliced);

    assert(interpolant(-1) == 10);
    assert(interpolant(0) == 10);
    assert(interpolant(0.5) == 10);

    assert(interpolant(1) == 20);
    
    assert(interpolant(3) == 40);
    assert(interpolant(4) == 40);
}



import std.traits;
import mir.primitives;
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
    `grid`, `values` must have the same length >= 1

Returns: $(LREF Constant)
+/
template constant(T, size_t N = 1, FirstGridIterator = immutable(T)*, NextGridIterators = Repeat!(N - 1, FirstGridIterator))
    if (is(T == Unqual!T) && N <= 6)
{
    static if (N > 1) pragma(msg, "Warning: multivariate constant interpolant was not tested.");

    import std.meta: AliasSeq;

@optmath:

    private alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    private alias GridVectors = Constant!(T, N, GridIterators).GridVectors;

    /++
    Params:
        grid = immutable `x` values for interpolant
        values = `f(x)` values for interpolant
    Constraints:
        `grid` and `values` must have the same length >= 3
    Returns: $(LREF Spline)
    +/
    Constant!(T, N, GridIterators) constant(yIterator, SliceKind ykind)(
        GridVectors grid,
        Slice!(yIterator, 1, ykind) values
        ) pure @trusted
    {
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        auto ret = typeof(return)(grid);
        ret._data[] = values;
        return ret.move;
    }
}

/++
Multivariate constant interpolant with nodes on rectilinear grid.
+/
struct Constant(F, size_t N = 1, FirstGridIterator = immutable(F)*, NextGridIterators = Repeat!(N - 1, FirstGridIterator))
    if (N && N <= 6 && NextGridIterators.length == N - 1)
{
    import mir.rc.array;
    import std.meta: AliasSeq, staticMap;

    package alias GridIterators = AliasSeq!(FirstGridIterator, NextGridIterators);
    package alias GridVectors = staticMap!(GridVector, GridIterators);

@optmath:

    /// Aligned buffer allocated with `mir.internal.memory`. $(RED For internal use.)
    mir_slice!(mir_rci!F, N) _data;
    /// Grid iterators. $(RED For internal use.)
    GridIterators _grid;

    import mir.utility: min, max;
    package enum alignment = min(64u, F.sizeof).max(size_t.sizeof);

    /++
    +/
    this(GridVectors grid) @safe @nogc
    {
        size_t length = 1;
        size_t[N] shape;
        enum  msg =  "constant interpolant: minimal allowed length for the grid equals 1.";
        version(D_Exceptions)
            static immutable exc = new Exception(msg);
        foreach(i, ref x; grid)
        {
            if (x.length < 1)
            {
                version(D_Exceptions)
                    throw exc;
                else
                    assert(0, msg);
            }
            length *= shape[i] = x.length;
        }

        auto rca = mir_rcarray!F(length);
        this._data = rca.asSlice.sliced(shape);
        this._grid = staticMap!(iter, grid);
    }

@trusted:

    ///
    Constant lightConst()() const @property { return *cast(Constant*)&this; }
    ///
    Constant lightImmutable()() immutable @property { return *cast(Constant*)&this; }

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
        assert(_data._lengths[dimension] > 0);
        return _data._lengths[dimension] - 0;
    }

    ///
    size_t[N] gridShape()() scope const @property
    {
        return _data.shape;
    }

    ///
    enum uint derivativeOrder = 0;

    ///
    template opCall(uint derivative = 0)
        if (derivative <= derivativeOrder)
    {
        @trusted:
        /++
        `(x)` and `[x]` operators.
        Complexity:
            `O(log(grid.length))`
        +/
        auto opCall(X...)(in X xs) scope const
            if (X.length == N)
            // @FUTURE@
            // X.length == N || derivative == 0 && X.length && X.length <= N
        {
            size_t[N] indexes = void;

            foreach(i; Iota!N)
            {
                static if (isInterval!(typeof(xs[i])))
                    indexes[i] = xs[i][1];
                else
                    indexes[i] = _data._lengths[i] > 1 ? this.findInterval!i(xs[i]) : 0;
            }
            return _data[indexes];
        }
    }
}
