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
@safe pure @nogc unittest
{
    import mir.ndslice;
    import mir.math.common: approxEqual;

    static immutable x = [0, 1, 2, 3];
    static immutable y = [10, 20, 30, 40];

    auto interpolant = constant!int(x.rcslice, y.rcslice!(const int));

    assert(interpolant(-1) == 10);
    assert(interpolant(0) == 10);
    assert(interpolant(0.5) == 10);

    assert(interpolant(1) == 20);
    
    assert(interpolant(3) == 40);
    assert(interpolant(4) == 40);
}


import core.lifetime: move; 
import mir.internal.utility;
import mir.functional;
import mir.interpolate;
import mir.math.common: optmath;
import mir.ndslice.slice;
import mir.primitives;
import mir.rc.array;
import mir.utility: min, max;
import std.meta: AliasSeq, staticMap;
import std.traits;
public import mir.interpolate: atInterval;

/++
Constructs multivariate constant interpolant with nodes on rectilinear grid.

Params:
    grid = `x` values for interpolant
    values = `f(x)` values for interpolant

Constraints:
    `grid`, `values` must have the same length >= 1

Returns: $(LREF Constant)
+/
Constant!(F, N, X) constant(F, size_t N = 1, X = F)
    (Repeat!(N, Slice!(RCI!(immutable X))) grid, Slice!(RCI!(const F), N) values)
{
    return typeof(return)(forward!grid, values.move);
}

/++
Multivariate constant interpolant with nodes on rectilinear grid.
+/
struct Constant(F, size_t N = 1, X = F)
    if (N && N <= 6)
{
@optmath:

    /// Aligned buffer allocated with `mir.internal.memory`. $(RED For internal use.)
    Slice!(RCI!(const F), N) _data;
    /// Grid iterators. $(RED For internal use.)
    RCI!(immutable X)[N] _grid;

extern(D):

    /++
    +/
    this(Repeat!(N, Slice!(RCI!(immutable X))) grid, Slice!(RCI!(const F), N) data) @safe @nogc
    {
        enum  msg_min =  "constant interpolant: minimal allowed length for the grid equals 1.";
        enum  msg_eq =  "constant interpolant: X and Y values length should be equal.";
        version(D_Exceptions)
        {
            static immutable exc_min = new Exception(msg_min);
            static immutable exc_eq = new Exception(msg_eq);
        }
        foreach(i, ref x; grid)
        {
            if (x.length < 1)
            {
                version(D_Exceptions) throw exc_min;
                else assert(0, msg_min);
            }
            if (x.length != data._lengths[i])
            {
                version(D_Exceptions) throw exc_eq;
                else assert(0, msg_eq);
            }
            _grid[i] = x._iterator;
        }
        _data = data;
    }

@trusted:

    ///
    Constant lightConst()() const @property { return *cast(Constant*)&this; }

    ///
    Slice!(RCI!(immutable X)) grid(size_t dimension = 0)() scope return const @property
        if (dimension < N)
    {
        return _grid[dimension].lightConst.sliced(_data._lengths[dimension]);
    }

    ///
    immutable(X)[] gridScopeView(size_t dimension = 0)() scope return const @property @trusted
        if (dimension < N)
    {
        return _grid[dimension]._iterator[0 .. _data._lengths[dimension]];
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
        /++
        `(x)` operator.
        Complexity:
            `O(log(grid.length))`
        +/
        auto opCall(X...)(in X xs) scope const @trusted
            if (X.length == N)
        {
            size_t[N] indexes;
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
