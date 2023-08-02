/++
$(H2 Constant Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.constant;

@fmamath:

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
import mir.math.common: fmamath;
import mir.ndslice.slice;
import mir.primitives;
import mir.rc.array;
import mir.utility: min, max;
import std.meta: AliasSeq, staticMap;
import std.traits;

///
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
@fmamath:

    /// Aligned buffer allocated with `mir.internal.memory`. $(RED For internal use.)
    Slice!(RCI!(const F), N) _data;
    /// Grid iterators. $(RED For internal use.)
    Repeat!(N, RCI!(immutable X)) _grid;

extern(D):

    bool opEquals()(auto ref scope const typeof(this) rhs) scope const @trusted pure nothrow @nogc
    {
        if (rhs._data != this._data)
            return false;
        static foreach (d; 0 .. N)
            if (gridScopeView!d != rhs.gridScopeView!d)
                return false;
        return true;
    }

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
                version(D_Exceptions) { import mir.exception : toMutable; throw exc_min.toMutable; }
                else assert(0, msg_min);
            }
            if (x.length != data._lengths[i])
            {
                version(D_Exceptions) { import mir.exception : toMutable; throw exc_eq.toMutable; }
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
    Slice!(RCI!(immutable X)) grid(size_t dimension = 0)() return scope const @property
        if (dimension < N)
    {
        return _grid[dimension].lightConst.sliced(_data._lengths[dimension]);
    }

    ///
    immutable(X)[] gridScopeView(size_t dimension = 0)() return scope const @property @trusted
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
    enum uint dimensionCount = N;

    ///
    template opCall(uint derivative = 0)
        // if (derivative <= derivativeOrder)
    {
        /++
        `(x)` operator.
        Complexity:
            `O(log(grid.length))`
        +/
        auto opCall(X...)(in X xs) scope const @trusted
            if (X.length == N)
        {
            size_t[N] indices;
            foreach(i; Iota!N)
            {
                static if (isInterval!(typeof(xs[i])))
                    indices[i] = xs[i][1];
                else
                    indices[i] = _data._lengths[i] > 1 ? this.findInterval!i(xs[i]) : 0;
            }
            static if (derivative == 0)
            {
                return _data[indices];
            }
            else
            {
                F[derivative + 1] ret = 0;
                ret[0] = _data[indices];
                return ret;
            }
        }
    }
}

/++
Single value interpolation
+/
SingleConstant!F singleConstant(F)(const F value)
{
    return typeof(return)(value);
}

/// ditto
struct SingleConstant(F, X = F)
{
    ///
    enum uint derivativeOrder = 0;

    ///
    enum uint dimensionCount = 1;

    ///
    F value;

    ///
    this(F value)
    {
        this.value = value;
    }


    ///
    immutable(X)[] gridScopeView(size_t dimension = 0)() return scope const @property @trusted
        if (dimension == 0)
    {
        return null;
    }

    ///
    template opCall(uint derivative = 0)
    {
        /++
        `(x)` operator.
        Complexity:
            `O(1)`
        +/
        auto opCall(X...)(in X xs) scope const @trusted
        {
            static if (derivative == 0)
            {
                return F(value);
            }
            else
            {
                F[derivative + 1] ret = 0;
                ret[0] = value;
                return ret;
            }
        }
    }
}

///
@safe pure nothrow
version (mir_test)
unittest
{
    auto sc = singleConstant(34.1);
    assert(sc(100) == 34.1);
    assert(sc.opCall!2(100) == [34.1, 0, 0]);
}

/++
Interpolator used for non-rectiliner trapezoid-like greeds.
Params:
    grid = rc-array of interpolation grid
    data = rc-array of interpolator-like structures
+/
auto metaSingleConstant(T)(T data)
{
    import core.lifetime: move;
    return MetaSingleConstant!T(data.move);
}

/// ditto
struct MetaSingleConstant(T, X = double)
    // if (T.derivativeOrder >= 1)
{
    import mir.interpolate.utility: DeepType;

    ///
    T data;

    ///
    this(T data)
    {
        import core.lifetime: move;
        this.data = data.move;
    }

    ///
    MetaSingleConstant lightConst()() const @property { return *cast(MetaSingleConstant*)&this; }

    ///
    immutable(X)[] gridScopeView(size_t dimension = 0)() return scope const @property @trusted
        if (dimension == 0)
    {
        return null;
    }

    ///
    enum uint derivativeOrder = 1;

    static if (__traits(compiles, {enum N = T.dimensionCount;}))
    ///
    enum uint dimensionCount = T.dimensionCount + 1;

    ///
    template opCall(uint derivative = 0)
    {
        /++
        `(x)` operator.
        Complexity:
            `O(log(grid.length))`
        +/
        auto opCall(X...)(const X xs) scope const @trusted
            if (xs.length >= 1)
        {
            static if (derivative == 0)
            {
                return data(xs[1.. $]);
            }
            else
            {
                auto iv = data.opCall!derivative(xs[1.. $]);
                typeof(iv)[derivative + 1] ret = 0;
                ret[0] = iv;
                return ret;
            }
        }
    }
}

/// Ignores the first dimension parameter
version(mir_test)
unittest
{
    import mir.interpolate.linear;

    auto x = [0.0, 1, 2, 3, 5];
    auto y = [4.0, 0, 9, 23, 40];

    auto g = [7.0, 10, 15];

    import mir.ndslice.allocation: rcslice;

    auto d = linear!double(x.rcslice!(immutable double), y.rcslice!(const double));

    auto ignoresFirstDim = d.metaSingleConstant;

    assert(ignoresFirstDim(9.0, 1.8) == d(1.8));
    assert(ignoresFirstDim.opCall!1(9.0, 1.8) == [d.opCall!1(1.8), [0.0, 0.0]]);
}
