/++
$(H2 Generic Piecewise Interpolant)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.generic;

@fmamath:

///
version(mir_test)
@safe pure @nogc unittest
{
    import mir.ndslice;
    import mir.math.common: approxEqual;

    struct PieceInterpolant
    {
        int value;

        this()(int value)
        {
            this.value = value;
        }

        int opCall(uint derivative : 0, X)(int x0, int x1, X x) const
        {
            return value;
        }

        enum uint derivativeOrder = 0;
    }

    alias S = PieceInterpolant;
    static immutable x = [0, 1, 2, 3]; // can be also an array of floating point numbers
    static immutable y = [S(10), S(20), S(30)];

    auto interpolant = generic(x.rcslice, y.rcslice!(const S));

    assert(interpolant(-1) == 10);
    assert(interpolant(0) == 10);
    assert(interpolant(0.5) == 10);

    assert(interpolant(1) == 20);
    assert(interpolant(1.5) == 20);

    assert(interpolant(2) == 30);
    assert(interpolant(3) == 30);
    assert(interpolant(3.4) == 30);
    assert(interpolant(3) == 30);
    assert(interpolant(4) == 30);
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
Constructs multivariate generic interpolant with nodes on rectilinear grid.

Params:
    grid = `x` values for interpolant
    values = `f(x)` values for interpolant

Constraints:
    `grid`, `values` must have the same length >= 1

Returns: $(LREF Generic)
+/
Generic!(X, F) generic(X, F)
    (Slice!(RCI!(immutable X)) grid, Slice!(RCI!(const F)) values)
{
    return typeof(return)(forward!grid, values.move);
}

/++
Multivariate generic interpolant with nodes on rectilinear grid.
+/
struct Generic(X, F)
{
@fmamath:

    /// Aligned buffer allocated with `mir.internal.memory`. $(RED For internal use.)
    Slice!(RCI!(const F)) _data;
    /// Grid iterators. $(RED For internal use.)
    RCI!(immutable X) _grid;

    bool opEquals()(auto ref scope const typeof(this) rhs) scope const @trusted pure nothrow @nogc
    {
        if (rhs._data != this._data)
            return false;
        static foreach (d; 0 .. 1)
            if (gridScopeView!d != rhs.gridScopeView!d)
                return false;
        return true;
    }

extern(D):

    /++
    +/
    this(Slice!(RCI!(immutable X)) grid, Slice!(RCI!(const F)) data) @safe @nogc
    {
        import core.lifetime: move;
        enum  msg_min =  "generic interpolant: minimal allowed length for the grid equals 2.";
        enum  msg_eq =  "generic interpolant: X length and Y values length + 1 should be equal.";
        version(D_Exceptions)
        {
            static immutable exc_min = new Exception(msg_min);
            static immutable exc_eq = new Exception(msg_eq);
        }
        if (grid.length < 2)
        {
            version(D_Exceptions) { import mir.exception : toMutable; throw exc_min.toMutable; }
            else assert(0, msg_min);
        }
        if (grid.length != data._lengths[0] + 1)
        {
            version(D_Exceptions) { import mir.exception : toMutable; throw exc_eq.toMutable; }
            else assert(0, msg_eq);
        }
        _grid = move(grid._iterator);
        _data = move(data);
    }

@trusted:

    ///
    Generic lightConst()() const @property { return *cast(Generic*)&this; }

    ///
    Slice!(RCI!(immutable X)) grid(size_t dimension = 0)() return scope const @property
        if (dimension == 0)
    {
        return _grid.lightConst.sliced(_data._lengths[0]);
    }

    ///
    immutable(X)[] gridScopeView(size_t dimension = 0)() return scope const @property @trusted
        if (dimension == 0)
    {
        return _grid._iterator[0 .. _data._lengths[0]];
    }

    /++
    Returns: intervals count.
    +/
    size_t intervalCount(size_t dimension = 0)() scope const @property
        if (dimension == 0)
    {
        assert(_data._lengths[0] > 1);
        return _data._lengths[0] - 0;
    }

    ///
    size_t[1] gridShape()() scope const @property
    {
        return _data.shape;
    }

    ///
    enum uint derivativeOrder = F.derivativeOrder;

    ///
    template opCall(uint derivative = 0)
        if (derivative == 0)
    {
        /++
        `(x)` operator.
        Complexity:
            `O(log(grid.length))`
        +/
        auto opCall(X)(in X x) const
        {
            return opCall!(X)(Tuple!(size_t, X)(this.findInterval(x), x));
        }

        ///
        auto opCall(X)(Tuple!(size_t, X) tuple) const
        {
            X x = tuple[1];
            size_t idx = tuple[0];
            return _data[idx].opCall!derivative(_grid[idx], _grid[idx + 1], x);
        }
    }
}
