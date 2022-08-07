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
module mir.interpolate.extrapolate;

/++
Constant extrapolator
+/
ConstantExtrapolator!T constantExtrapolator(T)(T interpolator)
{
    import core.lifetime: move;
    return typeof(return)(interpolator.move);
}


/// ditto
struct ConstantExtrapolator(T)
    if (__traits(hasMember, T, "gridScopeView"))
{
    ///
    T data;

    ///
    this(T data)
    {
        import core.lifetime: move;
        this.data = data.move;
    }

    ///
    ConstantExtrapolator lightConst()() const @property { return *cast(ConstantExtrapolator*)&this; }

    ///
    auto gridScopeView(size_t dimension = 0)() return scope const @property @trusted
    {
        return data.gridScopeView!dimension;
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
            import mir.internal.utility: Iota;
            import mir.math.common: fmin, fmax;
            import std.meta: staticMap;

            static if (derivative)
                bool[X.length] extrpolated;

            auto mod(size_t i)()
            {
                static if (__traits(compiles, gridScopeView!i))
                {
                    auto grid = gridScopeView!i;
                    static if (derivative)
                        extrpolated[i] = grid.length != 0 && (xs[i] < grid[0] || grid[$ - 1] < xs[i]);
                    return grid.length ? xs[i].fmax(grid[0]).fmin(grid[$ - 1]) : xs[i];
                }
                else
                {
                    return xs[i];
                }
            }

            alias xm = staticMap!(mod, Iota!(X.length));

            static if (derivative == 0)
                return data(xm);
            else
            {
                static assert (xs.length <= 2, "multidimensional constant exrapolation with derivatives isn't implemented");
                auto ret = data.opCall!derivative(xm);
                static if (xs.length == 1)
                {
                    if (extrpolated[0])
                    {
                        foreach (ref e; ret[1 .. $])
                        {
                            e = 0;
                        }
                    }
                }
                else
                static if (xs.length == 2)
                {
                    if (extrpolated[0])
                    {
                        foreach (ref e; ret[1 .. $])
                        {
                            e = 0;
                        }
                    }

                    if (extrpolated[1])
                    {
                        foreach (ref e; ret)
                        {
                            e[1 .. $] = 0;
                        }
                    }
                }
                return ret;
            }
        }
    }
}


///
version(mir_test)
unittest
{
    import mir.interpolate.linear;

    auto x = [0.0, 1, 2, 3, 5];
    auto y = [4.0, 0, 9, 23, 40];

    auto g = [7.0, 10, 15];

    import mir.ndslice.allocation: rcslice;

    auto linear = linear!double(
        x.rcslice!(immutable double),
        y.rcslice!(const double),
    ).constantExtrapolator;

    assert(linear(2) == 9);
    assert(linear(-1) == 4);
    assert(linear(100) == 40);
}
