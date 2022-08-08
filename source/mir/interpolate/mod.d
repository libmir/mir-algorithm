/++
$(H2 Interpolation Modifier)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2022 Ilia, Symmetry Investments
Authors: Ilia Ki

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.mod;

import mir.math.common;

/++
Applies function to the interpolated value.

Params:
    fun = two arguments `(x, derivativeOrder)` function
+/
template interpolationMap(alias fun)
{
    ///
    auto interpolationMap(T)(T interpolator)
    {
        import core.lifetime: move;
        alias S = InterpolationMap!fun;
        return S!T(interpolator.move);
    }
}

/// ditto
template InterpolationMap(alias fun)
{
    ///
    struct InterpolationMap(T)
    {
        static if (__traits(hasMember, T, "derivativeOrder"))
            enum derivativeOrder = T.derivativeOrder;

        static if (__traits(hasMember, T, "dimensionCount"))
            enum uint dimensionCount = T.dimensionCount;

        ///
        T interpolator;

        ///
        this(T interpolator)
        {
            import core.lifetime: move;
            this.interpolator = interpolator.move;
        }

        ///
        template opCall(uint derivative = 0)
            // if (derivative <= derivativeOrder)
        {
            /++
            `(x)` operator.
            Complexity:
                `O(log(grid.length))`
            +/
            auto opCall(X...)(const X xs) scope const @trusted
                // if (X.length == dimensionCount)
            {
                auto g = interpolator.opCall!derivative(xs);

                static if (derivative == 0)
                {
                    typeof(g)[1] ret;
                    fun(g, ret);
                    return ret[0];
                }
                else
                {
                    static if (X.length == 1)
                        auto g0 = g[0];
                    else
                    static if (X.length == 2)
                        auto g0 = g[0][0];
                    else
                    static if (X.length == 3)
                        auto g0 = g[0][0][0];
                    else
                    static assert(0, "Not implemented");

                    typeof(g0)[derivative + 1] f;

                    fun(g0, f);

                    static if (X.length == 1)
                    {
                        typeof(g) r;
                        r[0] = f[0];
                        r[1] = f[1] * g[1];

                        static if (derivative >= 2)
                        {
                            r[2] = f[2] * (g[1] * g[1]) + f[1] * g[2];
                        }
                        static if (derivative >= 3)
                        {
                            r[3] = f[3] * (g[1] * g[1] * g[1]) + f[1] * g[3] + 3 * (f[2] * g[1] * g[2]);
                        }
                        static if (derivative >= 4)
                        {
                            static assert(0, "Not implemented");
                        }

                        return r;
                    } else static assert(0, "Not implemented");
                }
            }
        }
    }
}

///
version (mir_test)
unittest
{
    import mir.interpolate.spline;
    import mir.math.common: log;
    import mir.ndslice.allocation: rcslice;
    import mir.test;

    alias g = (double x, uint d = 0) =>
        d == 0 ? 3 * x ^^ 3 + 5 * x ^^ 2 + 0.23 * x + 2 :
        d == 1 ? 9 * x ^^ 2 + 10 * x + 0.23 :
        double.nan;
    
    alias f = (double x, ref scope y)
    {
        y[0] = log(x);
        static if (y.length >= 2)
            y[1] = 1 / x;
        static if (y.length >= 3)
            y[2] = -y[1] * y[1];
        static if (y.length >= 4)
            y[3] = -2 * y[1] * y[2];
        static if (y.length >= 5)
            static assert(0, "Not implemented");
    };

    auto s = spline!double(
        [0.1, 0.4, 0.5, 1.0].rcslice!(immutable double),
        [g(0.1), g(0.4), g(0.5), g(1.0)].rcslice!(const double)
    );

    auto m = s.interpolationMap!f;

    m(0.7).shouldApprox == log(g(0.7));
    auto d = m.opCall!3(0.7);
    d[0].shouldApprox == log(g(0.7));
    d[1].shouldApprox == 1 / g(0.7) * g(0.7, 1);
    d[2].shouldApprox == -0.252301;
    d[3].shouldApprox == -4.03705;
}

private alias implSqrt = (x, ref scope y)
{
    import mir.math.common: sqrt;
    y[0] = sqrt(x);
    static if (y.length >= 2)
        y[1] = 0.5f / y[0];
    static if (y.length >= 3)
        y[2] = -0.5f * y[1] / x;
    static if (y.length >= 4)
        y[3] = -1.5f * y[2] / x;
    static if (y.length >= 5)
        static assert(0, "Not implemented");
};

/++
Applies square root function to the interpolated value.
+/
alias interpolationSqrt = interpolationMap!implSqrt;
/// ditto
alias InterpolationSqrt = InterpolationMap!implSqrt;

///
version (mir_test)
unittest
{
    import mir.interpolate.spline;
    import mir.math.common: sqrt;
    import mir.ndslice.allocation: rcslice;
    import mir.test;

    alias g = (double x, uint d = 0) =>
        d == 0 ? 3 * x ^^ 3 + 5 * x ^^ 2 + 0.23 * x + 2 :
        d == 1 ? 9 * x ^^ 2 + 10 * x + 0.23 :
        double.nan;
    
    auto s = spline!double(
        [0.1, 0.4, 0.5, 1.0].rcslice!(immutable double),
        [g(0.1), g(0.4), g(0.5), g(1.0)].rcslice!(const double)
    );

    auto m = s.interpolationSqrt;

    m(0.7).shouldApprox == sqrt(g(0.7));
    auto d = m.opCall!3(0.7);
    d[0].shouldApprox == sqrt(g(0.7));
    d[1].shouldApprox == 0.5 / sqrt(g(0.7)) * g(0.7, 1);
    d[2].shouldApprox == 2.2292836438189414;
    d[3].shouldApprox == -3.11161;
}
