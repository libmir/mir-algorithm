module mir.interpolate.utility;

import mir.ndslice.slice;
import std.traits;
import mir.math.common: optmath;

package template DeepType(T)
{
    static if (is(T : E[N], E, size_t N))
        alias DeepType = DeepType!E;
    else
        alias DeepType = T;
}

/++
Quadratic function structure
+/
struct ParabolaKernel(T)
{
    ///
    T a = 0;
    ///
    T b = 0;
    ///
    T c = 0;

@optmath:

    ///
    this(T a, T b, T c)
    {
        this.a = a;
        this.b = b;
        this.c = c;
    }

    /// Builds parabola given three points
    this(T x0, T x1, T x2, T y0, T y1, T y2)
    {
        auto b1 = x1 - x0;
        auto b2 = x2 - x1;
        auto d1 = y1 - y0;
        auto d2 = y2 - y1;
        auto a1 = b1 * (x1 + x0);
        auto a2 = b2 * (x2 + x1);
        auto bm = - (b2 / b1);
        auto a3 = bm * a1 + a2;
        auto d3 = bm * d1 + d2;
        a = d3 / a3;
        b = (d1 - a1 * a) / b1;
        c = y1 - x1 * (a * x1 + b);
    }

    /++
    Params:
        x0 = `x0`
        x1 = `x1`
        y0 = `f(x0)`
        y1 = `f(x1)`
        d1 = `f'(x1)`
    +/
    static ParabolaKernel fromFirstDerivative(T x0, T x1, T y0, T y1, T d1)
    {
        auto dy = y1 - y0;
        auto dx = x1 - x0;
        auto dd = dy / dx;
        auto a = (d1 - dd) / dx;
        auto b = dd - a * (x0 + x1);
        auto c = y1 - (a * x1 + b) * x1;
        return ParabolaKernel(a, b, c);
    }

    ///
    auto opCall(uint derivative = 0)(T x) const
        if (derivative <= 2)
    {
        auto y = (a * x + b) * x + c;
        static if (derivative == 0)
           return y;
        else
        {
            auto y1 = 2 * a * x + b;
            static if (derivative == 1)
                return cast(T[2])[y, y1];
            else
                return cast(T[3])[y, y1, 2 * a];
        }
    }

    ///
    alias withDerivative = opCall!1;
    ///
    alias withTwoDerivatives = opCall!2;
}

/// ditto
ParabolaKernel!(Unqual!(typeof(X.init - Y.init))) parabolaKernel(X, Y)(in X x0, in X x1, in X x2, const Y y0, const Y y1, const Y y2)
{
    return typeof(return)(x0, x1, x2, y0, y1, y2);
}

/++
Returns: `[f'(x0), f'(x1), f'(x2)]`
+/
Unqual!(typeof(X.init - Y.init))[3] parabolaDerivatives(X, Y)(in X x0, in X x1, in X x2, const Y y0, const Y y1, const Y y2)
{
    auto d0 = (y2 - y1) / (x2 - x1);
    auto d1 = (y0 - y2) / (x0 - x2);
    auto d2 = (y1 - y0) / (x1 - x0);
    return [d1 + d2 - d0, d0 + d2 - d1, d0 + d1 - d2];
}

///
unittest
{
    import mir.math.common: approxEqual;

    alias f = (double x) => 3 * x ^^ 2 + 7 * x + 5;
    auto x0 = 4;
    auto x1 = 9;
    auto x2 = 20;
    auto p = parabolaKernel(x0, x1, x2, f(x0), f(x1), f(x2));

    assert(p.a.approxEqual(3));
    assert(p.b.approxEqual(7));
    assert(p.c.approxEqual(5));
    assert(p(10).approxEqual(f(10)));
}


///
unittest
{
    import mir.math.common: approxEqual;

    alias f = (double x) => 3 * x ^^ 2 + 7 * x + 5;
    alias d = (double x) => 2 * 3 * x + 7;
    auto x0 = 4;
    auto x1 = 9;
    auto p = ParabolaKernel!double.fromFirstDerivative(x0, x1, f(x0), f(x1), d(x1));

    assert(p.a.approxEqual(3));
    assert(p.b.approxEqual(7));
    assert(p.c.approxEqual(5));
}

/++
Cubic function structure
+/
struct CubicKernel(T)
{
    ///
    T a = 0;
    ///
    T b = 0;
    ///
    T c = 0;
    ///
    T d = 0;

@optmath:

    ///
    this(T a, T b, T c, T d)
    {
        this.a = a;
        this.b = b;
        this.c = c;
        this.d = d;
    }

    /++
    Params:
        x0 = `x0`
        x1 = `x1`
        y0 = `f(x0)`
        y1 = `f(x1)`
        dd0 = `f''(x0)`
        d1 = `f'(x1)`
    +/
    static CubicKernel fromSecondAndFirstDerivative(T x0, T x1, T y0, T y1, T dd0, T d1)
    {
        auto hdd0 = 0.5f * dd0;
        auto dy = y1 - y0;
        auto dx = x1 - x0;
        auto dd = dy / dx;
        auto a =  0.5f * ((d1 - dd) / dx - hdd0) / dx;
        auto b = hdd0 - 3 * a * x0;
        auto c = d1 - (3 * a * x1 + 2 * b) * x1;
        auto d = y1 - ((a * x1 + b) * x1 + c) * x1;
        return CubicKernel!T(a, b, c, d);
    }

    ///
    auto opCall(uint derivative = 0)(T x) const
        if (derivative <= 3)
    {
        auto y = ((a * x + b) * x + c) * x + d;
        static if (derivative == 0)
           return y;
        else
        {
            T[derivative + 1] ret;
            ret[0] = y;
            ret[1] = (3 * a * x + 2 * b) * x + c;
            static if (derivative > 1)
            {
                ret[2] = 6 * a * x + 2 * b;
                static if (derivative > 2)
                    ret[3] = 6 * a;
            }
            return ret;
        }
    }

    ///
    alias withDerivative = opCall!1;
    ///
    alias withTwoDerivatives = opCall!2;
}

///
unittest
{
    import mir.math.common: approxEqual;

    alias f = (double x) => 3 * x ^^ 3 + 7 * x ^^ 2 + 5 * x + 10;
    alias d = (double x) => 3 * 3 * x ^^ 2 + 2 * 7 * x + 5;
    alias s = (double x) => 6 * 3 * x + 2 * 7;
    auto x0 = 4;
    auto x1 = 9;
    auto p = CubicKernel!double.fromSecondAndFirstDerivative(x0, x1, f(x0), f(x1), s(x0), d(x1));

    assert(p.a.approxEqual(3));
    assert(p.b.approxEqual(7));
    assert(p.c.approxEqual(5));
    assert(p.d.approxEqual(10));
    assert(p(13).approxEqual(f(13)));
    assert(p.opCall!1(13)[1].approxEqual(d(13)));
    assert(p.opCall!2(13)[2].approxEqual(s(13)));
    assert(p.opCall!3(13)[3].approxEqual(18));
}


package auto pchipTail(T)(in T step0, in T step1, in T diff0, in T diff1)
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
