module mir.interpolate.utility;

import mir.ndslice.slice;
import std.traits;
import mir.math.common: optmath;

/++
ParabolaKernel structure.
+/
struct ParabolaKernel(T)
{
    ///
    T a = 0;
    ///
    T b = 0;
    ///
    T c = 0;

    /// Builds parabola given three points
    this(T)(T x0, T x1, T x2, T y0, T y1, T y2)
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
ParabolaKernel!(Unqual!(typeof(X.init - Y.init))) parabolaKernel(X, Y)(in X x0, in X x1, in X x2, in Y y0, in Y y1, in Y y2)
{
    return typeof(return)(x0, x1, x2, y0, y1, y2);
}

///
unittest
{
    import std.math: approxEqual;

    alias f = (double x) => 3 * (x ^^ 2) + 7 * x + 5;
    auto p = parabolaKernel(4, 9, 20, f(4), f(9), f(20));

    assert(p.a.approxEqual(3));
    assert(p.b.approxEqual(7));
    assert(p.c.approxEqual(5));
    assert(p(10).approxEqual(f(10)));
}
