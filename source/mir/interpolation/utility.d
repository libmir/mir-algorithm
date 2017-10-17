module mir.interpolation.utility;

import mir.ndslice.slice;

/++
ParabolaKernel structure.
+/
struct ParabolaKernel(T, uint derivative = 0)
    if (derivative <= 2)
{
    ///
    T a = 0;
    ///
    static if (derivative <= 1)
    T b = 0;
    ///
    static if (derivative == 0)
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
        static if (derivative <= 1)
        b = (d1 - a1 * a) / b1;
        static if (derivative == 0)
        c = y1 - x1 * (a * x1 + b);
    }

    ///
    auto opCall(V)(V x)
        if (!isSlice!V)
    {
        static if (derivative == 0)
           return (a * x + b) * x + c;
        else
        static if (derivative == 1)
            return 2 * a * x + b;
        else
            return 2 * a;        
    }

    /// ditto
    auto opCall(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, iterator) x)
    {
        import mir.ndslice.topology: indexed;
        return this.indexed(x);
    }

    ///
    alias opIndex = opCall;
}

///
unittest
{
    import std.math: approxEqual;

    alias f = (double x) => 3 * (x ^^ 2) + 7 * x + 5;
    auto p = ParabolaKernel!double(4, 9, 20, f(4), f(9), f(20));

    assert(p.a.approxEqual(3));
    assert(p.b.approxEqual(7));
    assert(p.c.approxEqual(5));
    assert(p(10).approxEqual(f(10)));
}
