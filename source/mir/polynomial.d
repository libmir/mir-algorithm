/++
Polynomial ref-counted structure.

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilia Ki
+/
module mir.polynomial;

import mir.math.common: optmath;
import mir.rc.array;

@optmath:

/++
Polynomial callable ref-counted structure.
+/
struct Polynomial(F)
{
    ///
    RCArray!(const F) coefficients;

    /++
    Params:
        coefficients = coefficients `c[i]` for polynomial function `f(x)=c[0]+c[1]*x^^1+...+c[n]*x^^n`
    +/
    this(RCArray!(const F) coefficients)
    {
        import core.lifetime: move;
        this.coefficients = coefficients.move;
    }

    /++
    Params:
        derivative = derivative order
    +/
    template opCall(uint derivative = 0)
    {
        /++
        Params:
            x = `x` point
        +/
        @optmath typeof(F.init * X.init * 1f + F.init) opCall(X)(in X x) const
        {
            return x.poly!derivative(this.coefficients[]);
        }
    }
}

/// ditto
Polynomial!F polynomial(F)(RCArray!(const F) coefficients)
{
    import core.lifetime: move;
    return typeof(return)(coefficients.move);
}

///
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.rc.array;
    auto a = rcarray!(const double)(3.0, 4.5, 1.9, 2);
    auto p = a.polynomial;

    alias   f = (x) =>     3.0 +     4.5 * x^^1 +   1.9 * x^^2 + 2 * x^^3;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2;
    alias d2f = (x) => 2 * 1.9 + 6 *   2 * x^^1;

    assert(p(3.3).approxEqual(f(3.3)));
    assert(p(7.2).approxEqual(f(7.2)));

    assert(p.opCall!1(3.3).approxEqual(df(3.3)));
    assert(p.opCall!1(7.2).approxEqual(df(7.2)));

    assert(p.opCall!2(3.3).approxEqual(d2f(3.3)));
    assert(p.opCall!2(7.2).approxEqual(d2f(7.2)));
}

/++
Evaluate polynomial.

Coefficients assumed to be in the order a0 + a1 * x ^^ 1 + ... + aN * x ^^ N

Params:
    F = controls type of output
    derivative = order of derivatives (default = 0)

Returns:
    Value of the polynomial, evaluated at `x`

See_also:
    $(WEB en.wikipedia.org/wiki/Polynomial, Polynomial).
+/
template poly(uint derivative = 0)
{
    import std.traits: ForeachType;
    /++
    Params:
        x = value to evaluate
        coefficients = coefficients of polynomial
    +/
    @optmath typeof(F.init * X.init * 1f + F.init) poly(X, F)(in X x, scope const F[] coefficients...)
    {
        import mir.internal.utility: Iota;
        auto ret = cast(typeof(return))0;
        if (coefficients.length > 0)
        {
            ptrdiff_t i = coefficients.length - 1;
            assert(i >= 0);
            auto c = cast()coefficients[i];
            static foreach (d; Iota!derivative)
                c *= i - d;
            ret = cast(typeof(return)) c;
            while (--i >= cast(ptrdiff_t)derivative)
            {
                assert(i < coefficients.length);
                c = cast()coefficients[i];
                static foreach (d; Iota!derivative)
                    c *= i - d;
                ret *= x;
                ret += c;
            }
        }
        return ret;
    }
}

///
version (mir_test) @safe pure nothrow unittest
{
    import mir.math.common: approxEqual;

    double[] x = [3.0, 4.5, 1.9, 2];

    alias   f = (x) =>     3.0 +     4.5 * x^^1 +   1.9 * x^^2 + 2 * x^^3;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2;
    alias d2f = (x) => 2 * 1.9 + 6 *   2 * x^^1;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly(7.2, x).approxEqual(f(7.2)));

    assert(poly!1(3.3, x).approxEqual(df(3.3)));
    assert(poly!1(7.2, x).approxEqual(df(7.2)));

    assert(poly!2(3.3, x).approxEqual(d2f(3.3)));
    assert(poly!2(7.2, x).approxEqual(d2f(7.2)));
}

// static array test
version (mir_test) @safe pure @nogc nothrow unittest
{
    import mir.math.common: approxEqual;

    double[4] x = [3.0, 4.5, 1.9, 2];

    alias   f = (x) =>     3.0 +     4.5 * x^^1 +   1.9 * x^^2 + 2 * x^^3;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2;
    alias d2f = (x) => 2 * 1.9 + 6 *   2 * x^^1;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly(7.2, x).approxEqual(f(7.2)));

    assert(poly!1(3.3, x).approxEqual(df(3.3)));
    assert(poly!1(7.2, x).approxEqual(df(7.2)));

    assert(poly!2(3.3, x).approxEqual(d2f(3.3)));
    assert(poly!2(7.2, x).approxEqual(d2f(7.2)));
}

// Check coefficient.length = 3
version (mir_test) @safe pure nothrow unittest
{
    import mir.math.common: approxEqual;

    double[] x = [3.0, 4.5, 1.9];

    alias   f = (x) =>     3.0 +     4.5 * x^^1 + 1.9 * x^^2;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1;
    alias d2f = (x) => 2 * 1.9;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly(7.2, x).approxEqual(f(7.2)));

    assert(poly!1(3.3, x).approxEqual(df(3.3)));
    assert(poly!1(7.2, x).approxEqual(df(7.2)));

    assert(poly!2(3.3, x).approxEqual(d2f(3.3)));
    assert(poly!2(7.2, x).approxEqual(d2f(7.2)));
}

// Check coefficient.length = 2
version (mir_test) @safe pure nothrow unittest
{
    import mir.math.common: approxEqual;

    double[] x = [3.0, 4.5];

    alias   f = (x) => 3.0 + 4.5 * x^^1;
    alias  df = (x) => 4.5;
    alias d2f = (x) => 0.0;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly(7.2, x).approxEqual(f(7.2)));

    assert(poly!1(3.3, x).approxEqual(df(3.3)));
    assert(poly!1(7.2, x).approxEqual(df(7.2)));

    assert(poly!2(3.3, x).approxEqual(d2f(3.3)));
    assert(poly!2(7.2, x).approxEqual(d2f(7.2)));
}

// Check coefficient.length = 1
version (mir_test) @safe pure nothrow unittest
{
    import mir.math.common: approxEqual;

    double[] x = [3.0];

    alias  f = (x) => 3.0;
    alias df = (x) => 0.0;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly(7.2, x).approxEqual(f(7.2)));

    assert(poly!1(3.3, x).approxEqual(df(3.3)));
    assert(poly!1(7.2, x).approxEqual(df(7.2)));
}
