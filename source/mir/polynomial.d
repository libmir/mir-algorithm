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
            import mir.internal.utility: Iota;
            auto ret = cast(typeof(return))0;
            if (coefficients)
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

    alias f = (x) => 3.0 + 4.5 * x^^1 + 1.9 * x^^2 + 2 * x^^3;
    alias df = (x) => 4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2;
    alias d2f = (x) => 2 * 1.9  + 6 * 2 * x^^1;

    assert(p(3.3).approxEqual(f(3.3)));
    assert(p(7.2).approxEqual(f(7.2)));

    assert(p.opCall!1(3.3).approxEqual(df(3.3)));
    assert(p.opCall!1(7.2).approxEqual(df(7.2)));

    assert(p.opCall!2(3.3).approxEqual(d2f(3.3)));
    assert(p.opCall!2(7.2).approxEqual(d2f(7.2)));
}

/++
Monic polynomial (leading coefficient equals 1) callable ref-counted structure.

See_also:
    $(WEB en.wikipedia.org/wiki/Monic_polynomial, Monic polynomial).

+/
struct Monic(F)
{
    ///
    RCArray!(const F) coefficients;

    /++
    Params:
        coefficients = coefficients `c[i]` for polynomial function `f(x)=c[0]+c[1]*x^^1+...+c[n]*x^^(n - 1)+x^^n`
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
            import mir.internal.utility: Iota;
            auto ret = cast(typeof(return))0;
            if (coefficients)
            {
                ptrdiff_t i = coefficients.length - 1;
                assert(i >= 0);
                ptrdiff_t j = 1;
                static foreach (d; Iota!derivative) {
                    j *= i - d + 1;
                }
                ret += j;
                typeof(cast()coefficients[0]) c;
                if (i >= cast(ptrdiff_t)derivative) {
                    do
                    {
                        assert(i < coefficients.length);
                        ret *= x;
                        c = cast()coefficients[i];
                        static foreach (d; Iota!derivative)
                            c *= i - d;
                        ret += c;
                    } while (--i >= cast(ptrdiff_t)derivative);
                }
            }
            return ret;
        }
    }
}

/// ditto
Monic!F monic(F)(RCArray!(const F) coefficients)
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
    auto m = a.monic;

    alias f = (x) =>       3.0 +     4.5 * x^^1 +   1.9 * x^^2 + 2 * x^^3 + x^^4;
    alias df = (x) =>      4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2 + 4 * x^^3;
    alias d2f = (x) => 2 * 1.9 +   6 * 2 * x^^1 + 3 * 4 * x^^2;

    assert(m(3.3).approxEqual(f(3.3)));
    assert(m(7.2).approxEqual(f(7.2)));

    assert(m.opCall!1(3.3).approxEqual(df(3.3)));
    assert(m.opCall!1(7.2).approxEqual(df(7.2)));

    assert(m.opCall!2(3.3).approxEqual(d2f(3.3)));
    assert(m.opCall!2(7.2).approxEqual(d2f(7.2)));
}

version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.rc.array;
    auto a = rcarray!(const double)(3.0, 4.5, 1.9);
    auto m = a.monic;

    alias f = (x) =>       3.0 +     4.5 * x^^1 + 1.9 * x^^2 + x^^3;
    alias df = (x) =>      4.5 + 2 * 1.9 * x^^1 +   3 * x^^2;
    alias d2f = (x) => 2 * 1.9 +       6 * x^^1;

    assert(m(3.3).approxEqual(f(3.3)));
    assert(m(7.2).approxEqual(f(7.2)));

    assert(m.opCall!1(3.3).approxEqual(df(3.3)));
    assert(m.opCall!1(7.2).approxEqual(df(7.2)));

    assert(m.opCall!2(3.3).approxEqual(d2f(3.3)));
    assert(m.opCall!2(7.2).approxEqual(d2f(7.2)));
}

version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.rc.array;
    auto a = rcarray!(const double)(3.0, 4.5);
    auto m = a.monic;

    alias f = (x) =>   3.0 + 4.5 * x^^1 + x^^2;
    alias df = (x) =>  4.5 +   2 * x^^1;
    alias d2f = (x) =>   2;

    assert(m(3.3).approxEqual(f(3.3)));
    assert(m(7.2).approxEqual(f(7.2)));

    assert(m.opCall!1(3.3).approxEqual(df(3.3)));
    assert(m.opCall!1(7.2).approxEqual(df(7.2)));

    assert(m.opCall!2(3.3).approxEqual(d2f(3.3)));
    assert(m.opCall!2(7.2).approxEqual(d2f(7.2)));
}

version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.rc.array;
    auto a = rcarray!(const double)(3.0);
    auto m = a.monic;

    alias f = (x) =>  3.0 + x^^1;
    alias df = (x) => 1;

    assert(m(3.3).approxEqual(f(3.3)));
    assert(m(7.2).approxEqual(f(7.2)));

    assert(m.opCall!1(3.3).approxEqual(df(3.3)));
    assert(m.opCall!1(7.2).approxEqual(df(7.2)));
}
