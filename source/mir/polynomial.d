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

typeof(F.init * X.init * 1f + F.init) polyImpl(X, T, F, uint derivative = 0)(in X x, in T coefficients)
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
template poly(F, uint derivative = 0)
{
    import mir.ndslice.slice: Slice, SliceKind;

    /++
    Params:
        x = value to evaluate
        coefficients = coefficients of polynomial
    +/
    typeof(F.init * X.init * 1f + F.init) poly(X, T : Slice!(const(U)*, 1, sliceKind), U, SliceKind sliceKind)
        (in X x, T coefficients)
    {
        import core.lifetime: move;
        return polyImpl!(X, T, F, derivative)(x, coefficients.move);
    }

    /// ditto
    typeof(F.init * X.init * 1f + F.init) poly(X, T)(in X x, scope const T[] coefficients...)
    {
        return polyImpl!(X, typeof(coefficients), F, derivative)(x, coefficients);
    }
}

/// ditto
template poly(uint derivative = 0)
{
    import mir.ndslice.slice: Slice, SliceKind;

    /// ditto
    typeof(U.init * X.init * 1f + U.init) poly(X, T : Slice!(const(U)*, 1, sliceKind), U, SliceKind sliceKind)
        (in X x, T coefficients)
    {
        import core.lifetime: move;
        return polyImpl!(X, T, U, derivative)(x, coefficients.move);
    }

    /// ditto
    typeof(T.init * X.init * 1f + T.init) poly(X, T)(in X x, scope const T[] coefficients...)
    {
        return polyImpl!(X, typeof(coefficients), T, derivative)(x, coefficients);
    }
}

///
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0, 4.5, 1.9, 2];
    auto x = a.sliced;

    alias   f = (x) =>     3.0 +     4.5 * x^^1 +   1.9 * x^^2 + 2 * x^^3;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2;
    alias d2f = (x) => 2 * 1.9 + 6 *   2 * x^^1;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly(7.2, x).approxEqual(f(7.2)));

    assert(poly!1(3.3, x).approxEqual(df(3.3)));
    assert(poly!1(7.2, x).approxEqual(df(7.2)));

    assert(poly!2(3.3, x).approxEqual(d2f(3.3)));
    assert(poly!2(7.2, x).approxEqual(d2f(7.2)));

    // can also control the type
    assert(poly!real(3.3, x).approxEqual(f(3.3)));
}

/// Dynamic array
version (mir_test) @safe pure nothrow unittest
{
    import mir.math.common: approxEqual;
    double[] x = [3.0, 4.5, 1.9, 2];

    alias   f = (x) =>     3.0 +     4.5 * x^^1 +   1.9 * x^^2 + 2 * x^^3;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2;
    alias d2f = (x) => 2 * 1.9 + 6 *   2 * x^^1;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly!real(3.3, x).approxEqual(f(3.3)));
}

// Check coefficient.length = 3
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0, 4.5, 1.9];
    auto x = a.sliced;

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
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0, 4.5];
    auto x = a.sliced;

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
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0];
    auto x = a.sliced;

    alias  f = (x) => 3.0;
    alias df = (x) => 0.0;

    assert(poly(3.3, x).approxEqual(f(3.3)));
    assert(poly(7.2, x).approxEqual(f(7.2)));

    assert(poly!1(3.3, x).approxEqual(df(3.3)));
    assert(poly!1(7.2, x).approxEqual(df(7.2)));
}

typeof(F.init * X.init * 1f + F.init) monicImpl(X, T, F, uint derivative = 0)(in X x, in T coefficients)
{
    import mir.internal.utility: Iota;
    auto ret = cast(typeof(return))0;
    if (coefficients.length > 0)
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

/++
Evaluate monic polynomial (leading coefficient equals 1).

Coefficients assumed to be in the order: a0 + a1 * x ^^ 1 + ... + aN * x ^^ N + x ^^ (N + 1)

Params:
    F = controls type of output
    derivative = order of derivatives (default = 0)

Returns:
    Value of the monic polynomial, evaluated at `x`

See_also:
    $(WEB en.wikipedia.org/wiki/Monic_polynomial, Monic polynomial).
+/
template monic(F, uint derivative = 0)
{
    import mir.ndslice.slice: Slice, SliceKind;

    /++
    Params:
        x = value to evaluate
        coefficients = coefficients of polynomial
    +/
    typeof(F.init * X.init * 1f + F.init) monic(X, T : Slice!(const(U)*, 1, sliceKind), U, SliceKind sliceKind)
        (in X x, T coefficients)
    {
        import core.lifetime: move;
        return monicImpl!(X, T, F, derivative)(x, coefficients.move);
    }

    /// ditto
    typeof(F.init * X.init * 1f + F.init) monic(X, T)(in X x, scope const T[] coefficients...)
    {
        return monicImpl!(X, typeof(coefficients), F, derivative)(x, coefficients);
    }
}

/// ditto
template monic(uint derivative = 0)
{
    import mir.ndslice.slice: Slice, SliceKind;

    /// ditto
    typeof(U.init * X.init * 1f + U.init) monic(X, T : Slice!(const(U)*, 1, sliceKind), U, SliceKind sliceKind)
        (in X x, T coefficients)
    {
        import core.lifetime: move;
        return monicImpl!(X, T, U, derivative)(x, coefficients.move);
    }

    /// ditto
    typeof(T.init * X.init * 1f + T.init) monic(X, T)(in X x, scope const T[] coefficients...)
    {
        return monicImpl!(X, typeof(coefficients), T, derivative)(x, coefficients);
    }
}

///
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0, 4.5, 1.9, 2];
    auto x = a.sliced;

    alias   f = (x) =>     3.0 +     4.5 * x^^1 +   1.9 * x^^2 + 2 * x^^3 + x^^4;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1 + 3 * 2 * x^^2 + 4 * x^^3;
    alias d2f = (x) => 2 * 1.9 +   6 * 2 * x^^1 + 3 * 4 * x^^2;

    assert(monic(3.3, x).approxEqual(f(3.3)));
    assert(monic(7.2, x).approxEqual(f(7.2)));

    assert(monic!1(3.3, x).approxEqual(df(3.3)));
    assert(monic!1(7.2, x).approxEqual(df(7.2)));

    assert(monic!2(3.3, x).approxEqual(d2f(3.3)));
    assert(monic!2(7.2, x).approxEqual(d2f(7.2)));

    // can also control the type
    assert(monic!real(3.3, x).approxEqual(f(3.3)));
}

/// Dynamic array
version (mir_test) @safe pure nothrow unittest
{
    import mir.math.common: approxEqual;
    double[] x = [3.0, 4.5, 1.9, 2];

    alias f = (x) =>  3.0 + 4.5 * x^^1 + 1.9 * x^^2 + 2 * x^^3 + x^^4;

    assert(monic(3.3, x).approxEqual(f(3.3)));
    assert(monic!real(3.3, x).approxEqual(f(3.3)));
}

// Check coefficient.length = 3
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0, 4.5, 1.9];
    auto x = a.sliced;

    alias   f = (x) =>     3.0 +     4.5 * x^^1 + 1.9 * x^^2 + x^^3;
    alias  df = (x) =>     4.5 + 2 * 1.9 * x^^1 +   3 * x^^2;
    alias d2f = (x) => 2 * 1.9 +       6 * x^^1;

    assert(monic(3.3, x).approxEqual(f(3.3)));
    assert(monic(7.2, x).approxEqual(f(7.2)));

    assert(monic!1(3.3, x).approxEqual(df(3.3)));
    assert(monic!1(7.2, x).approxEqual(df(7.2)));

    assert(monic!2(3.3, x).approxEqual(d2f(3.3)));
    assert(monic!2(7.2, x).approxEqual(d2f(7.2)));
}

// Check coefficient.length = 2
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0, 4.5];
    auto x = a.sliced;

    alias   f = (x) => 3.0 + 4.5 * x^^1 + x^^2;
    alias  df = (x) => 4.5 +   2 * x^^1;
    alias d2f = (x) => 2;

    assert(monic(3.3, x).approxEqual(f(3.3)));
    assert(monic(7.2, x).approxEqual(f(7.2)));

    assert(monic!1(3.3, x).approxEqual(df(3.3)));
    assert(monic!1(7.2, x).approxEqual(df(7.2)));

    assert(monic!2(3.3, x).approxEqual(d2f(3.3)));
    assert(monic!2(7.2, x).approxEqual(d2f(7.2)));
}

// Check coefficient.length = 1
version (mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    static immutable a = [3.0];
    auto x = a.sliced;

    alias  f = (x) => 3.0 + x^^1;
    alias df = (x) => 1;

    assert(monic(3.3, x).approxEqual(f(3.3)));
    assert(monic(7.2, x).approxEqual(f(7.2)));

    assert(monic!1(3.3, x).approxEqual(df(3.3)));
    assert(monic!1(7.2, x).approxEqual(df(7.2)));
}
