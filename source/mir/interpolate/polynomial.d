/++
$(H2 Lagrange Barycentric Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2019, Symmetry Investments & Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.polynomial;

public import mir.interpolate: atInterval;
import mir.functional: RefTuple;
import mir.internal.utility : isFloatingPoint, Iota;
import mir.interpolate: findInterval;
import mir.math.common;
import mir.math.numeric;
import mir.math.sum;
import mir.ndslice.slice;
import mir.ndslice.topology: diff, map, member, iota, triplets;
import mir.rc.array;
import mir.utility: min, swap;
import std.traits: Unqual;

@optmath:

///
version(mir_test)
@safe pure unittest
{
    import mir.algorithm.iteration: all;
    import mir.math;
    import mir.ndslice;

    auto f(double x) { return (x-2) * (x-5) * (x-9); }
    auto fd(double x) { return (x-5) * (x-9) + (x-2) * (x-5) + (x-2) * (x-9); }
    auto fd2(double x) { return (x-5) + (x-9) + (x-2) + (x-5) + (x-2) + (x-9); }
    double[2] fWithDerivative(double x) { return [f(x), fd(x)]; }
    double[3] fWithTwoDerivatives(double x) { return [f(x), fd(x), fd2(x)]; }

    // 
    auto x = [0.0, 3, 5, 10];
    auto y = x.map!f.slice.field;
    // `!2` adds first two derivatives: f, f', and f''
    // default parameter is 0
    auto l = x.lagrange!2(y);

    foreach(test; x ~ [2.0, 5, 9] ~ [double(PI), double(E), 10, 100, 1e3])
    foreach(scale; [-1, +1, 1 + double.epsilon, 1 + double.epsilon.sqrt])
    foreach(shift; [0, double.min_normal/2, double.min_normal*2, double.epsilon, double.epsilon.sqrt])
    {
        auto testX = test * scale + shift;

        auto lx = l(testX);
        auto l_ldx = l.withDerivative(testX);
        auto l_ld_ld2x = l.withTwoDerivatives(testX);

        assert(lx.approxEqual(f(testX)));
        assert(l_ldx[].all!approxEqual(fWithDerivative(testX)[]));
        assert(l_ld_ld2x[].all!approxEqual(fWithTwoDerivatives(testX)[]));
    }
}

/++
Constructs barycentric lagrange interpolant.
+/
Lagrange!(T, maxDerivative) lagrange(uint maxDerivative = 0, T, X)(scope const T[] x, scope const X[] y)
    if (maxDerivative < 16)
{
    return x.sliced.lagrange!maxDerivative(y.sliced);
}

/// ditto
Lagrange!(Unqual!(Slice!(YIterator, 1, ykind).DeepElement), maxDerivative)
    lagrange(uint maxDerivative = 0, XIterator, SliceKind xkind, YIterator, SliceKind ykind)(scope Slice!(XIterator, 1, xkind) x, scope Slice!(YIterator, 1, ykind) y) @trusted
    if (maxDerivative < 16)
{
    alias T = Unqual!(Slice!(YIterator, 1, ykind).DeepElement);
    return Lagrange!(T, maxDerivative)(rcarray!(immutable T)(x), rcarray!T(y));
}

/++
+/
struct Lagrange(T, uint maxAdditionalFunctions = 0)
    if (isFloatingPoint!T && maxAdditionalFunctions < 16)
{
    /// $(RED for internal use only.)
    RCArray!(immutable T) _grid;
    /// $(RED for internal use only.)
    RCArray!(immutable T) _inversedBarycentricWeights;
    /// $(RED for internal use only.)
    RCArray!T[maxAdditionalFunctions + 1] _normalizedValues;
    /// $(RED for internal use only.)
    T[maxAdditionalFunctions + 1] _asums;

@optmath @safe pure @nogc:

    /++
    Complexity: `O(N)`
    +/
    pragma(inline, false)
    this(RCArray!(immutable T) grid, RCArray!T values, RCArray!(immutable T) inversedBarycentricWeights)
    {
        import mir.algorithm.iteration: all;
        assert(grid.length > 1);
        assert(grid.length == values.length);
        assert(grid.length == inversedBarycentricWeights.length);
        enum msg = "Lagrange: grid points are too close or have not finite values.";
        version(D_Exceptions)
        {
            enum T md = T.min_normal / T.epsilon;
            static immutable exc = new Exception(msg);
            if (!grid[].diff.all!(a => md <= a && a <= T.max))
                throw exc;
        }
        swap(_grid, grid);
        swap(_inversedBarycentricWeights, inversedBarycentricWeights);
        swap(_normalizedValues[0], values);
        auto x = _grid[].sliced;
        auto w = _inversedBarycentricWeights[].sliced;
        foreach (_; Iota!maxAdditionalFunctions)
        {
            auto y = _normalizedValues[_][].sliced;
            static if (_ == 0)
                _asums[_] = y.asumNorm;
            _normalizedValues[_ + 1] = RCArray!T(x.length, true, false);
            auto d = _normalizedValues[_ + 1][].sliced;
            polynomialDerivativeValues(d, x, y, w);
            _asums[_ + 1] = d.asumNorm * _asums[_];
        }
    }

    /++
    Complexity: `O(N^^2)`
    +/
    this(RCArray!(immutable T) grid, RCArray!T values)
    {
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        auto weights = grid[].sliced.inversedBarycentricWeights;
        this(grid.move, values.move, weights.move);
    }

scope const:

    ///
    Lagrange lightConst()() const @property @trusted { return *cast(Lagrange*)&this; }
    ///
    Lagrange lightImmutable()() immutable @property @trusted { return *cast(Lagrange*)&this; }

    @property
    {
        ///
        ref const(RCArray!(immutable T)) grid() { return _grid; }
        ///
        ref const(RCArray!(immutable T)) inversedBarycentricWeights() { return _inversedBarycentricWeights; }
        ///
        ref const(RCArray!T)[maxAdditionalFunctions + 1] normalizedValues() { return _normalizedValues; }
        ///
        ref const(T)[maxAdditionalFunctions + 1] asums() { return _asums; }
        ///
        size_t intervalCount(size_t dimension = 0)()
        {
            assert(_grid.length > 1);
            return _grid.length - 1;
        }
    }

    template opCall(uint derivative = 0)
        if (derivative <= maxAdditionalFunctions)
    {
        ///
        pragma(inline, false)
        auto opCall(T x)
        {
            return opCall!derivative(RefTuple!(size_t, T)(this.findInterval(x), x));
        }

        ///
        pragma(inline, false)
        auto opCall(RefTuple!(size_t, T) tuple)
        {

            const x = tuple[1];
            const idx = tuple[0];
            const grid = _grid[].sliced;
            const inversedBarycentricWeights = _inversedBarycentricWeights[].sliced;
            scope Slice!(const(T)*)[derivative + 1] values;
            foreach (i; Iota!(derivative + 1))
                values[i] = _normalizedValues[i][].sliced;
            const T[2] pd = [
                T(x - grid[idx + 0]).fabs,
                T(x - grid[idx + 1]).fabs,
            ];
            ptrdiff_t fastIndex =
                pd[0] < T.min_normal ? idx + 0 :
                pd[1] < T.min_normal ? idx + 1 :
                -1;
            if (fastIndex >= 0)
            {
                static if (derivative == 0)
                {
                    return values[0][fastIndex] * _asums[0];
                }
                else
                {
                    T[derivative + 1] ret = 0;
                    foreach (_; Iota!(derivative + 1))
                        ret[_] = values[_][fastIndex] * _asums[_];
                    return ret;
                }
            }
            T d = 0;
            T[derivative + 1] n = 0;
            foreach (i; 0 .. grid.length)
            {
                T w = 1 / (inversedBarycentricWeights[i] * (x - grid[i]));
                d += w;
                foreach (_; Iota!(derivative + 1))
                    n[_] += w * values[_][i];
            }
            foreach (_; Iota!(derivative + 1))
            {
                n[_] /= d;
                n[_] *= asums[_];
            }
            static if (derivative == 0)
                return n[0];
            else
                return n;
        }
    }

    static if (maxAdditionalFunctions)
    {
        ///
        alias withDerivative = opCall!1;

        static if (maxAdditionalFunctions > 1)
        {
            ///
            alias withTwoDerivatives = opCall!2;
        }
    }
}


/++
+/
pragma(inline, false)
@nogc
RCArray!(immutable T) inversedBarycentricWeights(T)(scope Slice!(const(T)*) x)
    if (isFloatingPoint!T)
{
    const n = x.length;
    scope prodsa = RCArray!(Prod!T)(n);
    scope p = prodsa[].sliced;
    foreach (triplet; n.iota.triplets) with(triplet)
    {
        foreach (l; left)
        {
            auto e = wipProd(x[center] - x[l]);
            p[l] *= -e;
            p[center] *= e;
        }
    }
    import mir.algorithm.iteration: reduce;
    const minExp = long.max.reduce!min(p.member!"exp");
    foreach (ref e; p)
        e = e.ldexp(1 - minExp);
    auto ret = rcarray!(immutable T)(p.member!"value");
    return ret;
}

/++
Computes derivative values in the same points
Params:
    d = derivative values (output)
    y = values
    x = grid
    w = inversed barycentric weights
Returns:
    Derivative values in the same points
+/
@nogc
Slice!(T*) polynomialDerivativeValues(T)(return Slice!(T*) d,  Slice!(const(T)*) x,  Slice!(const(T)*) y,  Slice!(const(T)*) w)
    if (isFloatingPoint!T)
{
    pragma(inline, false);
    import mir.math.sum;

    const n = x.length;
    assert(n == w.length);
    assert(n == y.length);

    d.fillCollapseSums!(Summation.fast,
        (c, s1, s2) => w[c] * s1 + y[c] * s2,
        (c, _) => y[_] / (w[_] * (x[c] - x[_])),
        (c, _) => map!"1 / a"(x[c] - x[_]));
    return d;
}

///
@nogc
Slice!(T*) polynomialDerivativeValues(T)(return Slice!(T*) d,  Slice!(const(T)*) x,  Slice!(const(T)*) y)
    if (isFloatingPoint!T)
{
    return .polynomialDerivativeValues(d, x, y, x.inversedBarycentricWeights[].sliced);
}

private T asumNorm(T)(Slice!(T*) v)
{
    pragma(inline, false);
    auto n = v.map!fabs.sum!"fast";
    v[] /= n;
    return n;
}
