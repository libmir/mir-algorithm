/++
$(H2 Lagrange Barycentric Interpolation)

See_also: $(REF_ALTTEXT $(TT interp1), interp1, mir, interpolate)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate.polynomial;

///
public import mir.interpolate: atInterval;
import core.lifetime: move;
import mir.functional: Tuple;
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

@fmamath:

///
version(mir_test)
// @safe pure
unittest
{
    import mir.test;
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

        lx.shouldApprox == f(testX);
        assert(l_ldx[].all!approxEqual(fWithDerivative(testX)[]));
        assert(l_ld_ld2x[].all!approxEqual(fWithTwoDerivatives(testX)[]));
    }
}

/++
Constructs barycentric lagrange interpolant.
+/
Lagrange!(T, maxDerivative) lagrange(uint maxDerivative = 0, T, X)(scope const X[] x, scope const T[] y) @trusted
    if (maxDerivative < 16)
{
    import mir.ndslice.allocation: rcslice;
    return x.rcslice!(immutable X).lagrange!maxDerivative(y.sliced);
}

/// ditto
Lagrange!(Unqual!(Slice!(Iterator, 1, kind).DeepElement), maxDerivative, X)
    lagrange(uint maxDerivative = 0, X, Iterator, SliceKind kind)(Slice!(RCI!(immutable X)) x, Slice!(Iterator, 1, kind) y) @trusted
    if (maxDerivative < 16)
{
    alias T = Unqual!(Slice!(Iterator, 1, kind).DeepElement);
    return Lagrange!(T, maxDerivative)(x.move, rcarray!T(y));
}

/++
+/
struct Lagrange(T, uint maxAdditionalFunctions = 0, X = T)
    if (isFloatingPoint!T && maxAdditionalFunctions < 16)
{
    /// $(RED for internal use only.)
    Slice!(RCI!(immutable X)) _grid;
    /// $(RED for internal use only.)
    RCArray!(immutable T) _inversedBarycentricWeights;
    /// $(RED for internal use only.)
    RCArray!T[maxAdditionalFunctions + 1] _normalizedValues;
    /// $(RED for internal use only.)
    T[maxAdditionalFunctions + 1] _asums;

@fmamath @safe pure @nogc extern(D):

    ///
    enum uint derivativeOrder = maxAdditionalFunctions;
    ///
    enum uint dimensionCount = 1;

    /++
    Complexity: `O(N)`
    +/
    pragma(inline, false)
    this(Slice!(RCI!(immutable X)) grid, RCArray!T values, RCArray!(immutable T) inversedBarycentricWeights)
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
            if (!grid.lightScope.diff.all!(a => md <= a && a <= T.max))
                { import mir.exception : toMutable; throw exc.toMutable; }
        }
        swap(_grid, grid);
        swap(_inversedBarycentricWeights, inversedBarycentricWeights);
        swap(_normalizedValues[0], values);
        auto w = _inversedBarycentricWeights[].sliced;
        foreach (_; Iota!maxAdditionalFunctions)
        {
            auto y = _normalizedValues[_][].sliced;
            static if (_ == 0)
                _asums[_] = y.asumNorm;
            _normalizedValues[_ + 1] = RCArray!T(_grid.length, true, false);
            auto d = _normalizedValues[_ + 1][].sliced;
            polynomialDerivativeValues(d, _grid.lightScope, y, w);
            _asums[_ + 1] = d.asumNorm * _asums[_];
        }
    }

    /++
    Complexity: `O(N^^2)`
    +/
    this(Slice!(RCI!(immutable X)) grid, RCArray!T values)
    {
        import core.lifetime: move; 
        auto weights = grid.lightScope.inversedBarycentricWeights;
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
        ref const(Slice!(RCI!(immutable X))) grid() { return _grid; }
        ///
        immutable(X)[] gridScopeView() return scope const @property @trusted { return _grid.lightScope.field; }
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
            return opCall!derivative(Tuple!(size_t, T)(this.findInterval(x), x));
        }

        ///
        pragma(inline, false)
        auto opCall(Tuple!(size_t, T) tuple)
        {

            const x = tuple[1];
            const idx = tuple[0];
            const inversedBarycentricWeights = _inversedBarycentricWeights[].sliced;
            Slice!(const(T)*)[derivative + 1] values;
            foreach (i; Iota!(derivative + 1))
                values[i] = _normalizedValues[i][].sliced;
            const T[2] pd = [
                T(x - _grid[idx + 0]).fabs,
                T(x - _grid[idx + 1]).fabs,
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
            foreach (i; 0 .. _grid.length)
            {
                T w = 1 / (inversedBarycentricWeights[i] * (x - _grid[i]));
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
RCArray!(immutable T) inversedBarycentricWeights(T)(Slice!(const(T)*) x)
    if (isFloatingPoint!T)
{
    
    const n = x.length;
    scope prodsa = RCArray!(ProdAccumulator!T)(n);
    scope p = prodsa[].sliced;
    foreach (triplet; n.iota.triplets) with(triplet)
    {
        foreach (l; left)
        {
            auto e = prod!T(x[center] - x[l]);
            p[l] *= -e;
            p[center] *= e;
        }
    }
    import mir.algorithm.iteration: reduce;
    const minExp = long.max.reduce!min(p.member!"exp");
    foreach (ref e; p)
        e = e.ldexp(1 - minExp);
    auto ret = rcarray!(immutable T)(p.member!"prod");
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
