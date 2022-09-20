/++
$(H1 Interpolation Algorithms)

$(BOOKTABLE $(H2 Interpolation modules),
$(TR $(TH Module) $(TH Interpolation kind))
$(T2M constant, Constant Interpolant)
$(T2M generic, Generic Piecewise Interpolant)
$(T2M linear, Linear Interpolant)
$(T2M polynomial, Lagrange Barycentric Interpolant)
$(T2M spline, Piecewise Cubic Hermite Interpolant Spline: C2 (with contiguous second derivative), cardinal, monotone (aka PCHIP), double-quadratic, Akima)
)
]
Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir,interpolate, $1)$(NBSP)
T2M=$(TR $(TDNW $(MREF mir,interpolate,$1)) $(TD $+))
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.interpolate;

import mir.functional: RefTuple;
import mir.math.common: optmath;
import mir.ndslice.slice: Slice, Contiguous;
import mir.primitives;
import mir.qualifier;
import std.traits: isInstanceOf;

@optmath:

package ref iter(alias s)() { return s._iterator; };
package alias GridVector(It) = Slice!It;

package enum bool isInterval(T) = isInstanceOf!(RefTuple, T);
package enum bool isInterval(alias T) = isInstanceOf!(RefTuple, T);

package template Repeat(ulong n, L...)
{
    static if (n)
    {
        static import std.meta;
        alias Repeat = std.meta.Repeat!(n, L);
    }
    else
        alias Repeat = L[0 .. 0];
}

/++
Interval index for x value given.
+/
template findInterval(size_t dimension = 0)
{
    /++
    Interval index for x value given.
    Params:
        interpolant = interpolant
        x = X value
    +/
    size_t findInterval(Interpolant, X)(auto ref const Interpolant interpolant, in X x) @trusted
    {
        import mir.ndslice.slice: sliced;
        import mir.ndslice.sorting: transitionIndex;
        static if (dimension)
        {
            immutable sizediff_t len = interpolant.intervalCount!dimension - 1;
            auto grid = interpolant.gridScopeView!dimension[1 .. $][0 .. len];
        }
        else
        {
            immutable sizediff_t len = interpolant.intervalCount - 1;
            auto grid = interpolant.gridScopeView[1 .. $][0 .. len];
        }
        assert(len >= 0);
        return grid.transitionIndex!"a <= b"(x);
    }
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: rcslice;
    import mir.ndslice.topology: as;
    import mir.ndslice.slice: sliced;
    import mir.interpolate.linear;

    static immutable x = [0.0, 1, 2];
    static immutable y = [10.0, 2, 4];
    auto interpolation = linear!double(x.rcslice, y.as!(const double).rcslice);
    assert(interpolation.findInterval(1.0) == 1);
}

/++
Lazy interpolation shell with linear complexity.

Params:
    range = sorted range
    interpolant = interpolant structure with `.gridScopeView` method.
Complexity:
    `O(range.length + interpolant.gridScopeView.length)` to evaluate all elements.
Returns:
    Lazy input range.
See_also:
    $(SUBREF linear, linear),
    $(SUBREF spline, spline).
+/
auto interp1(Range, Interpolant)(Range range, Interpolant interpolant, size_t interval = 0)
{
    return Interp1!(Range, Interpolant)(range, interpolant, interval);
}

/// ditto
struct Interp1(Range, Interpolant)
{
    /// Sorted range (descending). $(RED For internal use.)
    private Range _range;
    ///  Interpolant structure. $(RED For internal use.)
    private Interpolant _interpolant;
    /// Current interpolation interval. $(RED For internal use.)
    private size_t _interval;

    ///
    auto lightScope() scope
    {
        return Interp1!(LightScopeOf!Range, LightScopeOf!Interpolant)(.lightScope(_range), .lightScope(_interpolant), _interval);
    }

    static if (hasLength!Range)
    /// Length (optional)
    size_t length()() const @property  { return _range.length; }
    /// Save primitive (optional)
    auto save()() @property
    {
        auto ret = this;
        ret._range = _range.save;
        return ret;
    }
    /// Input range primitives
    bool empty () const @property  { return _range.empty;  }
    /// ditto
    void popFront() { _range.popFront; }
    /// ditto
    auto front() @property
        
    {
        assert(!empty);
        auto x = _range.front;
        return (x) @trusted {
            auto points = _interpolant.gridScopeView;
            sizediff_t len = _interpolant.intervalCount - 1;
            assert(len >= 0);
            while (x > points[_interval + 1] && _interval < len)
                _interval++;
            return _interpolant(x.atInterval(_interval));
        } (x);
    }
}

/++
PCHIP interpolation.
+/
version(mir_test)
@safe unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: rcslice;
    import mir.interpolate: interp1;
    import mir.interpolate.spline;

    static immutable x = [1.0, 2, 4, 5, 8, 10, 12, 15, 19, 22];
    static immutable y = [17.0, 0, 16, 4, 10, 15, 19, 5, 18, 6];
    auto interpolation = spline!double(x.rcslice, y.sliced, SplineType.monotone);

    auto xs = x[0 .. $ - 1].sliced + 0.5;

    auto ys = xs.interp1(interpolation);
}

@safe pure @nogc version(mir_test) unittest
{
    import mir.interpolate.linear;
    import mir.ndslice;
    import mir.math.common: approxEqual;

    static immutable x = [0, 1, 2, 3, 5.00274, 7.00274, 10.0055, 20.0137, 30.0192];
    static immutable y = [0.0011, 0.0011, 0.0030, 0.0064, 0.0144, 0.0207, 0.0261, 0.0329, 0.0356,];
    static immutable xs = [1, 2, 3, 4.00274, 5.00274, 6.00274, 7.00274, 8.00548, 9.00548, 10.0055, 11.0055, 12.0082, 13.0082, 14.0082, 15.0082, 16.011, 17.011, 18.011, 19.011, 20.0137, 21.0137, 22.0137, 23.0137, 24.0164, 25.0164, 26.0164, 27.0164, 28.0192, 29.0192, 30.0192];

    auto interpolation = linear!double(x.rcslice, y.as!(const double).rcslice);

    static immutable data = [0.0011, 0.0030, 0.0064, 0.0104, 0.0144, 0.0176, 0.0207, 0.0225, 0.0243, 0.0261, 0.0268, 0.0274, 0.0281, 0.0288, 0.0295, 0.0302, 0.0309, 0.0316, 0.0322, 0.0329, 0.0332, 0.0335, 0.0337, 0.0340, 0.0342, 0.0345, 0.0348, 0.0350, 0.0353, 0.0356];

    () @trusted {
        assert(all!((a, b) => approxEqual(a, b, 1e-4, 1e-4))(xs.interp1(interpolation), data));
    }();
}

/++
Optimization utility that can be used with interpolants if
x should be extrapolated at interval given.

By default interpolants uses binary search to find appropriate interval,
it has `O(log(.gridScopeView.length))` complexity.
If an interval is given, interpolant uses it instead of binary search.
+/
RefTuple!(T, size_t) atInterval(T)(in T value, size_t intervalIndex)
{
    return typeof(return)(value, intervalIndex);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    import mir.interpolate.spline;
    static immutable x = [0.0, 1, 2];
    static immutable y = [3.0, 4, -10];
    auto interpolant = spline!double(x.rcslice, y.sliced);
    assert(interpolant(1.3) != interpolant(1.3.atInterval(0)));
    assert(interpolant(1.3) == interpolant(1.3.atInterval(1)));
}

version(D_AVX2)
    enum _avx = true;
else
version(D_AVX)
    enum _avx = true;
else
    enum _avx = false;

version(LDC)
    enum LDC = true;
else
    enum LDC = false;

version(X86_64)
    enum x86_64 = true;
else
    enum x86_64 = false;

auto copyvec(F, size_t N)(ref const F[N] from, ref F[N] to)
{
    import mir.internal.utility;

    static if (LDC && F.mant_dig != 64 && is(__vector(F[N])))
    {
        alias V = __vector(F[N]); // @FUTURE@ vector support
        *cast(V*) to.ptr = *cast(V*) from.ptr;
    }
    else
    static if (F.sizeof <= double.sizeof && F[N].sizeof >= (double[2]).sizeof && x86_64)
    {
        import mir.utility;
        enum S = _avx ? 32u : 16u;
        enum M = min(S, F[N].sizeof) / F.sizeof;
        alias V = __vector(F[M]); // @FUTURE@ vector support
        enum C = N / M;
        foreach(i; Iota!C)
        {
            *cast(V*)(to.ptr + i * M) = *cast(V*)(from.ptr + i * M);
        }
    }
    else
    {
        to = from;
    }
}

package template SplineReturnType(F, size_t N, size_t P)
{
    static if (P <= 1 || N == 0)
        alias SplineReturnType = F;
    else
        alias SplineReturnType = .SplineReturnType!(F, N - 1, P)[P];
}

template generateShuffles3(size_t N, size_t P)
{
    enum size_t[N][2] generateShuffles3 = 
    ()
    {
        auto ret = new size_t[](2 * N);
        size_t[2] j;
        bool f = 1;
        foreach(i; 0 .. N)
        {
            ret[i * 2] = i;
            ret[i * 2 + 1] = i + N;
        }
        return [ret[0 .. $ / 2], ret[$ / 2 .. $]];
    }();
}


void shuffle3(size_t P, F, size_t N)(ref F[N] a, ref F[N] b, ref F[N] c, ref F[N] d)
    if (P <= N && N)
{
    static if (P == 0 || N == 1)
    {
        copyvec(a, c);
        copyvec(b, d);
    }
    else
    version(LDC)
    {
        enum masks = generateShuffles3!(N, P);
        import std.meta: aliasSeqOf;
        import ldc.simd: shufflevector;
        alias V = __vector(F[N]); // @FUTURE@ vector support
        auto as = shufflevector!(V, aliasSeqOf!(masks[0]))(*cast(V*)a.ptr, *cast(V*)b.ptr);
        auto bs = shufflevector!(V, aliasSeqOf!(masks[1]))(*cast(V*)a.ptr, *cast(V*)b.ptr);
        *cast(V*)c.ptr = as;
        *cast(V*)d.ptr = bs;
    }
    else
    {
        foreach(i; Iota!(N / P))
        {
            enum j = 2 * i * P;
            static if (j < N)
            {
                copyvec(a[i * P .. i * P + P], c[j .. j + P]);
                static assert(j + 2 * P <= c.length);
                copyvec(b[i * P .. i * P + P], c[j + P .. j + 2 * P]);
            }
            else
            {
                copyvec(a[i * P .. i * P + P], d[j - N .. j - N + P]);
                copyvec(b[i * P .. i * P + P], d[j - N + P .. j - N + 2 * P]);
            }
        }
    }
}

void shuffle2(size_t P, F, size_t N)(ref F[N] a, ref F[N] b, ref F[N] c, ref F[N] d)
    if (P <= N && N)
{
    static if (P == 0 || N == 1)
    {
        copyvec(a, c);
        copyvec(b, d);
    }
    else
    version(LDC)
    {
        enum masks = generateShuffles2!(N, P);
        import std.meta: aliasSeqOf;
        import ldc.simd: shufflevector;
        alias V = __vector(F[N]); // @FUTURE@ vector support
        auto as = shufflevector!(V, aliasSeqOf!(masks[0]))(*cast(V*)a.ptr, *cast(V*)b.ptr);
        auto bs = shufflevector!(V, aliasSeqOf!(masks[1]))(*cast(V*)a.ptr, *cast(V*)b.ptr);
        *cast(V*)c.ptr = as;
        *cast(V*)d.ptr = bs;
    }
    else
    {
        foreach(i; Iota!(N / P))
        {
            enum j = 2 * i * P;
            static if (j < N)
                copyvec(a[j .. j + P], c[i * P .. i * P + P]);
            else
                copyvec(b[j - N .. j - N + P], c[i * P .. i * P + P]);
        }
        foreach(i; Iota!(N / P))
        {
            enum j = 2 * i * P + P;
            static if (j < N)
                copyvec(a[j .. j + P], d[i * P .. i * P + P]);
            else
                copyvec(b[j - N .. j - N + P], d[i * P .. i * P + P]);
        }
    }
}

void shuffle1(size_t P, F, size_t N)(ref F[N] a, ref F[N] b, ref F[N] c, ref F[N] d)
    if (P <= N && N)
{
    static if (P == 0 || N == 1)
    {
        copyvec(a, c);
        copyvec(b, d);
    }
    else
    version(LDC)
    {
        enum masks = generateShuffles1!(N, P);
        import std.meta: aliasSeqOf;
        import ldc.simd: shufflevector;
        alias V = __vector(F[N]); // @FUTURE@ vector support
        auto as = shufflevector!(V, aliasSeqOf!(masks[0]))(*cast(V*)a.ptr, *cast(V*)b.ptr);
        auto bs = shufflevector!(V, aliasSeqOf!(masks[1]))(*cast(V*)a.ptr, *cast(V*)b.ptr);
        *cast(V*)c.ptr = as;
        *cast(V*)d.ptr = bs;
    }
    else
    {
        foreach(i; Iota!(N / P))
        {
            enum j = i * P;
            static if (i % 2 == 0)
                copyvec(a[j .. j + P], c[i * P .. i * P + P]);
            else
                copyvec(b[j - P .. j], c[i * P .. i * P + P]);
        }
        foreach(i; Iota!(N / P))
        {
            enum j = i * P + P;
            static if (i % 2 == 0)
                copyvec(a[j .. j + P], d[i * P .. i * P + P]);
            else
                copyvec(b[j - P .. j], d[i * P .. i * P + P]);
        }
    }
}

template generateShuffles2(size_t N, size_t P)
{
    enum size_t[N][2] generateShuffles2 = 
    ()
    {
        auto ret = new size_t[][](2, N);
        size_t[2] j;
        bool f = 1;
        foreach(i; 0 .. 2 * N)
        {
            if (i % P == 0)
                f = !f;
            ret[f][j[f]++] = i;
        }
        return ret;
    }();
}


template generateShuffles1(size_t N, size_t P)
{
    enum size_t[N][2] generateShuffles1 = 
    ()
    {
        auto ret = new size_t[][](2, N);
        foreach(i; 0 .. N)
        {
            ret[0][i] = (i / P + 1) % 2 ? i : i + N - P;
            ret[1][i] = ret[0][i] + P;
        }
        return ret;
    }();
}

unittest
{
    assert(generateShuffles1!(4, 1) == [[0, 4, 2, 6], [1, 5, 3, 7]]);
    assert(generateShuffles1!(4, 2) == [[0, 1, 4, 5], [2, 3, 6, 7]]);
    assert(generateShuffles1!(4, 4) == [[0, 1, 2, 3], [4, 5, 6, 7]]);
}

unittest
{
    assert(generateShuffles2!(4, 1) == [[0, 2, 4, 6], [1, 3, 5, 7]]);
    assert(generateShuffles2!(4, 2) == [[0, 1, 4, 5], [2, 3, 6, 7]]);
    assert(generateShuffles2!(4, 4) == [[0, 1, 2, 3], [4, 5, 6, 7]]);
}

unittest
{
    enum ai = [0, 1, 2, 3];
    enum bi = [4, 5, 6, 7];
    align(32)
    double[4] a = [0, 1, 2, 3], b = [4, 5, 6, 7], c, d;
    shuffle3!1(a, b, c, d);
    assert([c, d] == [[0.0, 4, 1, 5], [2.0, 6, 3, 7]]);
}

unittest
{
    enum ai = [0, 1, 2, 3];
    enum bi = [4, 5, 6, 7];
    align(32)
    double[4] a = [0, 1, 2, 3], b = [4, 5, 6, 7], c, d;
    shuffle2!1(a, b, c, d);
    assert([c, d] == [[0.0, 2, 4, 6], [1.0, 3, 5, 7]]);
    shuffle2!2(a, b, c, d);
    assert([c, d] == [[0.0, 1, 4, 5], [2.0, 3, 6, 7]]);
    // shuffle2!4(a, b, c, d);
    // assert([c, d] == [[0.0, 1, 2, 3], [4.0, 5, 6, 7]]);
}

unittest
{
    enum ai = [0, 1, 2, 3];
    enum bi = [4, 5, 6, 7];
    align(32)
    double[4] a = [0, 1, 2, 3], b = [4, 5, 6, 7], c, d;
    shuffle1!1(a, b, c, d);
    assert([c, d] == [[0, 4, 2, 6], [1, 5, 3, 7]]);
    shuffle1!2(a, b, c, d);
    assert([c, d] == [[0, 1, 4, 5], [2, 3, 6, 7]]);
    // shuffle1!4(a, b, c, d);
    // assert([c, d] == [[0, 1, 2, 3], [4, 5, 6, 7]]);
}

import mir.internal.utility;

auto vectorize(Kernel, F, size_t N, size_t R)(ref Kernel kernel, ref F[N] a0, ref F[N] b0, ref F[N] a1, ref F[N] b1, ref F[N][R] c)
{
    // static if (LDC && F.mant_dig != 64)
    // {
    //     alias V = __vector(F[N]); // @FUTURE@ vector support
    //     *cast(V[R]*) c.ptr = kernel(
    //         *cast(V*)a0.ptr, *cast(V*)b0.ptr,
    //         *cast(V*)a1.ptr, *cast(V*)b1.ptr);
    // }
    // else
    // static if (F.sizeof <= double.sizeof && F[N].sizeof >= (double[2]).sizeof)
    // {
    //     import mir.utility;
    //     enum S = _avx ? 32u : 16u;
    //     enum M = min(S, F[N].sizeof) / F.sizeof;
    //     alias V = __vector(F[M]); // @FUTURE@ vector support
    //     enum C = N / M;
    //     foreach(i; Iota!C)
    //     {
    //         auto r = kernel(
    //             *cast(V*)(a0.ptr + i * M), *cast(V*)(b0.ptr + i * M),
    //             *cast(V*)(a1.ptr + i * M), *cast(V*)(b1.ptr + i * M),
    //             );
    //         static if (R == 1)
    //             *cast(V*)(c[0].ptr + i * M) = r;
    //         else
    //             foreach(j; Iota!R)
    //                 *cast(V*)(c[j].ptr + i * M) = r[j];
    //     }
    // }
    // else
    // {
        foreach(i; Iota!N)
        {
            auto r = kernel(a0[i], b0[i], a1[i], b1[i]);
            static if (R == 1)
                c[0][i] = r;
            else
                foreach(j; Iota!R)
                    c[j][i] = r[j];
        }
    // }
}

auto vectorize(Kernel, F, size_t N, size_t R)(ref Kernel kernel, ref F[N] a, ref F[N] b, ref F[N][R] c)
{
    // static if (LDC && F.mant_dig != 64 && is(__vector(F[N])))
    // {
    //     alias V = __vector(F[N]); // @FUTURE@ vector support
    //     *cast(V[R]*) c.ptr = kernel(*cast(V*)a.ptr, *cast(V*)b.ptr);
    // }
    // else
    // static if (F.sizeof <= double.sizeof && F[N].sizeof >= (double[2]).sizeof && x86_64)
    // {
    //     import mir.utility;
    //     enum S = _avx ? 32u : 16u;
    //     enum M = min(S, F[N].sizeof) / F.sizeof;
    //     alias V = __vector(F[M]); // @FUTURE@ vector support
    //     enum C = N / M;
    //     foreach(i; Iota!C)
    //     {
    //         auto r = kernel(
    //             *cast(V*)(a.ptr + i * M),
    //             *cast(V*)(b.ptr + i * M),
    //             );
    //         static if (R == 1)
    //             *cast(V*)(c[0].ptr + i * M) = r;
    //         else
    //             foreach(j; Iota!R)
    //                 *cast(V*)(c[j].ptr + i * M) = r[j];
    //     }
    // }
    // else
    // {
        F[N][R] _c;//Temporary array in case "c" overlaps "a" and/or "b".
        foreach(i; Iota!N)
        {
            auto r = kernel(a[i], b[i]);
            static if (R == 1)
                _c[0][i] = r;
            else
                foreach(j; Iota!R)
                    _c[j][i] = r[j];
        }
        c = _c;
    // }
}

// version(unittest)
// template _test_fun(size_t R)
// {
//     auto _test_fun(T)(T a0, T b0, T a1, T b1)
//     {
//         static if (R == 4)
//         {
//             return cast(T[R])[a0, b0, a1, b1];
//         }
//         else
//         static if (R == 2)
//         {
//             return cast(T[R])[a0 + b0, a1 + b1];
//         }
//         else
//             return a0 + b0 + a1 + b1;
//     }
// }

// unittest
// {
//     import std.meta;

//     foreach(F; AliasSeq!(float, double))
//     foreach(N; AliasSeq!(1, 2, 4, 8, 16))
//     {
//         align(F[N].sizeof) F[N] a0 = 4;
//         align(F[N].sizeof) F[N] b0 = 30;
//         align(F[N].sizeof) F[N] a1 = 200;
//         align(F[N].sizeof) F[N] b1 = 1000;
//         align(F[N].sizeof) F[N][1] c1;
//         align(F[N].sizeof) F[N][2] c2;
//         align(F[N].sizeof) F[N][4] c4;
//         vectorize!(_test_fun!(1))(a0, b0, a1, b1, c1);
//         vectorize!(_test_fun!(2))(a0, b0, a1, b1, c2);
//         vectorize!(_test_fun!(4))(a0, b0, a1, b1, c4);
//     }
// }
