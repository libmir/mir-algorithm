/++
This module contains base statistical algorithms.

Note that used specialized summing algorithms execute more primitive operations
than vanilla summation. Therefore, if in certain cases maximum speed is required
at expense of precision, one can use $(REF_ALTTEXT $(TT Summation.fast), Summation.fast, mir, math, sum)$(NBSP).

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)

Authors: Shigeki Karita (original numir code), Ilia Ki, John Michael Hall

Copyright: 2020-3 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, math, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
+/
module mir.math.stat;

import core.lifetime: move;
import mir.internal.utility: isFloatingPoint;
import mir.math.common: fmamath;
import mir.math.sum;
import mir.ndslice.slice: Slice, SliceKind, hasAsSlice;
import mir.primitives;
import std.traits: Unqual, isArray, isMutable, isIterable, isIntegral, CommonType;

///
public import mir.math.sum: Summation;

///
package(mir)
template statType(T, bool checkComplex = true)
{
    import mir.internal.utility: isFloatingPoint;

    static if (isFloatingPoint!T) {
        import std.traits: Unqual;
        alias statType = Unqual!T;
    } else static if (is(T : double)) {
        alias statType = double;
    } else static if (checkComplex) {
        import mir.internal.utility: isComplex;
        static if (isComplex!T) {
            static if (__traits(getAliasThis, T).length == 1)
            {
                alias statType = .statType!(typeof(__traits(getMember, T, __traits(getAliasThis, T)[0]))); 
            }
            else
            {
                alias statType = Unqual!T;
            }
        } else {
            static assert(0, "statType: type " ~ T.stringof ~ " must be convertible to a complex floating point type");
        }
    } else {
        static assert(0, "statType: type " ~ T.stringof ~ " must be convertible to a floating point type");
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static assert(is(statType!int == double));
    static assert(is(statType!uint == double));
    static assert(is(statType!double == double));
    static assert(is(statType!float == float));
    static assert(is(statType!real == real));
    
    static assert(is(statType!(const(int)) == double));
    static assert(is(statType!(immutable(int)) == double));
    static assert(is(statType!(const(double)) == double));
    static assert(is(statType!(immutable(double)) == double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex: Complex;

    static assert(is(statType!(Complex!float) == Complex!float));
    static assert(is(statType!(Complex!double) == Complex!double));
    static assert(is(statType!(Complex!real) == Complex!real));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not float
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        Complex!float x;
        alias x this;
    }

    static assert(is(statType!Foo == Complex!float));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        double x;
        alias x this;
    }

    static assert(is(statType!Foo == double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        Complex!double x;
        alias x this;
    }

    static assert(is(statType!Foo == Complex!double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        real x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not real
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        Complex!real x;
        alias x this;
    }

    static assert(is(statType!Foo == Complex!real));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        int x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not ints
}

///
package(mir)
template meanType(T)
{
    import mir.math.sum: sumType;

    alias U = sumType!T;

    static if (__traits(compiles, {
        auto temp = U.init + U.init;
        auto a = temp / 2;
        temp += U.init;
    })) {
        alias V = typeof((U.init + U.init) / 2);
        alias meanType = statType!V;
    } else {
        static assert(0, "meanType: Can't calculate mean of elements of type " ~ U.stringof);
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static assert(is(meanType!(int[]) == double));
    static assert(is(meanType!(double[]) == double));
    static assert(is(meanType!(float[]) == float));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static assert(is(meanType!(Complex!float[]) == Complex!float));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }

    static assert(is(meanType!(Foo[]) == float));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        Complex!float x;
        alias x this;
    }

    static assert(is(meanType!(Foo[]) == Complex!float));
}

/++
Output range for mean.
+/
struct MeanAccumulator(T, Summation summation)
{
    ///
    size_t count;
    ///
    Summator!(T, summation) summator;

    ///
    F mean(F = T)() const @safe @property pure nothrow @nogc
    {
        return cast(F) summator.sum / cast(F) count;
    }
    
    ///
    F sum(F = T)() const @safe @property pure nothrow @nogc
    {
        return cast(F) summator.sum;
    }

    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        static if (hasShape!Range)
        {
            count += r.elementCount;
            summator.put(r);
        }
        else
        {
            foreach(x; r)
            {
                count++;
                summator.put(x);
            }
        }
    }

    ///
    void put()(T x)
    {
        count++;
        summator.put(x);
    }
    
    ///
    void put(F = T)(MeanAccumulator!(F, summation) m)
    {
        count += m.count;
        summator.put(cast(T) m.summator);
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    MeanAccumulator!(double, Summation.pairwise) x;
    x.put([0.0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    x.put(5);
    assert(x.mean == 2.5);
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    MeanAccumulator!(float, Summation.pairwise) x;
    x.put([0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    assert(x.sum == 10);
    x.put(5);
    assert(x.mean == 2.5);
}

version(mir_test)
@safe pure nothrow
unittest
{
    double[] x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25];
    double[] y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0];
    
    MeanAccumulator!(float, Summation.pairwise) m0;
    m0.put(x);
    MeanAccumulator!(float, Summation.pairwise) m1;
    m1.put(y);
    m0.put(m1);
    assert(m0.mean == 29.25 / 12);
}

/++
Computes the mean of the input.

By default, if `F` is not floating point type or complex type, then the result
will have a `double` type if `F` is implicitly convertible to a floating point 
type or a type for which `isComplex!F` is true.

Params:
    F = controls type of output
    summation = algorithm for calculating sums (default: Summation.appropriate)
Returns:
    The mean of all the elements in the input, must be floating point or complex type

See_also: 
    $(SUBREF sum, Summation)
+/
template mean(F, Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range, must be finite iterable
    +/
    @fmamath meanType!F mean(Range)(Range r)
        if (isIterable!Range)
    {
        alias G = typeof(return);
        MeanAccumulator!(G, ResolveSummationType!(summation, Range, G)) mean;
        mean.put(r.move);
        return mean.mean;
    }
    
    /++
    Params:
        ar = values
    +/
    @fmamath meanType!F mean(scope const F[] ar...)
    {
        alias G = typeof(return);
        MeanAccumulator!(G, ResolveSummationType!(summation, const(G)[], G)) mean;
        mean.put(ar);
        return mean.mean;
    }
}

/// ditto
template mean(Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range, must be finite iterable
    +/
    @fmamath meanType!Range mean(Range)(Range r)
        if (isIterable!Range)
    {
        alias F = typeof(return);
        return .mean!(F, summation)(r.move);
    }
    
    /++
    Params:
        ar = values
    +/
    @fmamath meanType!T mean(T)(scope const T[] ar...)
    {
        alias F = typeof(return);
        return .mean!(F, summation)(ar);
    }
}

/// ditto
template mean(F, string summation)
{
    mixin("alias mean = .mean!(F, Summation." ~ summation ~ ");");
}

/// ditto
template mean(string summation)
{
    mixin("alias mean = .mean!(Summation." ~ summation ~ ");");
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.complex;
    alias C = Complex!double;

    assert(mean([1.0, 2, 3]) == 2);
    assert(mean([C(1, 3), C(2), C(3)]) == C(2, 1));
    
    assert(mean!float([0, 1, 2, 3, 4, 5].sliced(3, 2)) == 2.5);
    
    static assert(is(typeof(mean!float([1, 2, 3])) == float));
}

/// Mean of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    assert(x.mean == 29.25 / 12);
}

/// Mean of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;

    auto x = [
        [0.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 0.0]
    ].fuse;

    assert(x.mean == 29.25 / 12);
}

/// Column mean of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    auto x = [
        [0.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 0.0]
    ].fuse;
    auto result = [1, 4.25, 3.25, 1.5, 2.5, 2.125];

    // Use byDim or alongDim with map to compute mean of row/column.
    assert(x.byDim!1.map!mean.all!approxEqual(result));
    assert(x.alongDim!0.map!mean.all!approxEqual(result));

    // FIXME
    // Without using map, computes the mean of the whole slice
    // assert(x.byDim!1.mean == x.sliced.mean);
    // assert(x.alongDim!0.mean == x.sliced.mean);
}

/// Can also set algorithm or output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;

    //Set sum algorithm or output type

    auto a = [1, 1e100, 1, -1e100].sliced;

    auto x = a * 10_000;

    assert(x.mean!"kbn" == 20_000 / 4);
    assert(x.mean!"kb2" == 20_000 / 4);
    assert(x.mean!"precise" == 20_000 / 4);
    assert(x.mean!(double, "precise") == 20_000.0 / 4);

    auto y = uint.max.repeat(3);
    assert(y.mean!ulong == 12884901885 / 3);
}

/++
For integral slices, pass output type as template parameter to ensure output
type is correct.
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0, 1, 1, 2, 4, 4,
              2, 7, 5, 1, 2, 0].sliced;

    auto y = x.mean;
    assert(y.approxEqual(29.0 / 12, 1.0e-10));
    static assert(is(typeof(y) == double));

    assert(x.mean!float.approxEqual(29f / 12, 1.0e-10));
}

/++
Mean works for complex numbers and other user-defined types (provided they
can be converted to a floating point or complex type)
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.complex.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.complex;
    alias C = Complex!double;

    auto x = [C(1.0, 2), C(2, 3), C(3, 4), C(4, 5)].sliced;
    assert(x.mean.approxEqual(C(2.5, 3.5)));
}

/// Compute mean tensors along specified dimention of tensors
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice: alongDim, iota, as, map;
    /++
      [[0,1,2],
       [3,4,5]]
     +/
    auto x = iota(2, 3).as!double;
    assert(x.mean == (5.0 / 2.0));

    auto m0 = [(0.0+3.0)/2.0, (1.0+4.0)/2.0, (2.0+5.0)/2.0];
    assert(x.alongDim!0.map!mean == m0);
    assert(x.alongDim!(-2).map!mean == m0);

    auto m1 = [(0.0+1.0+2.0)/3.0, (3.0+4.0+5.0)/3.0];
    assert(x.alongDim!1.map!mean == m1);
    assert(x.alongDim!(-1).map!mean == m1);

    assert(iota(2, 3, 4, 5).as!double.alongDim!0.map!mean == iota([3, 4, 5], 3 * 4 * 5 / 2));
}

/// Arbitrary mean
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    assert(mean(1.0, 2, 3) == 2);
    assert(mean!float(1, 2, 3) == 2);
}

version(mir_test)
@safe pure nothrow
unittest
{
    assert([1.0, 2, 3, 4].mean == 2.5);
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.topology: iota, alongDim, map;

    auto x = iota([2, 2], 1);
    auto y = x.alongDim!1.map!mean;
    assert(y.all!approxEqual([1.5, 3.5]));
    static assert(is(meanType!(typeof(y)) == double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    assert(x.sliced.mean == 29.25 / 12);
    assert(x.sliced.mean!float == 29.25 / 12);
}

///
package(mir)
template hmeanType(T)
{
    import mir.math.sum: sumType;
    
    alias U = sumType!T;

    static if (__traits(compiles, {
        U t = U.init + cast(U) 1; //added for when U.init = 0
        auto temp = cast(U) 1 / t + cast(U) 1 / t;
    })) {
        alias V = typeof(cast(U) 1 / ((cast(U) 1 / U.init + cast(U) 1 / U.init) / cast(U) 2));
        alias hmeanType = statType!V;
    } else {
        static assert(0, "hmeanType: Can't calculate hmean of elements of type " ~ U.stringof);
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static assert(is(hmeanType!(int[]) == double));
    static assert(is(hmeanType!(double[]) == double));
    static assert(is(hmeanType!(float[]) == float)); 
    static assert(is(hmeanType!(Complex!float[]) == Complex!float));    
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        float x;
        alias x this;
    }
    
    static struct Bar {
        Complex!float x;
        alias x this;
    }

    static assert(is(hmeanType!(Foo[]) == float));
    static assert(is(hmeanType!(Bar[]) == Complex!float));
}

/++
Computes the harmonic mean of the input.

By default, if `F` is not floating point type or complex type, then the result
will have a `double` type if `F` is implicitly convertible to a floating point 
type or a type for which `isComplex!F` is true.

Params:
    F = controls type of output
    summation = algorithm for calculating sums (default: Summation.appropriate)
Returns:
    harmonic mean of all the elements of the input, must be floating point or complex type

See_also: 
    $(SUBREF sum, Summation)
+/
template hmean(F, Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    +/
    @fmamath hmeanType!F hmean(Range)(Range r)
        if (isIterable!Range)
    {
        import mir.ndslice.topology: map;

        alias G = typeof(return);
        auto numerator = cast(G) 1;

        static if (summation == Summation.fast && __traits(compiles, r.move.map!"numerator / a"))
        {
            return numerator / r.move.map!"numerator / a".mean!(G, summation);
        }
        else
        {
            MeanAccumulator!(G, ResolveSummationType!(summation, Range, G)) imean;
            foreach (e; r)
                imean.put(numerator / e);
            return numerator / imean.mean;
        }
    }
   
    /++
    Params:
        ar = values
    +/
    @fmamath hmeanType!F hmean(scope const F[] ar...)
    {
        alias G = typeof(return);

        auto numerator = cast(G) 1;

        static if (summation == Summation.fast && __traits(compiles, ar.map!"numerator / a"))
        {
            return numerator / ar.map!"numerator / a".mean!(G, summation);
        }
        else
        {
            MeanAccumulator!(G, ResolveSummationType!(summation, const(G)[], G)) imean;
            foreach (e; ar)
                imean.put(numerator / e);
            return numerator / imean.mean;
        }
    }
}

/// ditto
template hmean(Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    +/
    @fmamath hmeanType!Range hmean(Range)(Range r)
        if (isIterable!Range)
    {
        alias F = typeof(return);
        return .hmean!(F, summation)(r.move);
    }
    
    /++
    Params:
        ar = values
    +/
    @fmamath hmeanType!T hmean(T)(scope const T[] ar...)
    {
        alias F = typeof(return);
        return .hmean!(F, summation)(ar);
    }
}

/// ditto
template hmean(F, string summation)
{
    mixin("alias hmean = .hmean!(F, Summation." ~ summation ~ ");");
}

/// ditto
template hmean(string summation)
{
    mixin("alias hmean = .hmean!(Summation." ~ summation ~ ");");
}

/// Harmonic mean of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [20.0, 100.0, 2000.0, 10.0, 5.0, 2.0].sliced;

    assert(x.hmean.approxEqual(6.97269));
}

/// Harmonic mean of matrix
version(mir_test)
pure @safe
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;

    auto x = [
        [20.0, 100.0, 2000.0], 
        [10.0, 5.0, 2.0]
    ].fuse;

    assert(x.hmean.approxEqual(6.97269));
}

/// Column harmonic mean of matrix
version(mir_test)
pure @safe
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;

    auto x = [
        [20.0, 100.0, 2000.0],
        [ 10.0, 5.0, 2.0]
    ].fuse;

    auto y = [13.33333, 9.52381, 3.996004];

    // Use byDim or alongDim with map to compute mean of row/column.
    assert(x.byDim!1.map!hmean.all!approxEqual(y));
    assert(x.alongDim!0.map!hmean.all!approxEqual(y));
}

/// Can also pass arguments to hmean
version(mir_test)
pure @safe nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.topology: repeat;
    import mir.ndslice.slice: sliced;

    //Set sum algorithm or output type
    auto x = [1, 1e-100, 1, -1e-100].sliced;

    assert(x.hmean!"kb2".approxEqual(2));
    assert(x.hmean!"precise".approxEqual(2));
    assert(x.hmean!(double, "precise").approxEqual(2));

    //Provide the summation type
    assert(float.max.repeat(3).hmean!double.approxEqual(float.max));
}

/++
For integral slices, pass output type as template parameter to ensure output
type is correct. 
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [20, 100, 2000, 10, 5, 2].sliced;

    auto y = x.hmean;

    assert(y.approxEqual(6.97269));
    static assert(is(typeof(y) == double));

    assert(x.hmean!float.approxEqual(6.97269));
}

/++
hmean works for complex numbers and other user-defined types (provided they
can be converted to a floating point or complex type)
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.complex.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.complex;
    alias C = Complex!double;

    auto x = [C(1, 2), C(2, 3), C(3, 4), C(4, 5)].sliced;
    assert(x.hmean.approxEqual(C(1.97110904, 3.14849332)));
}

/// Arbitrary harmonic mean
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = hmean(20.0, 100, 2000, 10, 5, 2);
    assert(x.approxEqual(6.97269));
    
    auto y = hmean!float(20, 100, 2000, 10, 5, 2);
    assert(y.approxEqual(6.97269));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    static immutable x = [20.0, 100.0, 2000.0, 10.0, 5.0, 2.0];

    assert(x.sliced.hmean.approxEqual(6.97269));
    assert(x.sliced.hmean!float.approxEqual(6.97269));
}

private
F nthroot(F)(in F x, in size_t n)
    if (isFloatingPoint!F)
{
    import mir.math.common: sqrt, pow;

    if (n > 2) {
        return pow(x, cast(F) 1 / cast(F) n);
    } else if (n == 2) {
        return sqrt(x);
    } else if (n == 1) {
        return x;
    } else {
        return cast(F) 1;
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;

    assert(nthroot(9.0, 0).approxEqual(1));
    assert(nthroot(9.0, 1).approxEqual(9));
    assert(nthroot(9.0, 2).approxEqual(3));
    assert(nthroot(9.5, 2).approxEqual(3.08220700));
    assert(nthroot(9.0, 3).approxEqual(2.08008382));
}

/++
Output range for gmean.
+/
struct GMeanAccumulator(T) 
    if (isMutable!T && isFloatingPoint!T)
{
    import mir.math.numeric: ProdAccumulator;

    ///
    size_t count;
    ///
    ProdAccumulator!T prodAccumulator;

    ///
    F gmean(F = T)() const @property
        if (isFloatingPoint!F)
    {
        import mir.math.common: exp2;

        return nthroot(cast(F) prodAccumulator.mantissa, count) * exp2(cast(F) prodAccumulator.exp / count);
    }

    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        static if (hasShape!Range)
        {
            count += r.elementCount;
            prodAccumulator.put(r);
        }
        else
        {
            foreach(x; r)
            {
                count++;
                prodAccumulator.put(x);
            }
        }
    }

    ///
    void put()(T x)
    {
        count++;
        prodAccumulator.put(x);
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    GMeanAccumulator!double x;
    x.put([1.0, 2, 3, 4].sliced);
    assert(x.gmean.approxEqual(2.21336384));
    x.put(5);
    assert(x.gmean.approxEqual(2.60517108));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    GMeanAccumulator!float x;
    x.put([1, 2, 3, 4].sliced);
    assert(x.gmean.approxEqual(2.21336384));
    x.put(5);
    assert(x.gmean.approxEqual(2.60517108));
}

///
package(mir)
template gmeanType(T)
{
    import mir.math.numeric: prodType;
    
    alias U = prodType!T;

    static if (__traits(compiles, {
        auto temp = U.init * U.init;
        auto a = nthroot(temp, 2);
        temp *= U.init;
    })) {
        alias V = typeof(nthroot(U.init * U.init, 2));
        alias gmeanType = statType!(V, false);
    } else {
        static assert(0, "gmeanType: Can't calculate gmean of elements of type " ~ U.stringof);
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static assert(is(gmeanType!int == double));
    static assert(is(gmeanType!double == double));
    static assert(is(gmeanType!float == float));
    static assert(is(gmeanType!(int[]) == double));
    static assert(is(gmeanType!(double[]) == double));
    static assert(is(gmeanType!(float[]) == float));    
}

/++
Computes the geometric average of the input.

By default, if `F` is not floating point type, then the result will have a 
`double` type if `F` is implicitly convertible to a floating point type.

Params:
    r = range, must be finite iterable
Returns:
    The geometric average of all the elements in the input, must be floating point type

See_also: 
    $(SUBREF numeric, prod)
+/
@fmamath gmeanType!F gmean(F, Range)(Range r)
    if (isFloatingPoint!F && isIterable!Range)
{
    alias G = typeof(return);
    GMeanAccumulator!G gmean;
    gmean.put(r.move);
    return gmean.gmean;
}
    
/// ditto
@fmamath gmeanType!Range gmean(Range)(Range r)
    if (isIterable!Range)
{
    alias G = typeof(return);
    return .gmean!(G, Range)(r.move);
}

/++
Params:
    ar = values
+/
@fmamath gmeanType!F gmean(F)(scope const F[] ar...)
    if (isFloatingPoint!F)
{
    alias G = typeof(return);
    GMeanAccumulator!G gmean;
    gmean.put(ar);
    return gmean.gmean;
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    assert(gmean([1.0, 2, 3]).approxEqual(1.81712059));
    
    assert(gmean!float([1, 2, 3, 4, 5, 6].sliced(3, 2)).approxEqual(2.99379516));
    
    static assert(is(typeof(gmean!float([1, 2, 3])) == float));
}

/// Geometric mean of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [3.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 2.0].sliced;

    assert(x.gmean.approxEqual(2.36178395));
}

/// Geometric mean of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;

    auto x = [
        [3.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 2.0]
    ].fuse;

    assert(x.gmean.approxEqual(2.36178395));
}

/// Column gmean of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;

    auto x = [
        [3.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 2.0]
    ].fuse;
    auto result = [2.44948974, 2.73861278, 2.73861278, 1.41421356, 2.29128784, 2.91547594];

    // Use byDim or alongDim with map to compute mean of row/column.
    assert(x.byDim!1.map!gmean.all!approxEqual(result));
    assert(x.alongDim!0.map!gmean.all!approxEqual(result));

    // FIXME
    // Without using map, computes the mean of the whole slice
    // assert(x.byDim!1.gmean.all!approxEqual(result));
    // assert(x.alongDim!0.gmean.all!approxEqual(result));
}

/// Can also set output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;

    auto x = [5120.0, 7340032, 32, 3758096384].sliced;

    assert(x.gmean!float.approxEqual(259281.45295212));

    auto y = uint.max.repeat(2);
    assert(y.gmean!float.approxEqual(cast(float) uint.max));
}

/++
For integral slices, pass output type as template parameter to ensure output
type is correct.
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [5, 1, 1, 2, 4, 4,
              2, 7, 5, 1, 2, 10].sliced;

    auto y = x.gmean;
    static assert(is(typeof(y) == double));
    
    assert(x.gmean!float.approxEqual(2.79160522));
}

/// gean works for user-defined types, provided the nth root can be taken for them
version(mir_test)
@safe pure nothrow
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }

    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [Foo(1.0), Foo(2.0), Foo(3.0)].sliced;
    assert(x.gmean.approxEqual(1.81712059));
}

/// Compute gmean tensors along specified dimention of tensors
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, iota, map;
    
    auto x = [
        [1.0, 2, 3],
        [4.0, 5, 6]
    ].fuse;

    assert(x.gmean.approxEqual(2.99379516));

    auto result0 = [2.0, 3.16227766, 4.24264069];
    assert(x.alongDim!0.map!gmean.all!approxEqual(result0));
    assert(x.alongDim!(-2).map!gmean.all!approxEqual(result0));

    auto result1 = [1.81712059, 4.93242414];
    assert(x.alongDim!1.map!gmean.all!approxEqual(result1));
    assert(x.alongDim!(-1).map!gmean.all!approxEqual(result1));

    auto y = [
        [
            [1.0, 2, 3],
            [4.0, 5, 6]
        ], [
            [7.0, 8, 9],
            [10.0, 9, 10]
        ]
    ].fuse;
    
    auto result3 = [
        [2.64575131, 4.0,        5.19615242],
        [6.32455532, 6.70820393, 7.74596669]
    ];
    assert(y.alongDim!0.map!gmean.all!approxEqual(result3));
}

/// Arbitrary gmean
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;

    assert(gmean(1.0, 2, 3).approxEqual(1.81712059));
    assert(gmean!float(1, 2, 3).approxEqual(1.81712059));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;

    assert([1.0, 2, 3, 4].gmean.approxEqual(2.21336384));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;

    assert(gmean([1, 2, 3]).approxEqual(1.81712059));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    static immutable x = [3.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 2.0];

    assert(x.sliced.gmean.approxEqual(2.36178395));
    assert(x.sliced.gmean!float.approxEqual(2.36178395));
}

/++
Computes the median of `slice`.

By default, if `F` is not floating point type or complex type, then the result
will have a `double` type if `F` is implicitly convertible to a floating point 
type or a type for which `isComplex!F` is true.

Can also pass a boolean variable, `allowModify`, that allows the input slice to
be modified. By default, a reference-counted copy is made. 

Params:
    F = output type
    allowModify = Allows the input slice to be modified, default is false
Returns:
    the median of the slice

See_also: 
    $(SUBREF stat, mean)
+/
template median(F, bool allowModify = false)
{
    /++
    Params:
        slice = slice
    +/
    @nogc
    meanType!F median(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        static assert (!allowModify ||
                       isMutable!(slice.DeepElement),
                           "allowModify must be false or the input must be mutable");
        alias G = typeof(return);
        size_t len = slice.elementCount;
        assert(len > 0, "median: slice must have length greater than zero");

        import mir.ndslice.topology: as, flattened;

        static if (!allowModify) {
            import mir.ndslice.allocation: rcslice;
            
            if (len > 2) {
                auto view = slice.lightScope;
                auto val = view.as!(Unqual!(slice.DeepElement)).rcslice;
                auto temp = val.lightScope.flattened;
                return .median!(G, true)(temp);
            } else {
                return mean!G(slice);
            }
        } else {
            import mir.ndslice.sorting: partitionAt;
            
            auto temp = slice.flattened;

            if (len > 5) {
                size_t half_n = len / 2;
                partitionAt(temp, half_n);
                if (len % 2 == 1) {
                    return cast(G) temp[half_n];
                } else {
                    //move largest value in first half of slice to half_n - 1
                    partitionAt(temp[0 .. half_n], half_n - 1);
                    return (temp[half_n - 1] + temp[half_n]) / cast(G) 2;
                }
            } else {
                return smallMedianImpl!(G)(temp);
            }
        }
    }
}

/// ditto
template median(bool allowModify = false)
{
    /// ditto
    meanType!(Slice!(Iterator, N, kind))
        median(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        static assert (!allowModify ||
                       isMutable!(DeepElementType!(Slice!(Iterator, N, kind))),
                           "allowModify must be false or the input must be mutable");
        alias F = typeof(return);
        return .median!(F, allowModify)(slice.move);
    }
}

/++
Params:
    ar = array
+/
meanType!(T[]) median(T)(scope const T[] ar...)
{
    import mir.ndslice.slice: sliced;

    alias F = typeof(return);
    return median!(F, false)(ar.sliced);
}

/++
Params:
    withAsSlice = input that satisfies hasAsSlice
+/
auto median(T)(T withAsSlice)
    if (hasAsSlice!T)
{
    return median(withAsSlice.asSlice);
}

/// Median of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    auto x0 = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10, 5].sliced;
    assert(x0.median == 5);

    auto x1 = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10].sliced;
    assert(x1.median == 5);
}

/// Median of dynamic array
version(mir_test)
@safe pure nothrow
unittest
{
    auto x0 = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10, 5];
    assert(x0.median == 5);

    auto x1 = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10];
    assert(x1.median == 5);
}

/// Median of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;

    auto x0 = [
        [9.0, 1, 0, 2,  3], 
        [4.0, 6, 8, 7, 10]
    ].fuse;

    assert(x0.median == 5);
}

/// Row median of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: alongDim, byDim, map;

    auto x = [
        [0.0, 1.0, 1.5, 2.0, 3.5, 4.25], 
        [2.0, 7.5, 5.0, 1.0, 1.5, 0.0]
    ].fuse;

    auto result = [1.75, 1.75].sliced;

    // Use byDim or alongDim with map to compute median of row/column.
    assert(x.byDim!0.map!median.all!approxEqual(result));
    assert(x.alongDim!1.map!median.all!approxEqual(result));
}

/// Can allow original slice to be modified or set output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    auto x0 = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10, 5].sliced;
    assert(x0.median!true == 5);
    
    auto x1 = [9, 1, 0, 2, 3, 4, 6, 8, 7, 10].sliced;
    assert(x1.median!(float, true) == 5);
}

/// Arbitrary median
version(mir_test)
@safe pure nothrow
unittest
{
    assert(median(0, 1, 2, 3, 4) == 2);
}

// @nogc test
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable x = [9.0, 1, 0, 2, 3];
    assert(x.sliced.median == 2);
}

// withAsSlice test
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    import mir.rc.array: RCArray;

    static immutable a = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10, 5];

    auto x = RCArray!double(11);
    foreach(i, ref e; x)
        e = a[i];

    assert(x.median.approxEqual(5));
}

/++
For integral slices, can pass output type as template parameter to ensure output
type is correct
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    auto x = [9, 1, 0, 2, 3, 4, 6, 8, 7, 10].sliced;
    assert(x.median!float == 5f);

    auto y = x.median;
    assert(y == 5.0);
    static assert(is(typeof(y) == double));
}

// additional logic tests
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [3, 3, 2, 0, 2, 0].sliced;
    assert(x.median!float.approxEqual(2));

    x[] = [2, 2, 4, 0, 4, 3];
    assert(x.median!float.approxEqual(2.5));
    x[] = [1, 4, 5, 4, 4, 3];
    assert(x.median!float.approxEqual(4));
    x[] = [1, 5, 3, 5, 2, 2];
    assert(x.median!float.approxEqual(2.5));
    x[] = [4, 3, 2, 1, 4, 5];
    assert(x.median!float.approxEqual(3.5));
    x[] = [4, 5, 3, 5, 5, 4];
    assert(x.median!float.approxEqual(4.5));
    x[] = [3, 3, 3, 0, 0, 1];
    assert(x.median!float.approxEqual(2));
    x[] = [4, 2, 2, 1, 2, 5];
    assert(x.median!float.approxEqual(2));
    x[] = [2, 3, 1, 4, 5, 5];
    assert(x.median!float.approxEqual(3.5));
    x[] = [1, 1, 4, 5, 5, 5];
    assert(x.median!float.approxEqual(4.5));
    x[] = [2, 4, 0, 5, 1, 0];
    assert(x.median!float.approxEqual(1.5));
    x[] = [3, 5, 2, 5, 4, 2];
    assert(x.median!float.approxEqual(3.5));
    x[] = [3, 5, 4, 1, 4, 3];
    assert(x.median!float.approxEqual(3.5));
    x[] = [4, 2, 0, 3, 1, 3];
    assert(x.median!float.approxEqual(2.5));
    x[] = [100, 4, 5, 0, 5, 1];
    assert(x.median!float.approxEqual(4.5));
    x[] = [100, 5, 4, 0, 5, 1];
    assert(x.median!float.approxEqual(4.5));
    x[] = [100, 5, 4, 0, 1, 5];
    assert(x.median!float.approxEqual(4.5));
    x[] = [4, 5, 100, 1, 5, 0];
    assert(x.median!float.approxEqual(4.5));
    x[] = [0, 1, 2, 2, 3, 4];
    assert(x.median!float.approxEqual(2));
    x[] = [0, 2, 2, 3, 4, 5];
    assert(x.median!float.approxEqual(2.5));
}

// smallMedianImpl tests
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x0 = [9.0, 1, 0, 2, 3].sliced;
    assert(x0.median.approxEqual(2));

    auto x1 = [9.0, 1, 0, 2].sliced;
    assert(x1.median.approxEqual(1.5));
    
    auto x2 = [9.0, 0, 1].sliced;
    assert(x2.median.approxEqual(1));
    
    auto x3 = [1.0, 0].sliced;
    assert(x3.median.approxEqual(0.5));
    
    auto x4 = [1.0].sliced;
    assert(x4.median.approxEqual(1));
}

// Check issue #328 fixed
version(mir_test)
@safe pure nothrow
unittest {
    import mir.ndslice.topology: iota;

    auto x = iota(18);
    auto y = median(x);
    assert(y == 8.5);
}

private pure @trusted nothrow @nogc
F smallMedianImpl(F, Iterator)(Slice!Iterator slice) 
{
    size_t n = slice.elementCount;

    assert(n > 0, "smallMedianImpl: slice must have elementCount greater than 0");
    assert(n <= 5, "smallMedianImpl: slice must have elementCount of 5 or less");

    import mir.functional: naryFun;
    import mir.ndslice.sorting: medianOf;
    import mir.utility: swapStars;

    auto sliceI0 = slice._iterator;
    
    if (n == 1) {
        return cast(F) *sliceI0;
    }

    auto sliceI1 = sliceI0;
    ++sliceI1;

    if (n > 2) {
        auto sliceI2 = sliceI1;
        ++sliceI2;
        alias less = naryFun!("a < b");

        if (n == 3) {
            medianOf!less(sliceI0, sliceI1, sliceI2);
            return cast(F) *sliceI1;
        } else {
            auto sliceI3 = sliceI2;
            ++sliceI3;
            if (n == 4) {
                // Put min in slice[0], lower median in slice[1]
                medianOf!less(sliceI0, sliceI1, sliceI2, sliceI3);
                // Ensure slice[2] < slice[3]
                medianOf!less(sliceI2, sliceI3);
                return cast(F) (*sliceI1 + *sliceI2) / cast(F) 2;
            } else {
                auto sliceI4 = sliceI3;
                ++sliceI4;
                medianOf!less(sliceI0, sliceI1, sliceI2, sliceI3, sliceI4);
                return cast(F) *sliceI2;
            }
        }
    } else {
        return cast(F) (*sliceI0 + *sliceI1) / cast(F) 2;
    }
}

// smallMedianImpl tests
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x0 = [9.0, 1, 0, 2, 3].sliced;
    assert(x0.smallMedianImpl!double.approxEqual(2));

    auto x1 = [9.0, 1, 0, 2].sliced;
    assert(x1.smallMedianImpl!double.approxEqual(1.5));

    auto x2 = [9.0, 0, 1].sliced;
    assert(x2.smallMedianImpl!double.approxEqual(1));

    auto x3 = [1.0, 0].sliced;
    assert(x3.smallMedianImpl!double.approxEqual(0.5));

    auto x4 = [1.0].sliced;
    assert(x4.smallMedianImpl!double.approxEqual(1));

    auto x5 = [2.0, 1, 0, 9].sliced;
    assert(x5.smallMedianImpl!double.approxEqual(1.5));

    auto x6 = [1.0, 2, 0, 9].sliced;
    assert(x6.smallMedianImpl!double.approxEqual(1.5));

    auto x7 = [1.0, 0, 9, 2].sliced;
    assert(x7.smallMedianImpl!double.approxEqual(1.5));
}

/++
Centers `slice`, which must be a finite iterable.

By default, `slice` is centered by the mean. A custom function may also be
provided using `centralTendency`.

Returns:
    The elements in the slice with the average subtracted from them.
+/
template center(alias centralTendency = mean!(Summation.appropriate))
{
    import mir.ndslice.slice: isConvertibleToSlice, isSlice, Slice, SliceKind;
    /++
    Params:
        slice = slice
    +/
    auto center(Iterator, size_t N, SliceKind kind)(
        Slice!(Iterator, N, kind) slice)
    {
        import core.lifetime: move;
        import mir.ndslice.internal: LeftOp, ImplicitlyUnqual;
        import mir.ndslice.topology: vmap;

        auto m = centralTendency(slice.lightScope);
        alias T = typeof(m);
        return slice.move.vmap(LeftOp!("-", ImplicitlyUnqual!T)(m));
    }
    
    /// ditto
    auto center(T)(T x)
        if (isConvertibleToSlice!T && !isSlice!T)
    {
        import mir.ndslice.slice: toSlice;
        return center(x.toSlice);
    }
}

/// Center vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;
    assert(x.center.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    
    // Can center using different functions
    assert(x.center!hmean.all!approxEqual([-1.44898, -0.44898, 0.55102, 1.55102, 2.55102, 3.55102]));
    assert(x.center!gmean.all!approxEqual([-1.99379516, -0.99379516, 0.00620483, 1.00620483, 2.00620483, 3.00620483]));
    assert(x.center!median.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));

    // center operates lazily, if original slice is changed, then 
    auto y = x.center;
    assert(y.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    x[0]++;
    assert(y.all!approxEqual([-1.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
}

/// Example of lazy behavior of center
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice: sliced;

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;
    auto y = x.center;
    auto z = x.center.slice;
    assert(y.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    x[0]++;
    // y changes, while z does not
    assert(y.all!approxEqual([-1.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(z.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));   
}

/// Center dynamic array
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    auto x = [1.0, 2, 3, 4, 5, 6];
    assert(x.center.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
}

/// Center matrix
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice: fuse;
    
    auto x = [
        [0.0, 1, 2], 
        [3.0, 4, 5]
    ].fuse;
    
    auto y = [
        [-2.5, -1.5, -0.5], 
        [ 0.5,  1.5,  2.5]
    ].fuse;
    
    assert(x.center.all!approxEqual(y));
}

/// Column center matrix
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all, equal;
    import mir.math.common: approxEqual;
    import mir.ndslice: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;

    auto x = [
        [20.0, 100.0, 2000.0],
        [10.0,   5.0,    2.0]
    ].fuse;

    auto result = [
        [ 5.0,  47.5,  999],
        [-5.0, -47.5, -999]
    ].fuse;

    // Use byDim with map to compute average of row/column.
    auto xCenterByDim = x.byDim!1.map!center;
    auto resultByDim = result.byDim!1;
    assert(xCenterByDim.equal!(equal!approxEqual)(resultByDim));

    auto xCenterAlongDim = x.alongDim!0.map!center;
    auto resultAlongDim = result.alongDim!0;
    assert(xCenterByDim.equal!(equal!approxEqual)(resultAlongDim));
}

/// Can also pass arguments to average function used by center
version(mir_test)
pure @safe nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    //Set sum algorithm or output type
    auto a = [1, 1e100, 1, -1e100];

    auto x = a.sliced * 10_000;

    //Due to Floating Point precision, subtracting the mean from the second
    //and fourth numbers in `x` does not change the value of the result
    auto result = [5000, 1e104, 5000, -1e104].sliced;

    assert(x.center!(mean!"kbn") == result);
    assert(x.center!(mean!"kb2") == result);
    assert(x.center!(mean!"precise") == result);
}

/++
Passing a centered input to `variance` or `standardDeviation` with the
`assumeZeroMean` algorithm is equivalent to calculating `variance` or
`standardDeviation` on the original input.
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;
    assert(x.center.variance!"assumeZeroMean".approxEqual(x.variance));
    assert(x.center.standardDeviation!"assumeZeroMean".approxEqual(x.standardDeviation));
}

// dynamic array test
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    double[] x = [1.0, 2, 3, 4, 5, 6];

    assert(x.center.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
}

// withAsSlice test
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.rc.array: RCArray;

    static immutable a = [1.0, 2, 3, 4, 5, 6];
    static immutable result = [-2.5, -1.5, -0.5, 0.5, 1.5, 2.5];

    auto x = RCArray!double(6);
    foreach(i, ref e; x)
        e = a[i];

    assert(x.center.all!approxEqual(result));
}

/++
Output range that applies function `fun` to each input before summing
+/
struct MapSummator(alias fun, T, Summation summation) 
    if(isMutable!T)
{
    ///
    Summator!(T, summation) summator;

    ///
    F sum(F = T)() const @property
    {
        return cast(F) summator.sum;
    }
    
    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        import mir.ndslice.topology: map;
        summator.put(r.map!fun);
    }

    ///
    void put()(T x)
    {
        summator.put(fun(x));
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: powi;
    import mir.ndslice.slice: sliced;

    alias f = (double x) => (powi(x, 2));
    MapSummator!(f, double, Summation.pairwise) x;
    x.put([0.0, 1, 2, 3, 4].sliced);
    assert(x.sum == 30.0);
    x.put(5);
    assert(x.sum == 55.0);
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    alias f = (double x) => (x + 1);
    MapSummator!(f, double, Summation.pairwise) x;
    x.put([0.0, 1, 2, 3, 4].sliced);
    assert(x.sum == 15.0);
    x.put(5);
    assert(x.sum == 21.0);
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.ndslice.slice: sliced;

    alias f = (double x) => (x + 1);
    MapSummator!(f, double, Summation.pairwise) x;
    static immutable a = [0.0, 1, 2, 3, 4];
    x.put(a.sliced);
    assert(x.sum == 15.0);
    x.put(5);
    assert(x.sum == 21.0);
}

version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.slice: sliced;

    alias f = (double x) => (x + 1);
    MapSummator!(f, double, Summation.pairwise) x;
    auto a = [
        [0.0, 1, 2],
        [3.0, 4, 5]
    ].fuse;
    auto b = [6.0, 7, 8].sliced;
    x.put(a);
    assert(x.sum == 21.0);
    x.put(b);
    assert(x.sum == 45.0);
}

/++
Variance algorithms.

See Also:
    $(WEB en.wikipedia.org/wiki/Algorithms_for_calculating_variance, Algorithms for calculating variance).
+/
enum VarianceAlgo
{
    /++
    Performs Welford's online algorithm for updating variance. Can also `put`
    another VarianceAccumulator of different types, which uses the parallel
    algorithm from Chan et al., described above.
    +/
    online,
    
    /++
    Calculates variance using E(x^^2) - E(x)^2 (alowing for adjustments for 
    population/sample variance). This algorithm can be numerically unstable. As
    in: 
    (E(x ^^ 2) - E(x) ^^ 2
    +/
    naive,

    /++
    Calculates variance using a two-pass algorithm whereby the input is first 
    centered and then the sum of squares is calculated from that. As in:
    E((x - E(x)) ^^ 2)
    +/
    twoPass,

    /++
    Calculates variance assuming the mean of the dataseries is zero. 
    +/
    assumeZeroMean,
    
    /++
    When slices, slice-like objects, or ranges are the inputs, uses the two-pass
    algorithm. When an individual data-point is added, uses the online algorithm.
    +/
    hybrid
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.naive)
{
    import mir.math.sum: Summator;

    ///
    private MeanAccumulator!(T, summation) meanAccumulator;

    ///
    private Summator!(T, summation) summatorOfSquares;

    ///
    this(Range)(Range r)
        if (isIterable!Range)
    {
        import core.lifetime: move;
        this.put(r.move);
    }

    ///
    this()(T x)
    {
        this.put(x);
    }


    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        foreach(x; r)
        {
            this.put(x);
        }
    }

    ///
    void put()(T x)
    {
        meanAccumulator.put(x);
        summatorOfSquares.put(x * x);
    }

    ///
    void put(U, Summation sumAlgo)(VarianceAccumulator!(U, varianceAlgo, sumAlgo) v)
    {
        meanAccumulator.put(v.meanAccumulator);
        summatorOfSquares.put(v.sumOfSquares!T);
    }

const:

    ///
    size_t count() @property
    {
        return meanAccumulator.count;
    }
    ///
    F mean(F = T)() const @property
    {
        return meanAccumulator.mean!F;
    }
    ///
    F sumOfSquares(F = T)()
    {
        return cast(F) summatorOfSquares.sum;
    }
    ///
    F centeredSumOfSquares(F = T)()
    {
        return sumOfSquares!F - count * mean!F * mean!F;
    }
    ///
    F variance(F = T)(bool isPopulation) @property
    in
    {
        assert(count > 1, "VarianceAccumulator.varaince: count must be larger than one");
    }
    do
    {
        return sumOfSquares!F / (count + isPopulation - 1) - 
            mean!F * mean!F * count / (count + isPopulation - 1);
    }
}

/// naive
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(true).approxEqual(57.01923 / 13));
    assert(v.variance(false).approxEqual(57.01923 / 12));
}

// Can put VarianceAccumulator
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.test: shouldApprox;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive) v;
    v.put(x);
    VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive) w;
    w.put(y);
    v.put(w);
    v.variance(true).shouldApprox == 54.76562 / 12;
}

// Test input range
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.sum: Summation;
    import mir.test: should;
    import std.range: iota;
    import std.algorithm: map;

    auto x1 = iota(0, 5);
    auto v1 = VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive)(x1);
    v1.variance(true).should == 2;
    v1.centeredSumOfSquares.should == 10;
    auto x2 = x1.map!(a => 2 * a);
    auto v2 = VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive)(x2);
    v2.variance(true).should == 8;
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.online)
{
    import mir.math.sum: Summator;

    ///
    private MeanAccumulator!(T, summation) meanAccumulator;

    ///
    private Summator!(T, summation) centeredSummatorOfSquares;

    ///
    this(Range)(Range r)
        if (isIterable!Range)
    {
        import core.lifetime: move;
        this.put(r.move);
    }

    ///
    this()(T x)
    {
        this.put(x);
    }

    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        foreach(x; r)
        {
            this.put(x);
        }
    }

    ///
    void put()(T x)
    {
        T delta = x;
        if (count > 0) {
            delta -= meanAccumulator.mean;
        }
        meanAccumulator.put(x);
        centeredSummatorOfSquares.put(delta * (x - meanAccumulator.mean));
    }

    ///
    void put(U, VarianceAlgo varAlgo, Summation sumAlgo)(VarianceAccumulator!(U, varAlgo, sumAlgo) v)
        if(!is(varAlgo == VarianceAlgo.assumeZeroMean))
    {
        size_t oldCount = count;
        T delta = v.mean!T;
        if (oldCount > 0) {
            delta -= meanAccumulator.mean;
        }
        meanAccumulator.put!T(v.meanAccumulator);
        centeredSummatorOfSquares.put(v.centeredSumOfSquares!T + delta * delta * v.count * oldCount / count);
    }

const:

    ///
    size_t count() @property
    {
        return meanAccumulator.count;
    }
    ///
    F mean(F = T)() const @property
    {
        return meanAccumulator.mean!F;
    }
    ///
    F centeredSumOfSquares(F = T)()
    {
        return cast(F) centeredSummatorOfSquares.sum;
    }
    ///
    F variance(F = T)(bool isPopulation) @property
    in
    {
        assert(count > 1, "VarianceAccumulator.variance: count must be larger than one");
    }
    do
    {
        return centeredSumOfSquares!F / (count + isPopulation - 1);
    }
}

/// online
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(true).approxEqual(57.01923 / 13));
    assert(v.variance(false).approxEqual(57.01923 / 12));
}

// can put slices
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    v.put(y);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// Can put accumulator (online)
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// Can put accumulator (naive)
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// Can put accumulator (twoPass)
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    auto w = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// complex
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.complex.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.complex: Complex;

    auto x = [Complex!double(1.0, 3), Complex!double(2), Complex!double(3)].sliced;

    VarianceAccumulator!(Complex!double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(Complex!double(-4.0, -6) / 3));
    assert(v.variance(false).approxEqual(Complex!double(-4.0, -6) / 2));
}

// Test input range
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.sum: Summation;
    import mir.test: should;
    import std.range: iota;
    import std.algorithm: map;

    auto x1 = iota(0, 5);
    auto v1 = VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive)(x1);
    v1.variance(true).should == 2;
    v1.centeredSumOfSquares.should == 10;
    auto x2 = x1.map!(a => 2 * a);
    auto v2 = VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive)(x2);
    v2.variance(true).should == 8;
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.twoPass)
{
    import mir.math.sum: elementType, Summator;
    import mir.ndslice.slice: isConvertibleToSlice, isSlice, Slice, SliceKind;
    import std.range: isInputRange;

    ///
    private MeanAccumulator!(T, summation) meanAccumulator;

    ///
    private Summator!(T, summation) centeredSummatorOfSquares;

    ///
    this(Iterator, size_t N, SliceKind kind)(
         Slice!(Iterator, N, kind) slice)
    {
        import mir.functional: naryFun;
        import mir.ndslice.internal: LeftOp;
        import mir.ndslice.topology: vmap, map;

        meanAccumulator.put(slice.lightScope);
        centeredSummatorOfSquares.put(slice.vmap(LeftOp!("-", T)(meanAccumulator.mean)).map!(naryFun!"a * a"));
    }

    ///
    this(SliceLike)(SliceLike x)
        if (isConvertibleToSlice!SliceLike && !isSlice!SliceLike)
    {
        import mir.ndslice.slice: toSlice;
        this(x.toSlice);
    }

    ///
    this(Range)(Range range)
        if (isInputRange!Range && !isConvertibleToSlice!Range && is(elementType!Range : T))
    {
        import std.algorithm: map;
        meanAccumulator.put(range);

        auto centeredRangeMultiplier = range.map!(a => (a - mean)).map!("a * a");
        centeredSummatorOfSquares.put(centeredRangeMultiplier);
    }

const:

    ///
    size_t count() @property
    {
        return meanAccumulator.count;
    }
    ///
    F mean(F = T)() const @property
    {
        return meanAccumulator.mean;
    }
    ///
    F centeredSumOfSquares(F = T)() const @property
    {
        return cast(F) centeredSummatorOfSquares.sum;
    }
    ///
    F variance(F = T)(bool isPopulation) @property
    in
    {
        assert(count > 1, "SkewnessAccumulator.variance: count must be larger than one");
    }
    do
    {
        return centeredSumOfSquares!F / (count + isPopulation - 1);
    }
}

/// twoPass
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    auto v = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(x);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// dynamic array test
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;

    double[] x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                  2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    auto v = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(x);
    assert(v.centeredSumOfSquares.approxEqual(54.76562));
}

// withAsSlice test
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    import mir.rc.array: RCArray;

    static immutable a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    auto x = RCArray!double(12);
    foreach(i, ref e; x)
        e = a[i];

    auto v = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(x);
    assert(v.centeredSumOfSquares.sum.approxEqual(54.76562));
}

// Test input range
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.sum: Summation;
    import mir.test: should;
    import std.range: iota;
    import std.algorithm: map;

    auto x1 = iota(0, 5);
    auto v1 = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(x1);
    v1.variance(true).should == 2;
    v1.centeredSumOfSquares.should == 10;
    auto x2 = x1.map!(a => 2 * a);
    auto v2 = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(x2);
    v2.variance(true).should == 8;
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.assumeZeroMean)
{
    import mir.math.sum: Summator;
    import mir.ndslice.slice: Slice, SliceKind, hasAsSlice;

    private size_t _count;
    ///
    private Summator!(T, summation) centeredSummatorOfSquares;

    ///
    this(Range)(Range r)
        if (isIterable!Range)
    {
        this.put(r);
    }

    ///
    this()(T x)
    {
        this.put(x);
    }

    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        foreach(x; r)
        {
            this.put(x);
        }
    }

    ///
    void put()(T x)
    {
        _count++;
        centeredSummatorOfSquares.put(x * x);
    }

    ///
    void put(U, Summation sumAlgo)(VarianceAccumulator!(U, varianceAlgo, sumAlgo) v)
    {
        _count += v.count;
        centeredSummatorOfSquares.put(v.centeredSumOfSquares!T);
    }

const:

    ///
    size_t count() @property
    {
        return _count;
    }
    ///
    F mean(F = T)() const @property
    {
        return cast(F) 0;
    }
    ///
    MeanAccumulator!(T, summation) meanAccumulator()()
    {
        typeof(return) m = { _count, T(0) };
        return m;
    }
    ///
    F centeredSumOfSquares(F = T)() const @property
    {
        return cast(F) centeredSummatorOfSquares.sum;
    }
    ///
    F variance(F = T)(bool isPopulation) @property
    {
        return centeredSumOfSquares!F / (count + isPopulation - 1);
    }
}

/// assumeZeroMean
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto x = a.center;

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
    v.put(4.0);
    assert(v.variance(true).approxEqual(70.76562 / 13));
    assert(v.variance(false).approxEqual(70.76562 / 12));
}

// can put slices
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto b = a.center;
    auto x = b[0 .. 6];
    auto y = b[6 .. $];

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(13.492188 / 6));
    assert(v.variance(false).approxEqual(13.492188 / 5));

    v.put(y);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// can put two accumulator
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto b = a.center;
    auto x = b[0 .. 6];
    auto y = b[6 .. $];

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(13.492188 / 6));
    assert(v.variance(false).approxEqual(13.492188 / 5));

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// complex
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.complex.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.complex: Complex;

    auto a = [Complex!double(1.0, 3), Complex!double(2), Complex!double(3)].sliced;
    auto x = a.center;

    VarianceAccumulator!(Complex!double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(Complex!double(-4.0, -6) / 3));
    assert(v.variance(false).approxEqual(Complex!double(-4.0, -6) / 2));
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.hybrid)
{
    import mir.math.sum: elementType, Summator;
    import mir.ndslice.slice: isConvertibleToSlice, isSlice, Slice, SliceKind;
    import std.range: isInputRange;

    ///
    private MeanAccumulator!(T, summation) meanAccumulator;

    ///
    private Summator!(T, summation) centeredSummatorOfSquares;

    ///
    this(Iterator, size_t N, SliceKind kind)(
         Slice!(Iterator, N, kind) slice)
    {
        import mir.functional: naryFun;
        import mir.ndslice.internal: LeftOp;
        import mir.ndslice.topology: vmap, map;

        meanAccumulator.put(slice.lightScope);
        centeredSummatorOfSquares.put(slice.vmap(LeftOp!("-", T)(meanAccumulator.mean)).map!(naryFun!"a * a"));
    }

    ///
    this(SliceLike)(SliceLike x)
        if (isConvertibleToSlice!SliceLike && !isSlice!SliceLike)
    {
        import mir.ndslice.slice: toSlice;
        this(x.toSlice);
    }

    ///
    this(Range)(Range range)
        if (isIterable!Range && !isConvertibleToSlice!Range)
    {
        static if (isInputRange!Range && is(elementType!Range : T))
        {
            import std.algorithm: map;
            meanAccumulator.put(range);

            auto centeredRangeMultiplier = range.map!(a => (a - mean)).map!("a * a");
            centeredSummatorOfSquares.put(centeredRangeMultiplier);
        } else {
            this.put(range);
        }
    }

    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        static if (isInputRange!Range && is(elementType!Range : T)) {
            auto v = typeof(this)(r);
            this.put(v);
        } else{
            foreach(x; r)
            {
                this.put(x);
            }
        }
    }

    ///
    void put()(T x)
    {
        T delta = x;
        if (count > 0) {
            delta -= meanAccumulator.mean;
        }
        meanAccumulator.put(x);
        centeredSummatorOfSquares.put(delta * (x - meanAccumulator.mean));
    }

    ///
    void put(U, VarianceAlgo varAlgo, Summation sumAlgo)(VarianceAccumulator!(U, varAlgo, sumAlgo) v)
        if(!is(varAlgo == VarianceAlgo.assumeZeroMean))
    {
        size_t oldCount = count;
        T delta = v.mean!T;
        if (oldCount > 0) {
            delta -= meanAccumulator.mean;
        }
        meanAccumulator.put!T(v.meanAccumulator);
        centeredSummatorOfSquares.put(v.centeredSumOfSquares!T + delta * delta * v.count * oldCount / count);
    }

const:

    ///
    size_t count() @property
    {
        return meanAccumulator.count;
    }
    ///
    F mean(F = T)() const @property
    {
        return meanAccumulator.mean!F;
    }
    ///
    F centeredSumOfSquares(F = T)()
    {
        return cast(F) centeredSummatorOfSquares.sum;
    }
    ///
    F variance(F = T)(bool isPopulation) @property
    in
    {
        assert(count > 1, "VarianceAccumulator.variance: count must be larger than one");
    }
    do
    {
        return centeredSumOfSquares!F / (count + isPopulation - 1);
    }
}

/// online
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    auto v = VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive)(x);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(true).approxEqual(57.01923 / 13));
    assert(v.variance(false).approxEqual(57.01923 / 12));
}

// can put slices
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    auto v = VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive)(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    v.put(y);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// Can put accumulator (hybrid)
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// Can put accumulator (naive)
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// Can put accumulator (online)
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// Can put accumulator (twoPass)
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(12.55208 / 6));
    assert(v.variance(false).approxEqual(12.55208 / 5));

    auto w = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(y);
    v.put(w);
    assert(v.variance(true).approxEqual(54.76562 / 12));
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

// complex
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.complex.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.complex: Complex;

    auto x = [Complex!double(1.0, 3), Complex!double(2), Complex!double(3)].sliced;

    VarianceAccumulator!(Complex!double, VarianceAlgo.hybrid, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual(Complex!double(-4.0, -6) / 3));
    assert(v.variance(false).approxEqual(Complex!double(-4.0, -6) / 2));
}

// Test input range
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.sum: Summation;
    import mir.test: should;
    import std.range: chunks, iota;
    import std.algorithm: map;

    auto x1 = iota(0, 5);
    auto v1 = VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive)(x1);
    v1.variance(true).should == 2;
    v1.centeredSumOfSquares.should == 10;
    auto x2 = x1.map!(a => 2 * a);
    auto v2 = VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive)(x2);
    v2.variance(true).should == 8;
    VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive) v3;
    v3.put(x1.chunks(1));
    v3.centeredSumOfSquares.should == 10;
    auto v4 = VarianceAccumulator!(double, VarianceAlgo.hybrid, Summation.naive)(x1.chunks(1));
    v4.centeredSumOfSquares.should == 10;
}

/++
Calculates the variance of the input

By default, if `F` is not floating point type or complex type, then the result
will have a `double` type if `F` is implicitly convertible to a floating point 
type or a type for which `isComplex!F` is true.

Params:
    F = controls type of output
    varianceAlgo = algorithm for calculating variance (default: VarianceAlgo.hybrid)
    summation = algorithm for calculating sums (default: Summation.appropriate)
Returns:
    The variance of the input, must be floating point or complex type
+/
template variance(
    F, 
    VarianceAlgo varianceAlgo = VarianceAlgo.hybrid, 
    Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range, must be finite iterable
        isPopulation = true if population variance, false if sample variance (default)
    +/
    @fmamath meanType!F variance(Range)(Range r, bool isPopulation = false)
        if (isIterable!Range)
    {
        import core.lifetime: move;

        alias G = typeof(return);
        auto varianceAccumulator = VarianceAccumulator!(G, varianceAlgo, ResolveSummationType!(summation, Range, G))(r.move);
        return varianceAccumulator.variance(isPopulation);
    }

    /++
    Params:
        ar = values
    +/
    @fmamath meanType!F variance(scope const F[] ar...)
    {
        alias G = typeof(return);
        auto varianceAccumulator = VarianceAccumulator!(G, varianceAlgo, ResolveSummationType!(summation, const(G)[], G))(ar);
        return varianceAccumulator.variance(false);
    }
}

/// ditto
template variance(
    VarianceAlgo varianceAlgo = VarianceAlgo.hybrid, 
    Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range, must be finite iterable
        isPopulation = true if population variance, false if sample variance (default)
    +/
    @fmamath meanType!Range variance(Range)(Range r, bool isPopulation = false)
        if(isIterable!Range)
    {
        import core.lifetime: move;

        alias F = typeof(return);
        return .variance!(F, varianceAlgo, summation)(r.move, isPopulation);
    }

    /++
    Params:
        ar = values
    +/
    @fmamath meanType!T variance(T)(scope const T[] ar...)
    {
        alias F = typeof(return);
        return .variance!(F, varianceAlgo, summation)(ar);
    }
}

/// ditto
template variance(F, string varianceAlgo, string summation = "appropriate")
{
    mixin("alias variance = .variance!(F, VarianceAlgo." ~ varianceAlgo ~ ", Summation." ~ summation ~ ");");
}

/// ditto
template variance(string varianceAlgo, string summation = "appropriate")
{
    mixin("alias variance = .variance!(VarianceAlgo." ~ varianceAlgo ~ ", Summation." ~ summation ~ ");");
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.complex.math: capproxEqual = approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.complex;
    alias C = Complex!double;

    assert(variance([1.0, 2, 3]).approxEqual(2.0 / 2));
    assert(variance([1.0, 2, 3], true).approxEqual(2.0 / 3));

    assert(variance([C(1, 3), C(2), C(3)]).capproxEqual(C(-4, -6) / 2));
    
    assert(variance!float([0, 1, 2, 3, 4, 5].sliced(3, 2)).approxEqual(17.5 / 5));
    
    static assert(is(typeof(variance!float([1, 2, 3])) == float));
}

/// Variance of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    assert(x.variance.approxEqual(54.76562 / 11));
}

/// Variance of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;

    auto x = [
        [0.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 0.0]
    ].fuse;

    assert(x.variance.approxEqual(54.76562 / 11));
}

/// Column variance of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;

    auto x = [
        [0.0,  1.0, 1.5, 2.0], 
        [3.5, 4.25, 2.0, 7.5],
        [5.0,  1.0, 1.5, 0.0]
    ].fuse;
    auto result = [13.16667 / 2, 7.041667 / 2, 0.1666667 / 2, 30.16667 / 2];

    // Use byDim or alongDim with map to compute variance of row/column.
    assert(x.byDim!1.map!variance.all!approxEqual(result));
    assert(x.alongDim!0.map!variance.all!approxEqual(result));

    // FIXME
    // Without using map, computes the variance of the whole slice
    // assert(x.byDim!1.variance == x.sliced.variance);
    // assert(x.alongDim!0.variance == x.sliced.variance);
}

/// Can also set algorithm type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    auto x = a + 1_000_000_000;

    auto y = x.variance;
    assert(y.approxEqual(54.76562 / 11));

    // The naive algorithm is numerically unstable in this case
    auto z0 = x.variance!"naive";
    assert(!z0.approxEqual(y));
    
    auto z1 = x.variance!"online";
    assert(z1.approxEqual(54.76562 / 11));

    // But the two-pass algorithm provides a consistent answer
    auto z2 = x.variance!"twoPass";
    assert(z2.approxEqual(y));

    // And the assumeZeroMean algorithm is way off
    auto z3 = x.variance!"assumeZeroMean";
    assert(z3.approxEqual(1.2e19 / 11));
}

/// Can also set algorithm or output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;

    //Set population variance, variance algorithm, sum algorithm or output type

    auto a = [1.0, 1e100, 1, -1e100].sliced;
    auto x = a * 10_000;

    /++
    Due to Floating Point precision, when centering `x`, subtracting the mean 
    from the second and fourth numbers has no effect. Further, after centering 
    and squaring `x`, the first and third numbers in the slice have precision 
    too low to be included in the centered sum of squares. 
    +/
    assert(x.variance(false).approxEqual(2.0e208 / 3));
    assert(x.variance(true).approxEqual(2.0e208 / 4));

    assert(x.variance!("online").approxEqual(2.0e208 / 3));
    assert(x.variance!("online", "kbn").approxEqual(2.0e208 / 3));
    assert(x.variance!("online", "kb2").approxEqual(2.0e208 / 3));
    assert(x.variance!("online", "precise").approxEqual(2.0e208 / 3));
    assert(x.variance!(double, "online", "precise").approxEqual(2.0e208 / 3));
    assert(x.variance!(double, "online", "precise")(true).approxEqual(2.0e208 / 4));

    auto y = uint.max.repeat(3);
    auto z = y.variance!ulong;
    assert(z == 0.0);
    static assert(is(typeof(z) == double));
}

/++
For integral slices, pass output type as template parameter to ensure output
type is correct.
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    auto x = [0, 1, 1, 2, 4, 4,
              2, 7, 5, 1, 2, 0].sliced;

    auto y = x.variance;
    assert(y.approxEqual(50.91667 / 11));
    static assert(is(typeof(y) == double));

    assert(x.variance!float.approxEqual(50.91667 / 11));
}

/++
Variance works for complex numbers and other user-defined types (provided they
can be converted to a floating point or complex type)
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.complex.math: approxEqual;
    import mir.ndslice.slice: sliced;
    import mir.complex;
    alias C = Complex!double;

    auto x = [C(1, 2), C(2, 3), C(3, 4), C(4, 5)].sliced;
    assert(x.variance.approxEqual((C(0, 10)) / 3));
}

/// Compute variance along specified dimention of tensors
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: as, iota, alongDim, map, repeat;

    auto x = [
        [0.0, 1, 2],
        [3.0, 4, 5]
    ].fuse;

    assert(x.variance.approxEqual(17.5 / 5));

    auto m0 = [4.5, 4.5, 4.5];
    assert(x.alongDim!0.map!variance.all!approxEqual(m0));
    assert(x.alongDim!(-2).map!variance.all!approxEqual(m0));

    auto m1 = [1.0, 1.0];
    assert(x.alongDim!1.map!variance.all!approxEqual(m1));
    assert(x.alongDim!(-1).map!variance.all!approxEqual(m1));

    assert(iota(2, 3, 4, 5).as!double.alongDim!0.map!variance.all!approxEqual(repeat(3600.0 / 2, 3, 4, 5)));
}

/// Arbitrary variance
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    assert(variance(1.0, 2, 3) == 1.0);
    assert(variance!float(1, 2, 3) == 1f);
}

// UCFS test
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;

    assert([1.0, 2, 3, 4].variance.approxEqual(5.0 / 3));
}

// testing types are right along dimension
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.topology: iota, alongDim, map;

    auto x = iota([2, 2], 1);
    auto y = x.alongDim!1.map!variance;
    assert(y.all!approxEqual([0.5, 0.5]));
    static assert(is(meanType!(typeof(y)) == double));
}

// @nogc test
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.slice: sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    assert(x.sliced.variance.approxEqual(54.76562 / 11));
    assert(x.sliced.variance!float.approxEqual(54.76562 / 11));
}

///
package(mir)
template stdevType(T)
{
    import mir.internal.utility: isFloatingPoint;
    
    alias U = meanType!T;

    static if (isFloatingPoint!U) {
        alias stdevType = U;
    } else {
        static assert(0, "stdevType: Can't calculate standard deviation of elements of type " ~ U.stringof);
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static assert(is(stdevType!(int[]) == double));
    static assert(is(stdevType!(double[]) == double));
    static assert(is(stdevType!(float[]) == float));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }

    static assert(is(stdevType!(Foo[]) == float));
}

/++
Calculates the standard deviation of the input

By default, if `F` is not floating point type, then the result will have a
`double` type if `F` is implicitly convertible to a floating point type.

Params:
    F = controls type of output
    varianceAlgo = algorithm for calculating variance (default: VarianceAlgo.online)
    summation = algorithm for calculating sums (default: Summation.appropriate)
Returns:
    The standard deviation of the input, must be floating point type type
+/
template standardDeviation(
    F, 
    VarianceAlgo varianceAlgo = VarianceAlgo.online, 
    Summation summation = Summation.appropriate)
{
    import mir.math.common: sqrt;

    /++
    Params:
        r = range, must be finite iterable
        isPopulation = true if population standard deviation, false if sample standard deviation (default)
    +/
    @fmamath stdevType!F standardDeviation(Range)(Range r, bool isPopulation = false)
        if (isIterable!Range)
    {
        import core.lifetime: move;
        alias G = typeof(return);
        return r.move.variance!(G, varianceAlgo, ResolveSummationType!(summation, Range, G))(isPopulation).sqrt;
    }

    /++
    Params:
        ar = values
    +/
    @fmamath stdevType!F standardDeviation(scope const F[] ar...)
    {
        alias G = typeof(return);
        return ar.variance!(G, varianceAlgo, ResolveSummationType!(summation, const(G)[], G)).sqrt;
    }
}

/// ditto
template standardDeviation(
    VarianceAlgo varianceAlgo = VarianceAlgo.online, 
    Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range, must be finite iterable
        isPopulation = true if population standard deviation, false if sample standard deviation (default)
    +/
    @fmamath stdevType!Range standardDeviation(Range)(Range r, bool isPopulation = false)
        if(isIterable!Range)
    {
        import core.lifetime: move;

        alias F = typeof(return);
        return .standardDeviation!(F, varianceAlgo, summation)(r.move, isPopulation);
    }

    /++
    Params:
        ar = values
    +/
    @fmamath stdevType!T standardDeviation(T)(scope const T[] ar...)
    {
        alias F = typeof(return);
        return .standardDeviation!(F, varianceAlgo, summation)(ar);
    }
}

/// ditto
template standardDeviation(F, string varianceAlgo, string summation = "appropriate")
{
    mixin("alias standardDeviation = .standardDeviation!(F, VarianceAlgo." ~ varianceAlgo ~ ", Summation." ~ summation ~ ");");
}

/// ditto
template standardDeviation(string varianceAlgo, string summation = "appropriate")
{
    mixin("alias standardDeviation = .standardDeviation!(VarianceAlgo." ~ varianceAlgo ~ ", Summation." ~ summation ~ ");");
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.slice: sliced;

    assert(standardDeviation([1.0, 2, 3]).approxEqual(sqrt(2.0 / 2)));
    assert(standardDeviation([1.0, 2, 3], true).approxEqual(sqrt(2.0 / 3)));
    
    assert(standardDeviation!float([0, 1, 2, 3, 4, 5].sliced(3, 2)).approxEqual(sqrt(17.5 / 5)));
    
    static assert(is(typeof(standardDeviation!float([1, 2, 3])) == float));
}

/// Standard deviation of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.slice: sliced;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    assert(x.standardDeviation.approxEqual(sqrt(54.76562 / 11)));
}

/// Standard deviation of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.fuse: fuse;

    auto x = [
        [0.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 0.0]
    ].fuse;

    assert(x.standardDeviation.approxEqual(sqrt(54.76562 / 11)));
}

/// Column standard deviation of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;

    auto x = [
        [0.0,  1.0, 1.5, 2.0], 
        [3.5, 4.25, 2.0, 7.5],
        [5.0,  1.0, 1.5, 0.0]
    ].fuse;
    auto result = [13.16667 / 2, 7.041667 / 2, 0.1666667 / 2, 30.16667 / 2].map!sqrt;

    // Use byDim or alongDim with map to compute standardDeviation of row/column.
    assert(x.byDim!1.map!standardDeviation.all!approxEqual(result));
    assert(x.alongDim!0.map!standardDeviation.all!approxEqual(result));

    // FIXME
    // Without using map, computes the standardDeviation of the whole slice
    // assert(x.byDim!1.standardDeviation == x.sliced.standardDeviation);
    // assert(x.alongDim!0.standardDeviation == x.sliced.standardDeviation);
}

/// Can also set algorithm type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.slice: sliced;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    auto x = a + 1_000_000_000;

    auto y = x.standardDeviation;
    assert(y.approxEqual(sqrt(54.76562 / 11)));

    // The naive algorithm is numerically unstable in this case
    auto z0 = x.standardDeviation!"naive";
    assert(!z0.approxEqual(y));

    // But the two-pass algorithm provides a consistent answer
    auto z1 = x.standardDeviation!"twoPass";
    assert(z1.approxEqual(y));
}

/// Can also set algorithm or output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;

    //Set population standard deviation, standardDeviation algorithm, sum algorithm or output type

    auto a = [1.0, 1e100, 1, -1e100].sliced;
    auto x = a * 10_000;

    /++
    Due to Floating Point precision, when centering `x`, subtracting the mean 
    from the second and fourth numbers has no effect. Further, after centering 
    and squaring `x`, the first and third numbers in the slice have precision 
    too low to be included in the centered sum of squares. 
    +/
    assert(x.standardDeviation(false).approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation(true).approxEqual(sqrt(2.0e208 / 4)));

    assert(x.standardDeviation!("online").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!("online", "kbn").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!("online", "kb2").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!("online", "precise").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!(double, "online", "precise").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!(double, "online", "precise")(true).approxEqual(sqrt(2.0e208 / 4)));

    auto y = uint.max.repeat(3);
    auto z = y.standardDeviation!ulong;
    assert(z == 0.0);
    static assert(is(typeof(z) == double));
}

/++
For integral slices, pass output type as template parameter to ensure output
type is correct.
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.slice: sliced;

    auto x = [0, 1, 1, 2, 4, 4,
              2, 7, 5, 1, 2, 0].sliced;

    auto y = x.standardDeviation;
    assert(y.approxEqual(sqrt(50.91667 / 11)));
    static assert(is(typeof(y) == double));

    assert(x.standardDeviation!float.approxEqual(sqrt(50.91667 / 11)));
}

/++
Variance works for other user-defined types (provided they
can be converted to a floating point)
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    
    static struct Foo {
        float x;
        alias x this;
    }
    
    Foo[] foo = [Foo(1f), Foo(2f), Foo(3f)];
    assert(foo.standardDeviation == 1f);
}

/// Compute standard deviation along specified dimention of tensors
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: as, iota, alongDim, map, repeat;

    auto x = [
        [0.0, 1, 2],
        [3.0, 4, 5]
    ].fuse;

    assert(x.standardDeviation.approxEqual(sqrt(17.5 / 5)));

    auto m0 = repeat(sqrt(4.5), 3);
    assert(x.alongDim!0.map!standardDeviation.all!approxEqual(m0));
    assert(x.alongDim!(-2).map!standardDeviation.all!approxEqual(m0));

    auto m1 = [1.0, 1.0];
    assert(x.alongDim!1.map!standardDeviation.all!approxEqual(m1));
    assert(x.alongDim!(-1).map!standardDeviation.all!approxEqual(m1));

    assert(iota(2, 3, 4, 5).as!double.alongDim!0.map!standardDeviation.all!approxEqual(repeat(sqrt(3600.0 / 2), 3, 4, 5)));
}

/// Arbitrary standard deviation
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: sqrt;

    assert(standardDeviation(1.0, 2, 3) == 1.0);
    assert(standardDeviation!float(1, 2, 3) == 1f);
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual, sqrt;
    assert([1.0, 2, 3, 4].standardDeviation.approxEqual(sqrt(5.0 / 3)));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.topology: iota, alongDim, map;

    auto x = iota([2, 2], 1);
    auto y = x.alongDim!1.map!standardDeviation;
    assert(y.all!approxEqual([sqrt(0.5), sqrt(0.5)]));
    static assert(is(meanType!(typeof(y)) == double));
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.math.common: approxEqual, sqrt;
    import mir.ndslice.slice: sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    assert(x.sliced.standardDeviation.approxEqual(sqrt(54.76562 / 11)));
    assert(x.sliced.standardDeviation!float.approxEqual(sqrt(54.76562 / 11)));
}

/++
A linear regression model with a single explanatory variable.
+/
template simpleLinearRegression(Summation summation = Summation.kbn)
{
    import mir.ndslice.slice;
    import mir.primitives: isInputRange;

    /++
    Params:
        x = `x[i]` points
        y = `f(x[i])` values
    Returns:
        The pair of shift and slope of the linear curve.
    +/
    @fmamath
    sumType!YRange[2]
    simpleLinearRegression(XRange, YRange)(XRange x, YRange y) @safe
        if (isInputRange!XRange && isInputRange!YRange && !(isArray!XRange && isArray!YRange) && isFloatingPoint!(sumType!YRange))
    in {
        static if (hasLength!XRange && hasLength!YRange)
            assert(x.length == y.length);
    }
    do {
        alias X = typeof(sumType!XRange.init * sumType!XRange.init);
        alias Y = sumType!YRange;
        enum summationX = !__traits(isIntegral, X) ? summation: Summation.naive;
        Summator!(X, summationX) xms = 0;
        Summator!(Y, summation) yms = 0;
        Summator!(X, summationX) xxms = 0;
        Summator!(Y, summation) xyms = 0;

        static if (hasLength!XRange)
            sizediff_t n = x.length;
        else
            sizediff_t n = 0;

        while (!x.empty)
        {
            static if (!(hasLength!XRange && hasLength!YRange))
                assert(!y.empty);

            static if (!hasLength!XRange)
                n++;

            auto xi = x.front;
            auto yi = y.front;
            xms.put(xi);
            yms.put(yi);
            xxms.put(xi * xi);
            xyms.put(xi * yi);

            y.popFront;
            x.popFront;
        }

        static if (!(hasLength!XRange && hasLength!YRange))
            assert(y.empty);

        auto xm = xms.sum;
        auto ym = yms.sum;
        auto xxm = xxms.sum;
        auto xym = xyms.sum;

        auto slope = (xym * n - xm * ym) / (xxm * n - xm * xm);

        return [(ym - slope * xm) / n, slope];
    }

    /// ditto
    @fmamath
    sumType!(Y[])[2]
    simpleLinearRegression(X, Y)(scope const X[] x, scope const Y[] y) @safe
    {
        return .simpleLinearRegression!summation(x.sliced, y.sliced);
    }
}

/// ditto
template simpleLinearRegression(string summation)
{
    mixin("alias simpleLinearRegression = .simpleLinearRegression!(Summation." ~ summation ~ ");");
}

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    static immutable x = [0, 1, 2, 3];
    static immutable y = [-1, 0.2, 0.9, 2.1];
    auto params = x.simpleLinearRegression(y);
    assert(params[0].approxEqual(-0.95)); // shift
    assert(params[1].approxEqual(1)); // slope
}
