/++
This module contains base statistical algorithms.

Note that used specialized summing algorithms execute more primitive operations
than vanilla summation. Therefore, if in certain cases maximum speed is required
at expense of precision, one can use $(REF_ALTTEXT $(TT Summation.fast), Summation.fast, mir, math, sum)$(NBSP).

License: $(LINK2 http://boost.org/LICENSE_1_0.txt, Boost License 1.0).

Authors: Shigeki Karita (original numir code), Ilya Yaroshenko, John Michael Hall

Copyright: 2019 Symmetry Investments Group and Kaleidic Associates Advisory Limited.

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, math, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
+/
module mir.math.stat;

import core.lifetime: move;
import mir.ndslice.slice: Slice, SliceKind, hasAsSlice;
import mir.math.common: fmamath;
import mir.math.sum;
import mir.primitives;
import std.traits: isArray, isMutable, isIterable, isIntegral, CommonType;
import mir.internal.utility: isFloatingPoint;

package template statType(T, bool checkComplex = true)
{
    import mir.internal.utility: isFloatingPoint, isComplex;

    static if (isFloatingPoint!T || (checkComplex && isComplex!T)) {
        import std.traits: Unqual;
        alias statType = Unqual!T;
    } else static if (is(T : double)) {
        alias statType = double;
    } else static if (checkComplex) {
        static if (is(T : cdouble)) {
            alias statType = cdouble;
        } else {
            static assert(0, "statType: type " ~ T.stringof ~ " must be convertible to a floating point (or complex floating point) type");
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
    static assert(is(statType!cfloat == cfloat));
    static assert(is(statType!cdouble == cdouble));
    static assert(is(statType!creal == creal));
    
    static assert(is(statType!(const(int)) == double));
    static assert(is(statType!(immutable(int)) == double));
    static assert(is(statType!(const(double)) == double));
    static assert(is(statType!(immutable(double)) == double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }
    
    static struct Bar {
        cfloat x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not float
    static assert(is(statType!Bar == cdouble)); // note: this is not cfloat
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        double x;
        alias x this;
    }
    
    static struct Bar {
        cdouble x;
        alias x this;
    }

    static assert(is(statType!Foo == double));
    static assert(is(statType!Bar == cdouble));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        real x;
        alias x this;
    }
    
    static struct Bar {
        creal x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not real
    static assert(is(statType!Bar == cdouble)); // note: this is not creal
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

package template meanType(T)
{
    import mir.math.sum: sumType;
    import mir.internal.utility: isFloatingPoint, isComplex;
    
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
    static assert(is(meanType!(cfloat[]) == cfloat));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }
    
    static struct Bar {
        cfloat x;
        alias x this;
    }

    static assert(is(meanType!(Foo[]) == float));
    static assert(is(meanType!(Bar[]) == cfloat));
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
type or have a `cdouble` type if `F` is implicitly convertible to a complex type.

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

    assert(mean([1.0, 2, 3]) == 2);
    assert(mean([1.0 + 3i, 2, 3]) == 2 + 1i);
    
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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [1.0 + 2i, 2 + 3i, 3 + 4i, 4 + 5i].sliced;
    assert(x.mean.approxEqual(2.5 + 3.5i));
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
    import mir.ndslice.topology: iota, alongDim, map;
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;

    auto x = iota([2, 2], 1);
    auto y = x.alongDim!1.map!mean;
    assert(y.all!approxEqual([1.5, 3.5]));
    static assert(is(meanType!(typeof(y)) == double));
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    assert(x.sliced.mean == 29.25 / 12);
    assert(x.sliced.mean!float == 29.25 / 12);
}

package template hmeanType(T)
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
        static assert(0, "meanType: Can't calculate hmean of elements of type " ~ U.stringof);
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static assert(is(hmeanType!(int[]) == double));
    static assert(is(hmeanType!(double[]) == double));
    static assert(is(hmeanType!(float[]) == float)); 
    static assert(is(hmeanType!(cfloat[]) == cfloat));    
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }
    
    static struct Bar {
        cfloat x;
        alias x this;
    }

    static assert(is(hmeanType!(Foo[]) == float));
    static assert(is(hmeanType!(Bar[]) == cfloat));
}

/++
Computes the harmonic mean of the input.

By default, if `F` is not floating point type or complex type, then the result
will have a `double` type if `F` is implicitly convertible to a floating point 
type or have a `cdouble` type if `F` is implicitly convertible to a complex type.

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
    import mir.ndslice.topology: repeat;
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [1.0 + 2i, 2 + 3i, 3 + 4i, 4 + 5i].sliced;
    assert(x.hmean.approxEqual(1.97110904 + 3.14849332i));
}

/// Arbitrary harmonic mean
version(mir_test)
@safe pure @nogc nothrow
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
@safe pure @nogc nothrow
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
@safe @nogc pure nothrow
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
    F gmean(F = T)() @property
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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    GMeanAccumulator!float x;
    x.put([1, 2, 3, 4].sliced);
    assert(x.gmean.approxEqual(2.21336384));
    x.put(5);
    assert(x.gmean.approxEqual(2.60517108));
}

package template gmeanType(T)
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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    assert(gmean([1.0, 2, 3]).approxEqual(1.81712059));
    
    assert(gmean!float([1, 2, 3, 4, 5, 6].sliced(3, 2)).approxEqual(2.99379516));
    
    static assert(is(typeof(gmean!float([1, 2, 3])) == float));
}

/// Geometric mean of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [3.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 2.0].sliced;

    assert(x.gmean.approxEqual(2.36178395));
}

/// Geometric mean of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.fuse: fuse;
    import mir.algorithm.iteration: all;
    import mir.ndslice.topology: alongDim, byDim, map;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, iota, map;
    import mir.math.common: approxEqual;
    
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
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    static immutable x = [3.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 2.0];

    assert(x.sliced.gmean.approxEqual(2.36178395));
    assert(x.sliced.gmean!float.approxEqual(2.36178395));
}

/++
Computes the median of `slice`.

Can also pass a boolean variable, `allowModify`, that allows the input slice to
be modified. By default, a reference-counted copy is made. 

Returns:
    the median of the slice

See_also:
    $(LREF, mean)
+/
template median(F, bool allowModify = false)
{
    F median(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        size_t len = slice.elementCount;
        assert(len > 0, "median: slice must have length greater than zero");

        import mir.ndslice.topology: flattened;

        static if (!allowModify) {
            import mir.ndslice.allocation: rcslice;
            
            if (len > 2) {
                auto val = slice.rcslice.flattened;
                auto temp = val.lightScope;
                return .median!(F, true)(temp);
            } else {
                return mean!F(slice);
            }
        } else {
            import mir.ndslice.sorting: partitionAt;
            
            auto temp = slice.flattened;

            if (len > 5) {
                size_t half_n = len / 2;
                partitionAt(temp, half_n);
                if (len % 2 == 1) {
                    return cast(F) temp[half_n];
                } else {
                    //move largest value in first half of slice to half_n - 1
                    partitionAt(temp[0 .. half_n], half_n - 1);
                    return (temp[half_n - 1] + temp[half_n]) / cast(F) 2;
                }
            } else {
                return smallMedianImpl!(F)(temp);
            }
        }
    }
}

///
template median(bool allowModify = false)
{
    sumType!(Slice!(Iterator, N, kind))
        median
            (Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice) {
        return .median!(sumType!(Slice!(Iterator, N, kind)), allowModify)(slice.move);
    }
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
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: alongDim, byDim, map;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

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

/++
For integral slices, pass output type as template parameter to ensure output
type is correct
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    auto x = [9, 1, 0, 2, 3, 4, 6, 8, 7, 10].sliced;
    assert(x.median!float == 5);
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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

private pure @trusted nothrow @nogc
F smallMedianImpl(F, Iterator)(Slice!Iterator slice) 
{
    size_t n = slice.elementCount;

    assert(n > 0, "smallMedianImpl: slice must have elementCount greater than 0");
    assert(n <= 5, "smallMedianImpl: slice must have elementCount of 5 or less");

    import mir.ndslice.sorting: medianOf;
    import mir.functional: naryFun;
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

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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
Output range that applies function `fun` to each input before summing
+/
struct MapSummator(alias fun, T, Summation summation) 
    if(isMutable!T)
{
    ///
    Summator!(T, summation) summator;

    ///
    F sum(F = T)() @property
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
    import mir.ndslice.slice: sliced;
    import mir.math.common: powi;

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
@safe pure @nogc nothrow
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
    import mir.ndslice.slice: sliced;
    import mir.ndslice.fuse: fuse;

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

See_also:
    $(WEB en.wikipedia.org/wiki/Algorithms_for_calculating_variance, Algorithms for calculating variance).
+/
enum VarianceAlgo
{
    /++
    Performs Welford's online algorithm for updating variance. Can also `put`
    another VarianceAccumulator of the same type, which uses the parallel
    algorithm from Chan et al., described above.
    +/
    online,
    
    /++
    Calculates variance using E(x^^2) - E(x)^2 (alowing for adjustments for 
    population/sample variance). This algorithm can be numerically unstable.
    +/
    naive,

    /++
    Calculates variance using a two-pass algorithm whereby the input is first 
    centered and then the sum of squares is calculated from that.
    +/
    twoPass,

    /++
    Calculates variance assuming the mean of the dataseries is zero. 
    +/
    assumeZeroMean
}

private
mixin template moment_ops(T,
                          Summation summation)
{
    ///
    MeanAccumulator!(T, summation) meanAccumulator;

    ///
    size_t count() @property
    {
        return meanAccumulator.count;
    }

    ///
    F mean(F = T)() @property
    {
        return meanAccumulator.mean;
    }
}

private
mixin template outputRange_ops(T)
{
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
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.naive)
{
    import mir.functional: naryFun;

    mixin moment_ops!(T, summation);
    mixin outputRange_ops!T;

    ///
    Summator!(T, summation) sumOfSquares;

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
        sumOfSquares.put(x * x);
    }

    ///
    F variance(F = T)(bool isPopulation) @property
    {
        if (isPopulation == false)
            return cast(F) sumOfSquares.sum / cast(F) (count - 1) - 
                (cast(F) meanAccumulator.mean) ^^ 2 * (cast(F) count / cast(F) (count - 1));
        else
            return cast(F) sumOfSquares.sum / cast(F) count - 
                (cast(F) meanAccumulator.mean) ^^ 2;
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    VarianceAccumulator!(double, VarianceAlgo.naive, Summation.naive) v;
    v.put(x);
    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(PopulationTrueRT).approxEqual(57.01923 / 13));
    assert(v.variance(PopulationTrueCT).approxEqual(57.01923 / 13));
    assert(v.variance(PopulationFalseRT).approxEqual(57.01923 / 12));
    assert(v.variance(PopulationFalseCT).approxEqual(57.01923 / 12));
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && 
        varianceAlgo == VarianceAlgo.online)
{
    mixin moment_ops!(T, summation);
    mixin outputRange_ops!T;

    ///
    Summator!(T, summation) centeredSumOfSquares;

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
        size_t oldCount = count;
        T delta = x;
        if (count > 0) {
            delta -= meanAccumulator.mean;
        }
        meanAccumulator.put(x);
        centeredSumOfSquares.put(delta * (x - meanAccumulator.mean));
    }

    ///
    void put()(VarianceAccumulator!(T, varianceAlgo, summation) v)
    {
        size_t oldCount = count;
        T delta = v.mean;
        if (oldCount > 0) {
            delta -= meanAccumulator.mean;
        }
        meanAccumulator.put!T(v.meanAccumulator);
        centeredSumOfSquares.put(v.centeredSumOfSquares.sum + delta * delta * v.count * oldCount / count);
    }

    ///
    F variance(F = T)(bool isPopulation) @property
    {
        if (isPopulation == false)
            return cast(F) centeredSumOfSquares.sum / cast(F) (count - 1);
        else
            return cast(F) centeredSumOfSquares.sum / cast(F) count;
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);

    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(PopulationTrueRT).approxEqual(57.01923 / 13));
    assert(v.variance(PopulationTrueCT).approxEqual(57.01923 / 13));
    assert(v.variance(PopulationFalseRT).approxEqual(57.01923 / 12));
    assert(v.variance(PopulationFalseCT).approxEqual(57.01923 / 12));
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(PopulationTrueRT).approxEqual(12.55208 / 6));
    assert(v.variance(PopulationTrueCT).approxEqual(12.55208 / 6));
    assert(v.variance(PopulationFalseRT).approxEqual(12.55208 / 5));
    assert(v.variance(PopulationFalseCT).approxEqual(12.55208 / 5));

    v.put(y);
    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(PopulationTrueRT).approxEqual(12.55208 / 6));
    assert(v.variance(PopulationTrueCT).approxEqual(12.55208 / 6));
    assert(v.variance(PopulationFalseRT).approxEqual(12.55208 / 5));
    assert(v.variance(PopulationFalseCT).approxEqual(12.55208 / 5));

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [1.0 + 3i, 2, 3].sliced;

    VarianceAccumulator!(cdouble, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual((-4.0 - 6i) / 3));
    assert(v.variance(false).approxEqual((-4.0 - 6i) / 2));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(false).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(false).approxEqual(57.01923 / 12));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25].sliced;
    auto y = [2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) v;
    v.put(x);
    assert(v.variance(false).approxEqual(12.55208 / 5));

    VarianceAccumulator!(double, VarianceAlgo.online, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.twoPass)
{
    import mir.functional: naryFun;
    import mir.ndslice.slice: Slice, SliceKind, hasAsSlice;

    mixin moment_ops!(T, summation);

    ///
    Summator!(T, summation) centeredSumOfSquares;

    ///
    this(Iterator, size_t N, SliceKind kind)(
         Slice!(Iterator, N, kind) slice)
    {
        import core.lifetime: move;
        import mir.ndslice.topology: vmap, map;
        import mir.ndslice.internal: LeftOp;

        meanAccumulator.put(slice.lightScope);
        centeredSumOfSquares.put(slice.move.vmap(LeftOp!("-", T)(meanAccumulator.mean)).map!(naryFun!"a * a"));
    }

    ///
    this(U)(U[] array)
    {
        import mir.ndslice.slice: sliced;
        this(array.sliced);
    }

    ///
    this(T)(T withAsSlice)
        if (hasAsSlice!T)
    {
        this(withAsSlice.asSlice);
    }

    ///
    this()(T x)
    {
        meanAccumulator.put(x);
        centeredSumOfSquares.put(cast(T) 0);
    }

    ///
    F variance(F = T)(bool isPopulation) @property
    {
        if (isPopulation == false)
            return cast(F) centeredSumOfSquares.sum / cast(F) (count - 1);
        else
            return cast(F) centeredSumOfSquares.sum / cast(F) count;
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    auto v = VarianceAccumulator!(double, VarianceAlgo.twoPass, Summation.naive)(x);
    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));
}

///
struct VarianceAccumulator(T, VarianceAlgo varianceAlgo, Summation summation)
    if (isMutable!T && varianceAlgo == VarianceAlgo.assumeZeroMean)
{
    import mir.ndslice.slice: Slice, SliceKind, hasAsSlice;

    private size_t _count;
    
    ///
    size_t count() @property
    {
        return _count;
    }
    
    ///
    F mean(F = T)() @property
    {
        return cast(F) 0;
    }

    ///
    Summator!(T, summation) centeredSumOfSquares;

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
        centeredSumOfSquares.put(x * x);
    }

    ///
    void put()(VarianceAccumulator!(T, varianceAlgo, summation) v)
    {
        _count += v.count;
        centeredSumOfSquares.put(v.centeredSumOfSquares.sum);
    }

    ///
    F variance(F = T)(bool isPopulation) @property
    {
        if (isPopulation == false)
            return cast(F) centeredSumOfSquares.sum / cast(F) (count - 1);
        else
            return cast(F) centeredSumOfSquares.sum / cast(F) count;
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto x = a.center;

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);

    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(PopulationTrueRT).approxEqual(70.76562 / 13));
    assert(v.variance(PopulationTrueCT).approxEqual(70.76562 / 13));
    assert(v.variance(PopulationFalseRT).approxEqual(70.76562 / 12));
    assert(v.variance(PopulationFalseCT).approxEqual(70.76562 / 12));
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto b = a.center;
    auto x = b[0 .. 6];
    auto y = b[6 .. $];

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(PopulationTrueRT).approxEqual(13.492188 / 6));
    assert(v.variance(PopulationTrueCT).approxEqual(13.492188 / 6));
    assert(v.variance(PopulationFalseRT).approxEqual(13.492188 / 5));
    assert(v.variance(PopulationFalseCT).approxEqual(13.492188 / 5));

    v.put(y);
    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto b = a.center;
    auto x = b[0 .. 6];
    auto y = b[6 .. $];

    enum PopulationTrueCT = true;
    enum PopulationFalseCT = false;
    bool PopulationTrueRT = true;
    bool PopulationFalseRT = false;

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(PopulationTrueRT).approxEqual(13.492188 / 6));
    assert(v.variance(PopulationTrueCT).approxEqual(13.492188 / 6));
    assert(v.variance(PopulationFalseRT).approxEqual(13.492188 / 5));
    assert(v.variance(PopulationFalseCT).approxEqual(13.492188 / 5));

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(PopulationTrueRT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationTrueCT).approxEqual(54.76562 / 12));
    assert(v.variance(PopulationFalseRT).approxEqual(54.76562 / 11));
    assert(v.variance(PopulationFalseCT).approxEqual(54.76562 / 11));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto a = [1.0 + 3i, 2, 3].sliced;
    auto x = a.center;

    VarianceAccumulator!(cdouble, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(true).approxEqual((-4.0 - 6i) / 3));
    assert(v.variance(false).approxEqual((-4.0 - 6i) / 2));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto x = a.center;

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(false).approxEqual(54.76562 / 11));

    v.put(4.0);
    assert(v.variance(false).approxEqual(70.76562 / 12));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
    auto b = a.center;
    auto x = b[0 .. 6];
    auto y = b[6 .. $];

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) v;
    v.put(x);
    assert(v.variance(false).approxEqual(13.492188 / 5));

    VarianceAccumulator!(double, VarianceAlgo.assumeZeroMean, Summation.naive) w;
    w.put(y);
    v.put(w);
    assert(v.variance(false).approxEqual(54.76562 / 11));
}

/++
Calculates the variance of the input

By default, if `F` is not floating point type or complex type, then the result
will have a `double` type if `F` is implicitly convertible to a floating point 
type or have a `cdouble` type if `F` is implicitly convertible to a complex type.

Params:
    F = controls type of output
    varianceAlgo = algorithm for calculating variance (default: VarianceAlgo.online)
    summation: algorithm for calculating sums (default: Summation.appropriate)

Returns:
    The variance of the input, must be floating point or complex type

See_also:
    $(LREF, VarianceAccumulator),
    $(LREF, VarianceAlgo),
    $(SUBREF sum, Summation)
+/
template variance(
    F, 
    VarianceAlgo varianceAlgo = VarianceAlgo.online, 
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
    VarianceAlgo varianceAlgo = VarianceAlgo.online, 
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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    assert(variance([1.0, 2, 3]).approxEqual(2.0 / 2));
    assert(variance([1.0, 2, 3], true).approxEqual(2.0 / 3));

    assert(variance([1.0 + 3i, 2, 3]).approxEqual((-4.0 - 6i) / 2));
    
    assert(variance!float([0, 1, 2, 3, 4, 5].sliced(3, 2)).approxEqual(17.5 / 5));
    
    static assert(is(typeof(variance!float([1, 2, 3])) == float));
}

/// Variance of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    assert(x.variance.approxEqual(54.76562 / 11));
}

/// Variance of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;

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
//@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto a = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    auto x = a + 1_000_000_000;

    auto y = x.variance;
    assert(y.approxEqual(54.76562 / 11));

    // The naive algorithm is numerically unstable in this case
    auto z0 = x.variance!"naive";
    assert(!z0.approxEqual(y));

    // But the two-pass algorithm provides a consistent answer
    auto z1 = x.variance!"twoPass";
    assert(z1.approxEqual(y));

    // And the assumeZeroMean algorithm is way off
    auto z2 = x.variance!"assumeZeroMean";
    assert(z2.approxEqual(1.2e19 / 11));
}

/// Can also set algorithm or output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;
    import mir.math.common: approxEqual;

    //Set population variance, variance algorithm, sum algorithm or output type

    auto a = [1.0, 1e100, 1, -1e100].sliced;
    auto x = a * 10_000;

    bool populationTrueRT = true;
    bool populationFalseRT = false;
    enum PopulationTrueCT = true;

    /++
    Due to Floating Point precision, when centering `x`, subtracting the mean 
    from the second and fourth numbers has no effect. Further, after centering 
    and squaring `x`, the first and third numbers in the slice have precision 
    too low to be included in the centered sum of squares. 
    +/
    assert(x.variance(populationFalseRT).approxEqual(2.0e208 / 3));
    assert(x.variance(populationTrueRT).approxEqual(2.0e208 / 4));
    assert(x.variance(PopulationTrueCT).approxEqual(2.0e208 / 4));

    assert(x.variance!("online").approxEqual(2.0e208 / 3));
    assert(x.variance!("online", "kbn").approxEqual(2.0e208 / 3));
    assert(x.variance!("online", "kb2").approxEqual(2.0e208 / 3));
    assert(x.variance!("online", "precise").approxEqual(2.0e208 / 3));
    assert(x.variance!(double, "online", "precise").approxEqual(2.0e208 / 3));
    assert(x.variance!(double, "online", "precise")(populationTrueRT).approxEqual(2.0e208 / 4));

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [1.0 + 2i, 2 + 3i, 3 + 4i, 4 + 5i].sliced;
    assert(x.variance.approxEqual((0.0+10.0i)/ 3));
}

/// Compute variance along specified dimention of tensors
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
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

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    assert([1.0, 2, 3, 4].variance.approxEqual(5.0 / 3));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.topology: iota, alongDim, map;
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;

    auto x = iota([2, 2], 1);
    auto y = x.alongDim!1.map!variance;
    assert(y.all!approxEqual([0.5, 0.5]));
    static assert(is(meanType!(typeof(y)) == double));
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    assert(x.sliced.variance.approxEqual(54.76562 / 11));
    assert(x.sliced.variance!float.approxEqual(54.76562 / 11));
}

package template stdevType(T)
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

See_also:
    $(LREF, variance),
    $(LREF, VarianceAlgo),
    $(SUBREF sum, Summation)
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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual, sqrt;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual, sqrt;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    assert(x.standardDeviation.approxEqual(sqrt(54.76562 / 11)));
}

/// Standard deviation of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.math.common: approxEqual, sqrt;

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
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;
    import mir.math.common: approxEqual, sqrt;
    import mir.algorithm.iteration: all;

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual, sqrt;

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
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;
    import mir.math.common: approxEqual, sqrt;

    //Set population standard deviation, standardDeviation algorithm, sum algorithm or output type

    auto a = [1.0, 1e100, 1, -1e100].sliced;
    auto x = a * 10_000;

    bool populationTrueRT = true;
    bool populationFalseRT = false;
    enum PopulationTrueCT = true;

    /++
    Due to Floating Point precision, when centering `x`, subtracting the mean 
    from the second and fourth numbers has no effect. Further, after centering 
    and squaring `x`, the first and third numbers in the slice have precision 
    too low to be included in the centered sum of squares. 
    +/
    assert(x.standardDeviation(populationFalseRT).approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation(populationTrueRT).approxEqual(sqrt(2.0e208 / 4)));
    assert(x.standardDeviation(PopulationTrueCT).approxEqual(sqrt(2.0e208 / 4)));

    assert(x.standardDeviation!("online").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!("online", "kbn").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!("online", "kb2").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!("online", "precise").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!(double, "online", "precise").approxEqual(sqrt(2.0e208 / 3)));
    assert(x.standardDeviation!(double, "online", "precise")(populationTrueRT).approxEqual(sqrt(2.0e208 / 4)));

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
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual, sqrt;

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
    import mir.ndslice.fuse: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual, sqrt;
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
    import mir.ndslice.topology: iota, alongDim, map;
    import mir.math.common: approxEqual, sqrt;
    import mir.algorithm.iteration: all;

    auto x = iota([2, 2], 1);
    auto y = x.alongDim!1.map!standardDeviation;
    assert(y.all!approxEqual([sqrt(0.5), sqrt(0.5)]));
    static assert(is(meanType!(typeof(y)) == double));
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual, sqrt;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    assert(x.sliced.standardDeviation.approxEqual(sqrt(54.76562 / 11)));
    assert(x.sliced.standardDeviation!float.approxEqual(sqrt(54.76562 / 11)));
}

/++
Calculates the dispersion of the input.

For an input `x`, this function first centers `x` by subtracting each `e` in `x`
by the result of `centralTendency`, then it transforms the centered values using
the function `transform`, and then finally summarizes that information using
the `summarize` funcion. 

The default functions provided are equivalent to calculating the population
variance. The `centralTendency` default is the `mean` function, which results
in the input being centered about the mean. The default `transform` function
will square the centered values. The default `summarize` function is `mean`,
which will return the mean of the squared centered values.

Params:
    centralTendency: function that will produce the value that the input is centered about, default is `mean`
    transform: function to transform centered values, default squares the centered values
    summarize: function to summarize the transformed centered values, default is `mean`

Returns:
    The dispersion of the input

See_also:
    $(LREF, variance),
    $(LREF, standardDeviation),
    $(LREF, mean),
    $(LREF, median),
    $(LREF, hmean),
    $(LREF, gmean)
+/
template dispersion(
    alias centralTendency = mean,
    alias transform = "a * a",
    alias summarize = mean)
{
    import mir.functional: naryFun;
    import mir.ndslice.slice: Slice, SliceKind, sliced, hasAsSlice;

    static if (__traits(isSame, naryFun!transform, transform))
    {
        /++
        Params:
            slice
        +/
        @fmamath auto dispersion(Iterator, size_t N, SliceKind kind)(
            Slice!(Iterator, N, kind) slice)
        {
            import core.lifetime: move;
            import mir.ndslice.topology: map;

            return summarize(slice.move.center!centralTendency.map!transform);
        }
        
        /// ditto
        @fmamath auto dispersion(T)(scope const T[] ar...)
        {
            return dispersion(ar.sliced);
        }

        /// ditto
        @fmamath auto dispersion(T)(T withAsSlice)
            if (hasAsSlice!T)
        {
            return dispersion(withAsSlice.asSlice);
        }
    }
    else
        alias dispersion = .dispersion!(centralTendency, naryFun!transform, summarize);
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;
    import mir.functional: naryFun;

    assert(dispersion([1.0, 2, 3]).approxEqual(2.0 / 3));

    assert(dispersion([1.0 + 3i, 2, 3]).approxEqual((-4.0 - 6i) / 3));

    assert(dispersion!(mean!float, "a * a", mean!float)([0, 1, 2, 3, 4, 5].sliced(3, 2)).approxEqual(17.5 / 6));
    
    static assert(is(typeof(dispersion!(mean!float, "a ^^ 2", mean!float)([1, 2, 3])) == float));
}

/// Dispersion of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;

    assert(x.dispersion.approxEqual(54.76562 / 12));
}

/// Dispersion of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.math.common: approxEqual;

    auto x = [
        [0.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 0.0]
    ].fuse;

    assert(x.dispersion.approxEqual(54.76562 / 12));
}

/// Column dispersion of matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;

    auto x = [
        [0.0,  1.0, 1.5, 2.0], 
        [3.5, 4.25, 2.0, 7.5],
        [5.0,  1.0, 1.5, 0.0]
    ].fuse;
    auto result = [13.16667 / 3, 7.041667 / 3, 0.1666667 / 3, 30.16667 / 3];

    // Use byDim or alongDim with map to compute dispersion of row/column.
    assert(x.byDim!1.map!dispersion.all!approxEqual(result));
    assert(x.alongDim!0.map!dispersion.all!approxEqual(result));

    // FIXME
    // Without using map, computes the dispersion of the whole slice
    // assert(x.byDim!1.dispersion == x.sliced.dispersion);
    // assert(x.alongDim!0.dispersion == x.sliced.dispersion);
}

/// Can also set functions to change type of dispersion that is used
version(mir_test)
@safe
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual, fabs, sqrt;
    import mir.functional: naryFun;

    auto x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
              2.0, 7.5, 5.0, 1.0, 1.5, 0.0].sliced;
              
    alias square = naryFun!"a * a";

    // Other population variance examples
    assert(x.dispersion.approxEqual(54.76562 / 12));
    assert(x.dispersion!mean.approxEqual(54.76562 / 12));
    assert(x.dispersion!(mean, square).approxEqual(54.76562 / 12));
    assert(x.dispersion!(mean, square, mean).approxEqual(54.76562 / 12));
    
    // Population standard deviation
    assert(x.dispersion!(mean, square, mean).sqrt.approxEqual(sqrt(54.76562 / 12)));
    
    // Mean absolute deviation about the mean
    assert(x.dispersion!(mean, fabs, mean).approxEqual(21.0 / 12));
    //Mean absolute deviation about the median
    assert(x.dispersion!(median, fabs, mean).approxEqual(19.25000 / 12));
    //Median absolute deviation about the mean
    assert(x.dispersion!(mean, fabs, median).approxEqual(1.43750));
    //Median absolute deviation about the median
    assert(x.dispersion!(median, fabs, median).approxEqual(1.25000));
}

/++
For integral slices, pass output type to `centralTendency`, `transform`, and 
`summary` functions as template parameter to ensure output type is correct.
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;
    import mir.functional: naryFun;

    auto x = [0, 1, 1, 2, 4, 4,
              2, 7, 5, 1, 2, 0].sliced;

    alias square = naryFun!"a * a";

    auto y = x.dispersion;
    assert(y.approxEqual(50.91667 / 12));
    static assert(is(typeof(y) == double));

    assert(x.dispersion!(mean!float, square, mean!float).approxEqual(50.91667 / 12));
}

/++
Dispersion works for complex numbers and other user-defined types (provided that
the `centralTendency`, `transform`, and `summary` functions are defined for those
types)
+/
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    auto x = [1.0 + 2i, 2 + 3i, 3 + 4i, 4 + 5i].sliced;
    assert(x.dispersion.approxEqual((0.0+10.0i)/ 4));
}

/// Compute mean tensors along specified dimention of tensors
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.topology: as, iota, alongDim, map, repeat;

    auto x = [
        [0.0, 1, 2],
        [3.0, 4, 5]
    ].fuse;

    assert(x.dispersion.approxEqual(17.5 / 6));

    auto m0 = [2.25, 2.25, 2.25];
    assert(x.alongDim!0.map!dispersion.all!approxEqual(m0));
    assert(x.alongDim!(-2).map!dispersion.all!approxEqual(m0));

    auto m1 = [2.0 / 3, 2.0 / 3];
    assert(x.alongDim!1.map!dispersion.all!approxEqual(m1));
    assert(x.alongDim!(-1).map!dispersion.all!approxEqual(m1));

    assert(iota(2, 3, 4, 5).as!double.alongDim!0.map!dispersion.all!approxEqual(repeat(1800.0 / 2, 3, 4, 5)));
}

/// Arbitrary dispersion
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;
    import mir.functional: naryFun;

    alias square = naryFun!"a * a";

    assert(dispersion(1.0, 2, 3).approxEqual(2.0 / 3));
    assert(dispersion!(mean!float, square, mean!float)(1, 2, 3).approxEqual(2f / 3));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;
    assert([1.0, 2, 3, 4].dispersion.approxEqual(5.0 / 4));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.topology: iota, alongDim, map;
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;

    auto x = iota([2, 2], 1);
    auto y = x.alongDim!1.map!dispersion;
    assert(y.all!approxEqual([0.25, 0.25]));
    static assert(is(meanType!(typeof(y)) == double));
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];

    assert(x.sliced.dispersion.approxEqual(54.76562 / 12));
}

/++
For each `e` of the input, applies `e op m` where `op` by default is "-"
(meaning `e - m`) and `m` is the result of applying `fun` to the input.

This function is equivalent to `center` when passing
`fun = mean!(Summation.appropriate)`.

Params:
    fun = function used to sweep
    op = operation, default is "-"

Returns:
    The input 

See_also:
    $(LREF, center),
    $(LREF, scale)
+/
template sweep(alias fun, string op = "-")
{
    import mir.ndslice.slice: Slice, SliceKind, sliced, hasAsSlice;
    import mir.ndslice.topology: vmap;
    import mir.ndslice.internal: LeftOp, ImplicitlyUnqual;
    /++
    Params:
        slice = slice
    +/
    @fmamath auto sweep(Iterator, size_t N, SliceKind kind)(
        Slice!(Iterator, N, kind) slice)
    {
        import core.lifetime: move;

        auto m = fun(slice.lightScope);
        return .sweep!op(slice.move, m);
    }
    
    /// ditto
    @fmamath auto sweep(T)(T[] array)
    {
        return sweep(array.sliced);
    }

    /// ditto
    @fmamath auto sweep(T)(T withAsSlice)
        if (hasAsSlice!T)
    {
        return sweep(withAsSlice.asSlice);
    }
}

/++
Params:
    op = operation, default is "-"
+/
template sweep(string op = "-")
{
    /++
    Params:
        slice = slice
        m = value to pass to vmap
    +/
    @fmamath auto sweep(Iterator, size_t N, SliceKind kind, T)(
               Slice!(Iterator, N, kind) slice, T m)
    {
        import core.lifetime: move;
        import mir.ndslice.topology: vmap;
        import mir.ndslice.internal: LeftOp, ImplicitlyUnqual;

        return slice.move.vmap(LeftOp!(op, ImplicitlyUnqual!T)(m));
    }
        
    /// ditto
    @fmamath auto sweep(T)(T[] array, T m)
    {
        import mir.ndslice.slice: sliced;

        return sweep(array.sliced, m);
    }

    /// ditto
    @fmamath auto sweep(T, U)(T withAsSlice, U m)
        if (hasAsSlice!T)
    {
        return sweep(withAsSlice.asSlice, m);
    }
}

/// Sweep vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    static double f(T)(T x) {
        return 3.5;
    }

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;
    assert(x.sweep!f.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(x.sweep(3.5).all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(x.sweep!(f, "+").all!approxEqual([4.5, 5.5, 6.5, 7.5, 8.5, 9.5]));
}

/// Sweep dynamic array
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    static double f(T)(T x) {
        return 3.5;
    }

    auto x = [1.0, 2, 3, 4, 5, 6];
    assert(x.sweep!f.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(x.sweep(3.5).all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(x.sweep!(f, "+").all!approxEqual([4.5, 5.5, 6.5, 7.5, 8.5, 9.5]));
}

/// Sweep matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    static double f(T)(T x) {
        return 3.5;
    }

    auto x = [
        [1.0, 2, 3],
        [4.0, 5, 6]
    ].fuse;

    auto y0 = [
        [-2.5, -1.5, -0.5],
        [ 0.5,  1.5,  2.5]
    ];

    auto y1 = [
        [4.5, 5.5, 6.5],
        [7.5, 8.5, 9.5]
    ];

    assert(x.sweep!f.all!approxEqual(y0));
    assert(x.sweep(3.5).all!approxEqual(y0));
    assert(x.sweep!(f, "+").all!approxEqual(y1));
}

/// Column sweep matrix
version(mir_test)
@safe pure
unittest
{
    import mir.algorithm.iteration: all, equal;
    import mir.math.common: approxEqual;
    import mir.ndslice: fuse;
    import mir.ndslice.topology: alongDim, byDim, map;

    static double f(T)(T x) {
        return 0.5 * (x[0] +x[1]);
    }

    auto x = [
        [20.0, 100.0, 2000.0],
        [10.0,   5.0,    2.0]
    ].fuse;

    auto result = [
        [ 5.0,  47.5,  999],
        [-5.0, -47.5, -999]
    ].fuse;

    // Use byDim with map to sweep mean of row/column.
    auto xSweepByDim = x.byDim!1.map!(sweep!f);
    auto resultByDim = result.byDim!1;
    assert(xSweepByDim.equal!(equal!approxEqual)(resultByDim));

    auto xSweepAlongDim = x.alongDim!0.map!(sweep!f);
    auto resultAlongDim = result.alongDim!0;
    assert(xSweepAlongDim.equal!(equal!approxEqual)(resultAlongDim));
}

/// Can also pass arguments to sweep function
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    static double f(T)(T x, double a) {
        return a;
    }

    static double g(double a, T)(T x) {
        return a;
    }

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;
    assert(x.sweep!(a => f(a, 3.5)).all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(x.sweep!(a => f(a, 3.5), "+").all!approxEqual([4.5, 5.5, 6.5, 7.5, 8.5, 9.5]));
    assert(x.sweep!(a => g!3.5(a)).all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(x.sweep!(a => g!3.5(a), "+").all!approxEqual([4.5, 5.5, 6.5, 7.5, 8.5, 9.5]));
}

/++
Centers the input.

By default, the input is centered by the mean. A custom function may also be
provided using `centralTendency`.

In addition, overloads are provided to center with variables `m`, which
corresponds to the result of `centralTendency`.

Params:
    centralTendency = function used to center input

Returns:
    The centered result

See_also:
    $(LREF, mean)
    $(LREF, median)
    $(LREF, gmean)
    $(LREF, hmean)
+/
template center(alias centralTendency = mean!(Summation.appropriate))
{
    alias center = sweep!(centralTendency, "-");
}

/++
Params:
    slice = slice
    m = value to subtract from slice
+/
auto center(Iterator, size_t N, SliceKind kind, T)(
    Slice!(Iterator, N, kind) slice, T m)
{
    import core.lifetime: move;

    return slice.move.sweep!("-")(m);
}
    
/// ditto
auto center(T)(T[] array, T m)
{
    import mir.ndslice.slice: sliced;
    return center(array.sliced, m);
}

/// ditto
auto center(T, U)(T withAsSlice, U m)
    if (hasAsSlice!T)
{
    return center(withAsSlice.asSlice, m);
}

/// Center vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;
    assert(x.center.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    assert(x.center(3.5).all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
    
    // Can center using different functions
    assert(x.center!hmean.all!approxEqual([-1.44898, -0.44898, 0.55102, 1.55102, 2.55102, 3.55102]));
    assert(x.center!gmean.all!approxEqual([-1.99379516, -0.99379516, 0.00620483, 1.00620483, 2.00620483, 3.00620483]));
    assert(x.center!median.all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
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
    assert(x.center(3.5).all!approxEqual([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]));
}

/// Center matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    
    auto x = [
        [0.0, 1, 2], 
        [3.0, 4, 5]
    ].fuse;
    
    assert(x.center.all!approxEqual([[-2.5, -1.5, -0.5], [ 0.5,  1.5,  2.5]]));
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
    assert(xCenterAlongDim.equal!(equal!approxEqual)(resultAlongDim));
}

/// Can also pass arguments to average function used by center
version(mir_test)
pure @safe nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    //Set sum algorithm
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
Scales the input.

By default, the input is first centered using the mean of the input. A custom
function may also be provided using `centralTendency`. The centered input is
then divided by the sample standard deviation of the input. A custom function
may also be provided using `dispersion`.

Overloads are also provided to scale with variables `m` and `d`, which
correspond to the results of `centralTendency` and `dispersion`. This function
is equivalent to `center` when passing `d = 1`.

Params:
    centralTendency = function used to center input, default is `mean`
    dispersion = function used to , default is `dispersion`

Returns:
    The scaled result

See_also:
    $(LREF, center),
    $(LREF, VarianceAlgo)
    $(SUBREF sum, Summation)
    $(LREF, mean),
    $(LREF, standardDeviation),
    $(LREF, median),
    $(LREF, gmean),
    $(LREF, hmean),
    $(LREF, variance),
    $(LREF, dispersion)
+/
template scale(alias centralTendency = mean!(Summation.appropriate),
               alias dispersion = standardDeviation!(VarianceAlgo.online, Summation.appropriate))
{
    import mir.ndslice.slice: Slice, SliceKind, sliced, hasAsSlice;
    /++
    Params:
        slice = slice
    +/
    @fmamath auto scale(Iterator, size_t N, SliceKind kind)(
        Slice!(Iterator, N, kind) slice)
    {
        import core.lifetime: move;

        auto m = centralTendency(slice.lightScope);
        auto d = dispersion(slice.lightScope);
        return .scale!(Iterator, N, kind, typeof(m))(slice.move, m, d);
    }
    
    /// ditto
    @fmamath auto scale(T)(T[] array)
    {
        return scale(array.sliced);
    }

    /// ditto
    @fmamath auto scale(T)(T withAsSlice)
        if (hasAsSlice!T)
    {
        return scale(withAsSlice.asSlice);
    }
}

/++
Params:
    slice = slice
    m = value to subtract from slice
    d = value to divide slice by
+/
@fmamath auto scale(Iterator, size_t N, SliceKind kind, T, U)(
           Slice!(Iterator, N, kind) slice, T m, U d)
{
    import core.lifetime: move;
    import mir.ndslice.topology: vmap;
    import mir.ndslice.internal: LeftOp, ImplicitlyUnqual;

    return slice.move.sweep!"-"(m).sweep!"/"(d);
}
    
/// ditto
@fmamath auto scale(T, U)(T[] array, T m, U d)
{
    import mir.ndslice.slice: sliced;

    return scale(array.sliced, m, d);
}

/// ditto
@fmamath auto scale(T, U, V)(T withAsSlice, U m, V d)
    if (hasAsSlice!T)
{
    return scale(withAsSlice.asSlice, m, d);
}

/// Scale vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;

    assert(x.scale.all!approxEqual([-1.336306, -0.801784, -0.267261, 0.267261, 0.801784, 1.336306]));
    assert(x.scale(3.5, 1.87083).all!approxEqual([-1.336306, -0.801784, -0.267261, 0.267261, 0.801784, 1.336306]));
    
    // Can scale using different `centralTendency` functions
    assert(x.scale!hmean.all!approxEqual([-0.774512, -0.23999, 0.294533, 0.829055, 1.363578, 1.898100]));
    assert(x.scale!gmean.all!approxEqual([-1.065728, -0.531206, 0.003317, 0.537839, 1.072362, 1.606884]));
    assert(x.scale!median.all!approxEqual([-1.336306, -0.801784, -0.267261, 0.267261, 0.801784, 1.336306]));
    
    // Can scale using different `centralTendency` and `dispersion` functions
    assert(x.scale!(mean, a => a.standardDeviation(true)).all!approxEqual([-1.46385, -0.87831, -0.29277, 0.29277, 0.87831, 1.46385]));
    assert(x.scale!(hmean, a => a.standardDeviation(true)).all!approxEqual([-0.848436, -0.262896, 0.322645, 0.908185, 1.493725, 2.079265]));
    assert(x.scale!(gmean, a => a.standardDeviation(true)).all!approxEqual([-1.167447, -0.581907, 0.003633, 0.589173, 1.174713, 1.760253]));
    assert(x.scale!(median, a => a.standardDeviation(true)).all!approxEqual([-1.46385, -0.87831, -0.29277, 0.29277, 0.87831, 1.46385]));
}

/// Scale dynamic array
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    auto x = [1.0, 2, 3, 4, 5, 6];
    assert(x.scale.all!approxEqual([-1.336306, -0.801784, -0.267261, 0.267261, 0.801784, 1.336306]));
    assert(x.scale(3.5, 1.87083).all!approxEqual([-1.336306, -0.801784, -0.267261, 0.267261, 0.801784, 1.336306]));
}

/// Scale matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    
    auto x = [
        [1.0, 2, 3], 
        [4.0, 5, 6]
    ].fuse;
    
    assert(x.scale.all!approxEqual([[-1.336306, -0.801784, -0.267261], [0.267261, 0.801784, 1.336306]]));
    assert(x.scale(3.5, 1.87083).all!approxEqual([[-1.336306, -0.801784, -0.267261], [0.267261, 0.801784, 1.336306]]));
}

/// Column scale matrix
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
        [ 0.707107,  0.707107,  0.707107],
        [-0.707107, -0.707107, -0.707107]
    ].fuse;

    // Use byDim with map to scale by row/column.
    auto xScaleByDim = x.byDim!1.map!scale;
    auto resultByDim = result.byDim!1;
    assert(xScaleByDim.equal!(equal!approxEqual)(resultByDim));

    auto xCenterAlongDim = x.alongDim!0.map!scale;
    auto resultAlongDim = result.alongDim!0;
    assert(xScaleByDim.equal!(equal!approxEqual)(resultAlongDim));
}

/// Can also pass arguments to `mean` and `standardDeviation` functions used by scale
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;

    //Set sum algorithm
    auto a = [1, 1e100, 1, -1e100];

    auto x = a.sliced * 10_000;

    auto result = [6.123724e-101, 1.224745, 6.123724e-101, -1.224745].sliced;

    assert(x.scale!(mean!"kbn", standardDeviation!("online", "kbn")).all!approxEqual(result));
    assert(x.scale!(mean!"kb2", standardDeviation!("online", "kb2")).all!approxEqual(result));
    assert(x.scale!(mean!"precise", standardDeviation!("online", "precise")).all!approxEqual(result));
}

/++
Computes the Z-score of the input.

The Z-score is computed by first calculating the mean and standard deviation of
the input, by default in one pass, and then scaling the input using those values.

Returns:
    The z-score of the input

See_also:
    $(LREF scale),
    $(LREF mean),
    $(LREF standardDeviation),
    $(LREF variance)
+/
template zscore(F, 
                VarianceAlgo varianceAlgo = VarianceAlgo.online,
                Summation summation = Summation.appropriate)
{
    /++
    Params:
        slice = slice
        isPopulation = true if population standard deviation, false is sample (default)
    +/
    @fmamath auto zscore(Iterator, size_t N, SliceKind kind)(
        Slice!(Iterator, N, kind) slice, 
        bool isPopulation = false)
    {
        import core.lifetime: move;
        import mir.math.common: sqrt;

        alias G = meanType!F;
        alias T = typeof(slice);
        auto varianceAccumulator = VarianceAccumulator!(
            G, varianceAlgo, ResolveSummationType!(summation, T, G))(
            slice.lightScope);
        return scale(slice,
                     varianceAccumulator.mean,
                     varianceAccumulator.variance(isPopulation).sqrt);
    }
    
    /// ditto
    @fmamath auto zscore(T)(T[] array, bool isPopulation = false)
    {
        import mir.ndslice.slice: sliced;

        return zscore(array.sliced, isPopulation);
    }

    /// ditto
    @fmamath auto zscore(T)(T withAsSlice, bool isPopulation = false)
        if (hasAsSlice!T)
    {
        return zscore(withAsSlice.asSlice, isPopulation);
    }
}

///
template zscore(VarianceAlgo varianceAlgo = VarianceAlgo.online,
                Summation summation = Summation.appropriate)
{
    /// ditto
    @fmamath auto zscore(Iterator, size_t N, SliceKind kind)(
        Slice!(Iterator, N, kind) slice, 
        bool isPopulation = false)
    {
        import core.lifetime: move;
        alias F = meanType!(Slice!(Iterator, N, kind));
        return .zscore!(F, varianceAlgo, summation)(slice.move, isPopulation);
    }

    /// ditto
    @fmamath auto zscore(T)(T[] array, bool isPopulation = false)
    {
        alias F = meanType!(T[]);
        return .zscore!(F, varianceAlgo, summation)(array, isPopulation);
    }

    /// ditto
    @fmamath auto zscore(T)(T withAsSlice, bool isPopulation = false)
        if (hasAsSlice!T)
    {
        alias F = meanType!(T);
        return .zscore!(F, varianceAlgo, summation)(withAsSlice, isPopulation);
    }
}

/// ditto
template zscore(F, string varianceAlgo, string summation = "appropriate")
{
    mixin("alias zscore = .zscore!(F, VarianceAlgo." ~ varianceAlgo ~ ", Summation." ~ summation ~ ");");
}

/// ditto
template zscore(string varianceAlgo, string summation = "appropriate")
{
    mixin("alias zscore = .zscore!(VarianceAlgo." ~ varianceAlgo ~ ", Summation." ~ summation ~ ");");
}

/// zscore vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    auto x = [1.0, 2, 3, 4, 5, 6].sliced;

    assert(x.zscore.all!approxEqual([-1.336306, -0.801784, -0.267261, 0.267261, 0.801784, 1.336306]));
    assert(x.zscore(true).all!approxEqual([-1.46385, -0.87831, -0.29277, 0.29277, 0.87831, 1.46385]));
}

/// zscore dynamic array
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;

    auto x = [1.0, 2, 3, 4, 5, 6];
    assert(x.zscore.all!approxEqual([-1.336306, -0.801784, -0.267261, 0.267261, 0.801784, 1.336306]));
    assert(x.zscore(true).all!approxEqual([-1.46385, -0.87831, -0.29277, 0.29277, 0.87831, 1.46385]));
}

/// zscore matrix
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    
    auto x = [
        [1.0, 2, 3], 
        [4.0, 5, 6]
    ].fuse;
    
    assert(x.zscore.all!approxEqual([[-1.336306, -0.801784, -0.267261], [0.267261, 0.801784, 1.336306]]));
    assert(x.zscore(true).all!approxEqual([[-1.46385, -0.87831, -0.29277], [0.29277, 0.87831, 1.46385]]));
}

/// Column zscore matrix
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
        [ 0.707107,  0.707107,  0.707107],
        [-0.707107, -0.707107, -0.707107]
    ].fuse;

    // Use byDim with map to scale by row/column.
    auto xScaleByDim = x.byDim!1.map!zscore;
    auto resultByDim = result.byDim!1;
    assert(xScaleByDim.equal!(equal!approxEqual)(resultByDim));

    auto xCenterAlongDim = x.alongDim!0.map!zscore;
    auto resultAlongDim = result.alongDim!0;
    assert(xScaleByDim.equal!(equal!approxEqual)(resultAlongDim));
}

/// Can control how `mean` and `standardDeviation` are calculated and output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;
    import mir.algorithm.iteration: all;
    import mir.ndslice.topology: repeat;

    //Set sum algorithm or output type
    auto a = [1, 1e100, 1, -1e100];

    auto x = a.sliced * 10_000;

    auto result = [6.123724e-101, 1.224745, 6.123724e-101, -1.224745].sliced;

    assert(x.zscore!("online", "kbn").all!approxEqual(result));
    assert(x.zscore!("online", "kb2").all!approxEqual(result));
    assert(x.zscore!("online", "precise").all!approxEqual(result));
    assert(x.zscore!(double, "online", "precise").all!approxEqual(result));

    auto y = [uint.max, uint.max / 2, uint.max / 3].sliced;
    assert(y.zscore!ulong.all!approxEqual([1.120897, -0.320256, -0.800641]));
}

/++
A linear regression model with a single explanatory variable.
+/
template simpleLinearRegression(Summation summation = Summation.kbn)
{
    import mir.ndslice.slice;
    import std.range.primitives: isInputRange;

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
