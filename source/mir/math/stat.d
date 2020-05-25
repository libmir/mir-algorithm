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
import mir.ndslice.slice: Slice, SliceKind;
import mir.math.common: fmamath;
import mir.math.sum;
import mir.math.numeric: ProdAlgo;
import mir.primitives;
import std.traits: isArray, isFloatingPoint, isMutable, isIterable;

// version = mir_test_topN;

/++
Output range for mean.
+/
struct MeanAccumulator(T, Summation summation) 
    if (isMutable!T)
{
    ///
    size_t count;
    ///
    Summator!(T, summation) sumAccumulator;

    ///
    F mean(F = T)() @property
    {
        return cast(F) sumAccumulator.sum / cast(F) count;
    }

    ///
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        static if (hasShape!Range)
        {
            count += r.elementCount;
            sumAccumulator.put(r);
        }
        else
        {
            foreach(x; r)
            {
                count++;
                sumAccumulator.put(x);
            }
        }
    }

    ///
    void put()(T x)
    {
        count++;
        sumAccumulator.put(x);
    }
}

///
version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.slice: sliced;

    MeanAccumulator!(double, Summation.pairwise) x;
    x.put([0.0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    x.put(5);
    assert(x.mean == 2.5);
}

version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.slice: sliced;

    MeanAccumulator!(float, Summation.pairwise) x;
    x.put([0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    x.put(5);
    assert(x.mean == 2.5);
}

/++
Computes the average of the input.

Returns:
    The average of all the elements in the input.

See_also: $(SUBREF sum, Summation)
+/
template mean(F, Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range, must be finite iterable
    +/
    @fmamath F mean(Range)(Range r)
        if (isIterable!Range)
    {
        MeanAccumulator!(F, ResolveSummationType!(summation, Range, F)) mean;
        mean.put(r.move);
        return mean.mean;
    }
    
    /++
    Params:
        val = values
    +/
    @fmamath F mean(scope const F[] val...)
    {
        MeanAccumulator!(F, ResolveSummationType!(summation, const(F)[], F)) mean;
        mean.put(val);
        return mean.mean;
    }
}

/// ditto
template mean(Summation summation = Summation.appropriate)
{
    import std.traits: CommonType;

    /++
    Params:
        r = range, must be finite iterable
    +/
    @fmamath sumType!Range mean(Range)(Range r)
        if (isIterable!Range)
    {
        return .mean!(sumType!Range, summation)(r.move);
    }
    
    /++
    Params:
        val = values
    +/
    @fmamath CommonType!T mean(T...)(T val)
        if (T.length > 0 &&
            !is(CommonType!T == void))
    {
        return .mean!(CommonType!T, summation)(val);
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
@safe pure nothrow unittest
{
    import mir.ndslice.slice: sliced;

    assert(mean([1.0, 2, 3]) == 2);
    assert(mean([1.0 + 3i, 2, 3]) == 2 + 1i);
    
    assert(mean!float([0, 1, 2, 3, 4, 5].sliced(3, 2)) == 2.5);
    
    assert(is(typeof(mean!float([1, 2, 3])) == float));
}

/// Mean of vector
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];
    assert(x.sliced.mean == 29.25 / 12);
}

/// Mean of matrix
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];
    assert(x.sliced(2, 6).mean == 29.25 / 12);
}

/// Column mean of matrix
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: alongDim, byDim, map;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];
    static immutable result = [1, 4.25, 3.25, 1.5, 2.5, 2.125];

    // Use byDim or alongDim with map to compute mean of row/column.
    assert(x.sliced(2, 6).byDim!1.map!mean == result);
    assert(x.sliced(2, 6).alongDim!0.map!mean == result);

    // FIXME
    // Without using map, computes the mean of the whole slice
    // assert(x.sliced(2, 6).byDim!1.mean == x.sliced.mean);
    // assert(x.sliced(2, 6).alongDim!0.mean == x.sliced.mean);
}

/// Can also set algorithm or output type
version(mir_test)
@safe @nogc pure nothrow

unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: map, repeat;

    //Set sum algorithm or output type

    static immutable a = [1, 1e100, 1, -1e100];

    auto x = a.sliced * 10_000;
    assert(x.mean!"kbn" == 20_000 / 4);
    assert(x.mean!"kb2" == 20_000 / 4);
    assert(x.mean!"precise" == 20_000 / 4);
    assert(x.mean!(double, "precise") == 20_000.0 / 4);

    auto y = uint.max.repeat(3);
    assert(y.mean!ulong == 12884901885 / 3);
}

/++
For integral slices, pass output type as template parameter to ensure output
type is correct
+/
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;

    static immutable x = [0, 1, 1, 2, 4, 4,
                          2, 7, 5, 1, 2, 0];
    assert(approxEqual(x.sliced.mean!double, 29.0 / 12, 1.0e-10));
}

/// Mean works for complex numbers (and other user-defined types)
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable cdouble[] x = [1.0 + 2i, 2 + 3i, 3 + 4i, 4 + 5i];
    static immutable cdouble result = 2.5 + 3.5i;
    assert(x.sliced.mean == result);
}

/// Compute mean tensors along specified dimention of tensors
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice: alongDim, iota, as, map;
    /*
      [[0,1,2],
       [3,4,5]]
     */
    auto x = iota(2, 3).as!double;
    assert(x.mean == (5.0 / 2.0));

    static immutable m0 = [(0.0+3.0)/2.0, (1.0+4.0)/2.0, (2.0+5.0)/2.0];
    assert(x.alongDim!0.map!mean == m0);
    assert(x.alongDim!(-2).map!mean == m0);

    static immutable m1 = [(0.0+1.0+2.0)/3.0, (3.0+4.0+5.0)/3.0];
    assert(x.alongDim!1.map!mean == m1);
    assert(x.alongDim!(-1).map!mean == m1);

    assert(iota(2, 3, 4, 5).as!double.alongDim!0.map!mean == iota([3, 4, 5], 3 * 4 * 5 / 2));
}

/// Arbitrary mean
version(mir_test)
@safe pure nothrow @nogc unittest
{
    assert(mean(1.0, 2, 3) == 2);
    assert(mean!float(1, 2, 3) == 2);
}

version(mir_test)
@safe pure nothrow unittest
{
    assert([1.0, 2, 3, 4].mean == 2.5);
}

/++
Computes the harmonic mean of a range.

See_also: $(SUBREF sum, Summation)
+/
template hmean(F, Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    Returns:
        harmonic mean of the range
    +/
    @fmamath F hmean(Range)(Range r)
        if (isIterable!Range)
    {
        import mir.ndslice.topology: map;
        static if (summation == Summation.fast && __traits(compiles, r.move.map!"1.0 / a"))
        {
            return 1.0 / r.move.map!"1.0 / a".mean!(F, summation);
        }
        else
        {
            MeanAccumulator!(F, ResolveSummationType!(summation, Range, F)) imean;
            foreach (e; r)
                imean.put(1.0 / e);
            return 1.0 / imean.mean;
        }
    }
}

/// ditto
template hmean(Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    Returns:
        harmonic mean of the range
    +/
    @fmamath sumType!Range hmean(Range)(Range r)
        if (isIterable!Range)
    {
        return .hmean!(typeof(1.0 / sumType!Range.init), summation)(r.move);
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
pure @safe nothrow @nogc
unittest
{
    import mir.math.common: approxEqual;

    static immutable x = [20.0, 100.0, 2000.0, 10.0, 5.0, 2.0];

    assert(x.hmean.approxEqual(6.97269));
}

/// Harmonic mean of matrix
version(mir_test)
pure @safe
unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.fuse: fuse;

    auto x = [[20.0, 100.0, 2000.0], [10.0, 5.0, 2.0]].fuse;

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
pure @safe nothrow @nogc
unittest
{
    import mir.ndslice.topology: repeat;
    import mir.math.common: approxEqual;

    //Set sum algorithm or output type
    static immutable x = [1, 1e-100, 1, -1e-100];

    assert(x.hmean!"kb2".approxEqual(2));
    assert(x.hmean!"precise".approxEqual(2));

    //Provide the summation type
    assert(float.max.repeat(3).hmean!(double, "fast").approxEqual(float.max));
}

private
auto pow(T, U)(in T x, in U power) {
    static if (is(U : int)) {
        import mir.math.common: powi;
        return powi(x, power);
    } else static if (isFloatingPoint!U && is(T == U)) {
        import mir.math.common: pow;
        return pow(x, power);
    } else {
        import std.math: pow;
        return pow(x, power);
    }
}

/++
Output range for gmean.
+/
struct GMeanAccumulator(T, ProdAlgo prodAlgo) 
    if (isMutable!T)
{
    import mir.math.numeric: ProdAccumulator;

    ///
    size_t count;
    ///
    ProdAccumulator!(T, prodAlgo) prodAccumulator;

    ///
    F gmean(F = T)() @property
    {
        return pow(cast(F) prodAccumulator.prod, cast(F) 1 / cast(F) count);
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

    GMeanAccumulator!(double, ProdAlgo.separateExponentAccumulation) x;
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

    GMeanAccumulator!(float, ProdAlgo.separateExponentAccumulation) x;
    x.put([1, 2, 3, 4].sliced);
    assert(x.gmean.approxEqual(2.21336384));
    x.put(5);
    assert(x.gmean.approxEqual(2.60517108));
}

package template gmeanType(T)
{
    import mir.math.common: pow;
    import mir.math.numeric: prodType;

    alias U = prodType!T;
    static if (__traits(compiles, {
        auto temp = U.init * U.init;
        auto a = pow(temp, cast(U) 1 / cast(U) 2);
        temp *= U.init;
        a = pow(temp, cast(U) 1 / cast(U) 3);
    }))
        alias gmeanType = typeof((U.init * U.init) ^^ (cast(U) 1 / cast(U) 2));
    else
        static assert(0, "Can't gmean elements of type " ~ U.stringof);
}

/++
Computes the geometric average of the input.

Returns:
    The geometric average of all the elements in the input.

See_also: $(SUBREF prod, ProdAlgo)
+/
template gmean(F, ProdAlgo prodAlgo = ProdAlgo.appropriate)
{
    import mir.math.numeric: ResolveProdAlgoType;

    /++
    Params:
        r = range, must be finite iterable
    +/
    @fmamath F gmean(Range)(Range r)
        if (isIterable!Range)
    {
        GMeanAccumulator!(F, ResolveProdAlgoType!(prodAlgo, F)) gmean;
        gmean.put(r.move);
        return gmean.gmean;
    }
    
    /++
    Params:
        val = values
    +/
    @fmamath F gmean(scope const F[] val...)
    {
        GMeanAccumulator!(F, ResolveProdAlgoType!(prodAlgo, F)) gmean;
        gmean.put(val);
        return gmean.gmean;
    }
}

/// ditto
template gmean(ProdAlgo prodAlgo = ProdAlgo.appropriate)
{
    import std.traits: CommonType;

    /++
    Params:
        r = range, must be finite iterable
    +/
    @fmamath gmeanType!Range gmean(Range)(Range r)
        if (isIterable!Range)
    {
        alias F = typeof(return);
        return .gmean!(F, prodAlgo)(r.move);
    }
    
    /++
    Params:
        val = values
    +/
    @fmamath gmeanType!(CommonType!T) gmean(T...)(T val)
        if (T.length > 0 &&
            !is(CommonType!T == void))
    {
        alias F = typeof(return);
        return .gmean!(F, prodAlgo)(val);
    }
}

/// ditto
template gmean(F, string prodAlgo)
{
    mixin("alias gmean = .gmean!(F, ProdAlgo." ~ prodAlgo ~ ");");
}

/// ditto
template gmean(string prodAlgo)
{
    mixin("alias gmean = .gmean!(ProdAlgo." ~ prodAlgo ~ ");");
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
    
    assert(is(typeof(gmean!float([1, 2, 3])) == float));
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

/// Can also set algorithm or output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: repeat;
    import mir.math.common: approxEqual;

    auto x = [5120.0, 7340032, 32, 3758096384].sliced;

    assert(x.gmean!"naive".approxEqual(259281.45295212));
    assert(x.gmean!(float, "separateExponentAccumulation").approxEqual(259281.45295212));

    auto y = uint.max.repeat(3);
    assert(y.gmean!float.approxEqual(cast(float) uint.max));
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
    import mir.math.common: approxEqual;

    auto x = [5, 1, 1, 2, 4, 4,
              2, 7, 5, 1, 2, 10].sliced;
    assert(x.gmean!double.approxEqual(2.79160522));
}

/// Mean works for user-defined types, provided exponentiation works for them
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


/++
Computes the median of `slice`.

Can also pass a a flag `allowModify` that allows the input slice to be modified.
By default, a copy is made. 

Returns:
    the median of the slice

See_also: $(SUBREF mean)
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
version(mir_test_topN)
@safe
unittest {
    import mir.ndslice.slice: sliced;

    auto x0 = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10, 5].sliced;
    assert(x0.median == 5);

    auto x1 = [9.0, 1, 0, 2, 3, 4, 6, 8, 7, 10].sliced;
    assert(x1.median == 5);
}

/// Median of matrix
version(mir_test_topN)
@safe
unittest {
    import mir.ndslice.fuse: fuse;

    auto x0 = [
        [9.0, 1, 0, 2,  3], 
        [4.0, 6, 8, 7, 10]
    ].fuse;

    assert(x0.median == 5);
}

/// Row median of matrix
version(mir_test_topN)
@safe
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
version(mir_test_topN)
@safe
unittest {
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
version(mir_test_topN)
@safe
unittest {
    import mir.ndslice.slice: sliced;

    auto x = [9, 1, 0, 2, 3, 4, 6, 8, 7, 10].sliced;
    assert(x.median!float == 5);
}

version(mir_test)
@safe
unittest {
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
@safe
unittest {
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
unittest {
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
Centers `slice`, which must be a finite iterable.

By default, `slice` is centered by the mean. A custom function may also be provided
using `centralTendency`.

Returns:
    The elements in the slice with the average subtracted from them.
+/
template center(alias centralTendency = mean!(Summation.appropriate))
{
    import mir.ndslice.slice: Slice, SliceKind, sliced, hasAsSlice;
    /++
    Params:
        slice = slice
    +/
    auto center(Iterator, size_t N, SliceKind kind)(
        Slice!(Iterator, N, kind) slice)
    {
        import core.lifetime: move;
        import mir.ndslice.topology: vmap;
        import mir.ndslice.internal: LeftOp, ImplicitlyUnqual;

        auto m = centralTendency(slice.lightScope);
        alias T = typeof(m);
        return slice.move.vmap(LeftOp!("-", ImplicitlyUnqual!T)(m));
    }
    
    /// ditto
    auto center(T)(T[] array)
    {
        return center(array.sliced);
    }

    /// ditto
    auto center(T)(T withAsSlice)
        if (hasAsSlice!T)
    {
        return center(withAsSlice.asSlice);
    }
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
    
    // Can center using different functions
    assert(x.center!hmean.all!approxEqual([-1.44898, -0.44898, 0.55102, 1.55102, 2.55102, 3.55102]));
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
    import mir.ndslice: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    
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
pure @safe
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
    import mir.algorithm.iteration: all;
    import mir.ndslice.topology: repeat;
    import mir.math.common: approxEqual;

    //Set sum algorithm or output type
    auto a = [1, 1e100, 1, -1e100];

    auto x = a.sliced * 10_000;
    auto result = [5000, 1e104 - 5000, 5000, -1e104 - 5000].sliced;

    assert(x.center!(mean!"kbn").all!approxEqual(result));
    assert(x.center!(mean!"kb2").all!approxEqual(result));
    assert(x.center!(mean!"precise").all!approxEqual(result));
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
@safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    static immutable x = [0, 1, 2, 3];
    static immutable y = [-1, 0.2, 0.9, 2.1];
    auto params = x.simpleLinearRegression(y);
    assert(params[0].approxEqual(-0.95)); // shift
    assert(params[1].approxEqual(1)); // slope
}
