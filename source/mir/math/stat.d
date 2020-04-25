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
import mir.math.common: fmamath;
import mir.math.sum;
import mir.primitives;
import std.range.primitives: isInputRange;
import std.traits: isArray, isFloatingPoint, isMutable, isIterable;

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
    import mir.ndslice.slice : sliced;

    MeanAccumulator!(double, Summation.pairwise) x;
    x.put([0.0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    x.put(5);
    assert(x.mean == 2.5);
}

version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.slice : sliced;

    MeanAccumulator!(float, Summation.pairwise) x;
    x.put([0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    x.put(5);
    assert(x.mean == 2.5);
}

/++
Computes the average of `r`, which must be a finite iterable.

Returns:
    The average of all the elements in the range r.
+/
template mean(F, Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    +/
    F mean(Range)(Range r)
        if (isIterable!Range)
    {
        MeanAccumulator!(F, ResolveSummationType!(summation, Range, sumType!Range)) mean;
        mean.put(r.move);
        return mean.mean;
    }
}

/// ditto
template mean(Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    +/
    sumType!Range mean(Range)(Range r)
        if (isIterable!Range)
    {
        return .mean!(sumType!Range, summation)(r.move);
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
    import mir.ndslice.slice : sliced;

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
    import mir.ndslice.slice : sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];
    assert(x.sliced.mean == 29.25 / 12);
}

/// Mean of matrix
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice : sliced;

    static immutable x = [0.0, 1.0, 1.5, 2.0, 3.5, 4.25,
                          2.0, 7.5, 5.0, 1.0, 1.5, 0.0];
    assert(x.sliced(2, 6).mean == 29.25 / 12);
}

/// Column mean of matrix
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice : sliced;
    import mir.ndslice.topology : alongDim, byDim, map;

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
    import mir.ndslice.slice : sliced;
    import std.math : approxEqual;

    static immutable x = [0, 1, 1, 2, 4, 4,
                          2, 7, 5, 1, 2, 0];
    assert(approxEqual(x.sliced.mean!double, 29.0 / 12, 1.0e-10));
}

/// Mean works for complex numbers (and other user-defined types)
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice : sliced;

    static immutable cdouble[] x = [1.0 + 2i, 2 + 3i, 3 + 4i, 4 + 5i];
    static immutable cdouble result = 2.5 + 3.5i;
    assert(x.sliced.mean == result);
}

/// Compute mean tensors along specified dimention of tensors
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice : alongDim, iota, as, map;
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

///
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice : sliced;
    import mir.ndslice.topology : alongDim, byDim, map;

    static immutable x      = [0.0, 1.00, 1.50, 2.0, 3.5, 4.250,
                               2.0, 7.50, 5.00, 1.0, 1.5, 0.000];
    static immutable result = [1.0, 4.25, 3.25, 1.5, 2.5, 2.125];

    // Use byDim or alongDim with map to compute mean of row/column.
    assert(x.sliced(2, 6).byDim!1.map!mean == result);
    assert(x.sliced(2, 6).alongDim!0.map!mean == result);
}

version(mir_test)
@safe pure nothrow unittest
{
    assert([1.0, 2, 3, 4].mean == 2.5);
}

/++
A linear regression model with a single explanatory variable.
+/
template simpleLinearRegression(Summation summation = Summation.kbn)
{
    import mir.ndslice.slice;

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
        enum summationX = !__traits(isIntegral, X) ? summation : Summation.naive;
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
