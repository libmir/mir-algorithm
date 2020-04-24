/++
This module contains base statistical algorithms.

Note that used specialized summing algorithms execute more primitive operations
than vanilla summation. Therefore, if in certain cases maximum speed is required
at expense of precision, one can use $(REF_ALTTEXT $(TT Summation.fast), Summation.fast, mir, math, sum)$(NBSP).

License: $(LINK2 http://boost.org/LICENSE_1_0.txt, Boost License 1.0).

Authors: Ilya Yaroshenko

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
import std.traits: isArray, isFloatingPoint, isMutable;

/++
Output range for mean.
+/
struct MeanAccumulator(T, Summation summation) 
    if (isMutable!T)
{
    private:
    
    Summator!(T, summation) sum;
    size_t count;
    
    public:
    
    this()(T x, size_t n = 0) {
        sum = Summator!(T, summation)(x);
        count = n;
    }
    
    F mean(F = T)() @property
    {
        return sum.sum / cast(F) count;
    }
    
    void put(U)(U x)
    {
        this.sum.put(x);
		size_t n;
        static if (hasShape!U) {
        	n = x.elementCount;
        } else static if (hasLength!U) {
        	n = x.length;
        } else {
            n = 1;    
        }
        this.count += n;
    }
}

///
version(mir_test) @safe pure nothrow unittest {
    import mir.ndslice.slice : sliced;

    MeanAccumulator!(double, Summation.pairwise) x;
    x.put([0.0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    x.put(5);
    assert(x.mean == 2.5);
}

version(mir_test) @safe pure nothrow unittest {
    import mir.ndslice.slice : sliced;

    auto x = MeanAccumulator!(float, Summation.pairwise)(0f, 0);
    x.put([0, 1, 2, 3, 4].sliced);
    assert(x.mean == 2);
    x.put(5);
    assert(x.mean == 2.5);
}

private template MeanAlgo(Summation summation, Range, F)
{
    static if (summation == Summation.precise)
        alias MeanAlgo = sumPrecise!(Range, F);
    else
    static if (summation == Summation.appropriate)
    {
        static if (isSummable!(Range, F))
            alias MeanAlgo = MeanAlgo!(Summation.pairwise, Range, F);
        else
        static if (is(F == class) || is(F == struct) || is(F == interface))
            alias MeanAlgo = MeanAlgo!(Summation.naive, Range, F);
        else
            alias MeanAlgo = MeanAlgo!(Summation.fast, Range, F);
    }
    else
    {
        F MeanAlgo(Range r)
        {
            static if (__traits(compiles, {MeanAccumulator!(F, summation) mean;}))
                MeanAccumulator!(F, summation) mean;
            else
                auto mean = MeanAccumulator!(F, summation)(summationInitValue!F);
            mean.put(r);
            return mean.mean;
        }

        F MeanAlgo(Range r, F s, size_t n = 0)
        {
            auto mean = MeanAccumulator!(F, summation)(s, n);
            mean.put(r);
            return mean.mean;
        }
    }
}

/++
Computes the average of `r`, which must be a finite iterable.

Can optionally provide a `seed`, which will be passed to the sum function. In 
addition, a `seedCount` can optionally be provided. This provides an initial count
to the mean function. 

Returns:
    The average of all the elements in the range r.
+/
template mean(F, Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    +/
    @safe @fmamath F
    mean(F, Range)(Range r)
    {
        return MeanAlgo!(summation, Range, F)(r);
    }

    /++
    Params:
        r = range
        seed = seed to pass to sum function
        seedCount = number of elements associated with seed, optional (default = 0)
    +/
    @safe @fmamath F
    mean(Range)(Range r, F seed, size_t seed_count = 0)
    {
        return MeanAlgo!(summation, Range, F)(r, seed, seedCount);
    }
}

template mean(Summation summation = Summation.appropriate)
{
    /++
    Params:
        r = range
    +/
    @safe @fmamath sumType!Range
    mean(Range)(Range r)
    {
        return MeanAlgo!(summation, Range, sumType!Range)(r);
    }
    
    /++
    Params:
        r = range
        seed = seed to pass to sum function
        seedCount = number of elements associated with seed, optional (default = 0)
    +/
    @safe @fmamath F
    mean(Range, F)(Range r, F seed, size_t seedCount = 0)
    {
        return MeanAlgo!(summation, Range, F)(r, seed, seedCount);
    }
}

///ditto
template mean(string summation)
{
    mixin("alias mean = .mean!(Summation." ~ summation ~ ");");
}

///
version(mir_test) @safe pure nothrow unittest
{
    import mir.ndslice.slice : sliced;

    assert(mean([1.0, 2, 3]) == 2);
    assert(mean([1.0 + 3i, 2, 3]) == 2 + 1i);
    
    assert(mean([0.0, 1, 2, 3, 4, 5].sliced(3, 2)) == 2.5);
    
    float seed = 0;
    assert(is(typeof(mean([1, 2, 3], seed)) == float));
}

version(mir_test) @safe pure nothrow unittest {
    assert([1.0, 2, 3, 4].mean == 2.5);
    assert([1, 2, 3, 4].mean(0f) == 2.5);
    assert([1, 2, 3, 4].mean(10f, 1) == 4.0);
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
version(mir_test) @safe pure nothrow @nogc unittest
{
    import mir.math.common: approxEqual;
    static immutable x = [0, 1, 2, 3];
    static immutable y = [-1, 0.2, 0.9, 2.1];
    auto params = x.simpleLinearRegression(y);
    assert(params[0].approxEqual(-0.95)); // shift
    assert(params[1].approxEqual(1)); // slope
}
