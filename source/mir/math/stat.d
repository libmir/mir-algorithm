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
import std.traits: isArray, isFloatingPoint;

/++
Computes the arithmetic mean of `r`, which must be a finite iterable.

Returns:
    The arithmetic mean of all the elements in the range r.
+/
template mean(Summation summation = Summation.appropriate)
{
    ///
    @safe @fmamath sumType!Range
    mean(Range)(Range r)
        if (hasElementCount!Range
         || hasLength!Range
         || summation == Summation.appropriate
         || summation == Summation.fast
         || summation == Summation.naive)
    {
        static if (hasElementCount!Range || hasLength!Range)
        {
            static if (hasElementCount!Range) {
                auto n = r.elementCount;
            } else {
                auto n = r.length;
            }
            return sum!summation(r.move) / cast(sumType!Range) n;
        }
        else
        {
            auto s = cast(typeof(return)) 0;
            size_t length;
            foreach (e; r)
            {
                length++;
                s += e;
            }
            return s / cast(sumType!Range) length;
        }
    }
    
    ///
    @safe @fmamath F
    mean(Range)(Range r, F seed)
        if (hasElementCount!Range
         || hasLength!Range
         || summation == Summation.appropriate
         || summation == Summation.fast
         || summation == Summation.naive)
    {
        static if (hasElementCount!Range || hasLength!Range)
        {
            static if (hasElementCount!Range) {
                auto n = r.elementCount;
            } else {
                auto n = r.length;
            }
            return sum!summation(r.move, seed) / cast(F) n;
        }
        else
        {
            size_t length;
            foreach (e; r)
            {
                length++;
                seed += e;
            }
            return seed / cast(F) length;
        }
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
