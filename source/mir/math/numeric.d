/++
This module contains simple numeric algorithms.

License: $(LINK2 http://boost.org/LICENSE_1_0.txt, Boost License 1.0).

Authors: Ilya Yaroshenko

Copyright: 2015-, Ilya Yaroshenko; 2017 Symmetry Investments Group and Kaleidic Associates Advisory Limited.

Sponsors: This work has been sponsored by $(SUBREF http://symmetryinvestments.com, Symmetry Investments) and Kaleidic Associates.
+/
module mir.math.numeric;

import mir.math.common;
import mir.primitives;
import std.range.primitives: isInputRange;

import std.traits;

/++
Product algorithms.
+/
enum ProdAlgo
{
    /++
    Performs `separateExponentAccumulation` product for floating point based types and `naive` product for integral-based types.
    +/
    appropriate,

    /++
    Separate Exponent Accumulation
    +/
    separateExponentAccumulation,

    /++
    Naive algorithm (one by one).
    +/
    naive,
}

///
struct ProdAccumulator(T, ProdAlgo prodAlgo)
{

    alias F = Unqual!T;

    static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
    {
        static assert(isFloatingPoint!F, "ProdAccumulator: ProdAlgo.separateExponentAccumulation only valid with floating point types");
        ///
        long exp = 1L;
        ///
        F x = cast(F) 0.5;
        ///
        alias mantissa = x;
    }
    else
    static if (prodAlgo == ProdAlgo.naive)
    {
        ///
        F p = cast(F) 1;
    }
    else
    {
        static assert(0, "ProdAccumulator: ProdAlgo not implemented");
    }

    ///
    this(F value)
    {
        static if (prodAlgo == ProdAlgo.naive) {
            this.p = value;
        } else static if (prodAlgo == ProdAlgo.separateExponentAccumulation) {
            import mir.math.ieee: frexp;

            int lexp;
            this.x = frexp(value, lexp);
            this.exp = lexp;
        } else {
            static assert(0, "ProdAccumulator: constructor not implemented");
        }
    }

    static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
    {
        ///
        this(long exp, F x)
        {
            this.exp = exp;
            this.x = x;
        }
    }

    ///
    void put(T e)
    {
        static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
        {
            int lexp;
            import mir.math.ieee: frexp;
            x *= frexp(e, lexp);
            exp += lexp;
            if (x.fabs < 0.5f)
            {
                x += x;
                exp--;
            }
        }
        else
        static if (prodAlgo == ProdAlgo.naive)
        {
            p *= e;
        }
    }

    ///
    void put(ProdAccumulator!(T, prodAlgo) value)
    {
        static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
        {
            exp += value.exp;
            x *= value.x;
            if (x.fabs < 0.5f)
            {
                x += x;
                exp--;
            }
        }
        else
        static if (prodAlgo == ProdAlgo.naive)
        {
            p *= value.p;
        }
    }
    
    void put(Range)(Range r)
        if (isIterable!Range)
    {
        foreach (ref elem; r)
            put(elem);
    }
    
    import mir.ndslice.slice;

    /// ditto
    void put(Range: Slice!(Iterator, N, kind), Iterator, size_t N, SliceKind kind)(Range r)
    {
        static if (N > 1 && kind == Contiguous)
        {
            import mir.ndslice.topology: flattened;
            this.put(r.flattened);
        }
        else
        static if (isPointer!Iterator && kind == Contiguous)
        {
            this.put(r.field);
        }
        else
        {
            foreach(elem; r)
                this.put(elem);
        }
    }

    ///
    T prod() const scope @property
    {
        static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
        {
            import mir.math.ieee: ldexp;
            int e =
                exp > int.max ? int.max :
                exp < int.min ? int.min :
                cast(int) exp;
            return ldexp(mantissa, e);
        }
        else
        static if (prodAlgo == ProdAlgo.naive)
        {
            return p;
        }
    }

    static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
    {
        ///
        ProdAccumulator!(T, prodAlgo) ldexp(long exp) const
        {
            return typeof(return)(this.exp + exp, mantissa);
        }
    }

    // ///
    alias opOpAssign(string op : "*") = put;

    ///
    ProdAccumulator!(T, prodAlgo) opUnary(string op : "-")() const
    {
        static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
            return typeof(return)(exp, -mantissa);
        else static if (prodAlgo == ProdAlgo.naive)
            return typeof(return)(-p);
    }

    ///
    ProdAccumulator!(T, prodAlgo) opUnary(string op : "+")() const
    {
        static if (prodAlgo == ProdAlgo.separateExponentAccumulation)
            return typeof(return)(exp, +mantissa);
        else static if (prodAlgo == ProdAlgo.naive)
            return typeof(return)(+p);
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    ProdAccumulator!(int, ProdAlgo.naive) x;
    x.put([1, 2, 3].sliced);
    assert(x.prod == 6);
    x.put(4);
    assert(x.prod == 24);
}

template ResolveProdAlgoType(ProdAlgo prodAlgo, F)
{
    static if (prodAlgo == ProdAlgo.appropriate) {
        static if (isFloatingPoint!F)
            enum ResolveProdAlgoType = ProdAlgo.separateExponentAccumulation;
        else
            enum ResolveProdAlgoType = ProdAlgo.naive;
    }
    else {
        enum ResolveProdAlgoType = prodAlgo;
    }
}

package template prodType(T)
{
    import mir.ndslice.slice: isSlice, DeepElementType;
    static if (isIterable!T) {
        static if (isSlice!T)
            alias U = Unqual!(DeepElementType!(T.This));
        else
            alias U = Unqual!(ForeachType!T);
    } else {
        alias U = Unqual!T;
    }
    static if (__traits(compiles, {
        auto a = U.init * U.init;
        a *= U.init;
    }))
        alias prodType = typeof(U.init * U.init);
    else
        static assert(0, "Can't prod elements of type " ~ U.stringof);
}


/++
Calculates the product of the elements of the input.

A `seed` may be passed to `prod`. Not only will this seed be used as an initial
value, but its type will be used if it is not specified.

+/
template prod(F, ProdAlgo prodAlgo = ProdAlgo.appropriate)
    if (isMutable!F)
{
    alias FAlgo = ResolveProdAlgoType!(prodAlgo, F);

    /++
    Params:
        val = values
    Returns:
        The prduct of all the elements in `val`
    +/
    F prod(scope const F[] val...)
    {
        ProdAccumulator!(F, FAlgo) prod;
        prod.put(val);
        return prod.prod;
    }

    /++
    Params:
        r = finite iterable range
    Returns:
        The prduct of all the elements in `r`
    +/
    F prod(Range)(Range r)
        if (isIterable!Range)
    {
        import core.lifetime: move;

        ProdAccumulator!(F, FAlgo) prod;
        prod.put(r.move);
        return prod.prod;
    }

    /++
    Params:
        r = finite iterable range
        seed = initial value
    Returns:
        The prduct of all the elements in `r`
    +/
    F prod(Range)(Range r, F seed)
         if (isIterable!Range &&
            FAlgo != ProdAlgo.separateExponentAccumulation)
    {
        import core.lifetime: move;

        auto prod = ProdAccumulator!(F, FAlgo)(seed);
        prod.put(r.move);
        return prod.prod;
    }

    /++
    Params:
        r = finite iterable range
        exp = value of exponent
    Returns:
        The mantissa, such that the product equals the mantissa times 2^^exp
    +/
    template prod(Range)
        if (isIterable!Range &&
            FAlgo == ProdAlgo.separateExponentAccumulation)
    {
        import core.lifetime: move;

        ///
        F prod(Range r, ref long exp)
        {
            ProdAccumulator!(F, FAlgo) prod;
            prod.put(r.move);
            exp = prod.exp;
            return prod.x;
        }

    /++
    Params:
        r = finite iterable range
        seed = initial value
        exp = value of exponent
    Returns:
        The mantissa, such that the product equals the mantissa times 2^^exp
    +/
        F prod(Range r, ref long exp, F seed)
        {
            auto prod = ProdAccumulator!(F, FAlgo)(seed);
            prod.put(r.move);
            exp = prod.exp;
            return prod.x;
        }
    }
}

///ditto
template prod(ProdAlgo prodAlgo = ProdAlgo.appropriate)
{
    import std.traits: CommonType;

    /++
    Params:
        val = values
    Returns:
        The prduct of all the elements in `val`
    +/
    prodType!(CommonType!T) prod(T...)(T val)
        if (T.length > 0 &&
            !is(CommonType!T == void))
    {
        alias F = typeof(return);
        return .prod!(F, prodAlgo)(val);
    }

    /++
    Params:
        r = finite iterable range
    Returns:
        The prduct of all the elements in `r`
    +/
    prodType!Range prod(Range)(Range r)
        if (isIterable!Range)
    {
        import core.lifetime: move;
        alias F = typeof(return);
        return .prod!(F, prodAlgo)(r.move);
    }

    /++
    Params:
        r = finite iterable range
        seed = initial value
    Returns:
        The prduct of all the elements in `r`
    +/
    F prod(Range, F)(Range r, F seed)
        if (isIterable!Range &&
            ResolveProdAlgoType!(prodAlgo, prodType!Range) != ProdAlgo.separateExponentAccumulation)
    {
        import core.lifetime: move;
        return .prod!(F, prodAlgo)(r.move, seed);
    }
    
    /++
    Params:
        r = finite iterable range
        exp = value of exponent
    Returns:
        The mantissa, such that the product equals the mantissa times 2^^exp
    +/
    prodType!Range prod(Range)(Range r, ref long exp)
        if (isIterable!Range &&
            ResolveProdAlgoType!(prodAlgo, prodType!Range) == ProdAlgo.separateExponentAccumulation)
    {
        import core.lifetime: move;
        alias F = typeof(return);
        return .prod!(F, prodAlgo)(r.move, exp);
    }

    /++
    Params:
        r = finite iterable range
        seed = initial value
        exp = value of exponent
    Returns:
        The mantissa, such that the product equals the mantissa times 2^^exp
    +/
    F prod(Range, F)(Range r, ref long exp, F seed)
        if (isIterable!Range &&
            ResolveProdAlgoType!(prodAlgo, F) == ProdAlgo.separateExponentAccumulation)
    {
        import core.lifetime: move;
        return .prod!(F, prodAlgo)(r.move, exp, seed);
    }
}

///ditto
template prod(F, string prodAlgo)
    if (isMutable!F)
{
    mixin("alias prod = .prod!(F, ProdAlgo." ~ prodAlgo ~ ");");
}

///ditto
template prod(string prodAlgo)
{
    mixin("alias prod = .prod!(ProdAlgo." ~ prodAlgo ~ ");");
}

/// Product of arbitrary inputs
version(mir_test)
unittest
{
    assert(prod(1, 3, 4) == 12);
    assert(prod!float(1, 3, 4) == 12.0);
}

/// Product of arrays and ranges
version(mir_test)
unittest
{
    enum l = 2.0 ^^ (double.max_exp - 1);
    enum s = 2.0 ^^ -(double.max_exp - 1);
    auto r = [l, l, l, s, s, s, 0.8 * 2.0 ^^ 10];
    
    assert(r.prod == 0.8 * 2.0 ^^ 10);
    
    // Can get the mantissa and exponent
    long e;
    assert(r.prod(e) == 0.8);
    assert(e == 10);
}

/// Product of vector
version(mir_test)
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: reduce;

    enum l = 2.0 ^^ (double.max_exp - 1);
    enum s = 2.0 ^^ -(double.max_exp - 1);
    auto c = 0.8;
    auto u = c * 2.0 ^^ 10;
    auto r = [l, l, l, s, s, s, u, u, u].sliced;
              
    assert(r.prod == reduce!"a * b"(1.0, [u, u, u]));

    long e;
    assert(r.prod(e) == reduce!"a * b"(1.0, [c, c, c]));
    assert(e == 30);
}

/// Product of matrix
version(mir_test)
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.algorithm.iteration: reduce;

    enum l = 2.0 ^^ (double.max_exp - 1);
    enum s = 2.0 ^^ -(double.max_exp - 1);
    auto c = 0.8;
    auto u = c * 2.0 ^^ 10;
    auto r = [
        [l, l, l],
        [s, s, s],
        [u, u, u]
    ].fuse;
              
    assert(r.prod == reduce!"a * b"(1.0, [u, u, u]));

    long e;
    assert(r.prod(e) == reduce!"a * b"(1.0, [c, c, c]));
    assert(e == 30);
}

/// Column prod of matrix
version(mir_test)
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.algorithm.iteration: all;
    import mir.math.common: approxEqual;
    import mir.ndslice.topology: alongDim, byDim, map;

    auto x = [
        [2.0, 1.0, 1.5, 2.0, 3.5, 4.25],
        [2.0, 7.5, 5.0, 1.0, 1.5, 5.0]
    ].fuse;

    auto result = [4.0, 7.5, 7.5, 2.0, 5.25, 21.25];

    // Use byDim or alongDim with map to compute mean of row/column.
    assert(x.byDim!1.map!prod.all!approxEqual(result));
    assert(x.alongDim!0.map!prod.all!approxEqual(result));

    // FIXME
    // Without using map, computes the prod of the whole slice
    // assert(x.byDim!1.prod.all!approxEqual(result));
    // assert(x.alongDim!0.prod.all!approxEqual(result));
}


/// Can also set algorithm or output type
version(mir_test)
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;
    import mir.ndslice.topology: repeat;

    auto x = [1.0, 2, 3].sliced;
    assert(x.prod!"naive".approxEqual(6));
    assert(x.prod!"separateExponentAccumulation".approxEqual(6));
    assert(x.prod!(float, "naive") == 6);
    
    auto y = uint.max.repeat(3);
    assert(y.prod!ulong == (cast(ulong) uint.max) ^^ 3);
}

/// Also works for complex numbers (and other user-defined types)
version(mir_test)
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable cdouble[] x = [1.0 + 2i, 2 + 3i, 3 + 4i, 4 + 5i];
    static immutable cdouble result = -185 - 180i;
    assert(x.sliced.prod == result);
}


/++
Compute the sum of binary logarithms of the input range $(D r).
The error of this method is much smaller than with a naive sum of log2.
+/
Unqual!(DeepElementType!Range) sumOfLog2s(Range)(Range r)
    if (isFloatingPoint!(DeepElementType!Range))
{
    long exp = 0;
    auto x = .prod(r, exp);
    return exp + log2(x);
}

///
version(mir_test)
@safe unittest
{
    alias isNaN = x => x != x;

    assert(sumOfLog2s(new double[0]) == 0);
    assert(sumOfLog2s([0.0L]) == -real.infinity);
    assert(sumOfLog2s([-0.0L]) == -real.infinity);
    assert(sumOfLog2s([2.0L]) == 1);
    assert(isNaN(sumOfLog2s([-2.0L])));
    assert(isNaN(sumOfLog2s([real.nan])));
    assert(isNaN(sumOfLog2s([-real.nan])));
    assert(sumOfLog2s([real.infinity]) == real.infinity);
    assert(isNaN(sumOfLog2s([-real.infinity])));
    assert(sumOfLog2s([ 0.25, 0.25, 0.25, 0.125 ]) == -9);
}
