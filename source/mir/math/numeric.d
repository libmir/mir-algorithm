/++
This module contains simple numeric algorithms.
License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Sponsors: This work has been sponsored by $(SUBREF http://symmetryinvestments.com, Symmetry Investments) and Kaleidic Associates.
+/
module mir.math.numeric;

import mir.math.common;
import mir.primitives;
import mir.primitives: isInputRange;
import std.traits: CommonType, Unqual, isIterable, ForeachType, isPointer;
import mir.internal.utility: isFloatingPoint;

///
struct ProdAccumulator(T)
    if (isFloatingPoint!T)
{
    alias F = Unqual!T;

    ///
    long exp = 1L;
    ///
    F x = cast(F) 0.5;
    ///
    alias mantissa = x;

    ///
    @safe pure @nogc nothrow
    this(F value)
    {
        import mir.math.ieee: frexp;

        int lexp;
        this.x = frexp(value, lexp);
        this.exp = lexp;
    }

    ///
    @safe pure @nogc nothrow
    this(long exp, F x)
    {
        this.exp = exp;
        this.x = x;
    }

    ///
    @safe pure @nogc nothrow
    void put(U)(U e)
        if (is(U : T))
    {
        static if (is(U == T))
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
        } else {
            return put(cast(T) e);
        }
    }

    ///
    @safe pure @nogc nothrow
    void put(ProdAccumulator!T value)
    {
        exp += value.exp;
        x *= value.x;
        if (x.fabs < 0.5f)
        {
            x += x;
            exp--;
        }
    }

    ///
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
    @safe pure @nogc nothrow
    T prod() const scope @property
    {
        import mir.math.ieee: ldexp;
        int e =
            exp > int.max ? int.max :
            exp < int.min ? int.min :
            cast(int) exp;
        return ldexp(mantissa, e);
    }

    ///
    @safe pure @nogc nothrow
    ProdAccumulator!T ldexp(long exp) const
    {
        return typeof(return)(this.exp + exp, mantissa);
    }

    // ///
    alias opOpAssign(string op : "*") = put;

    ///
    @safe pure @nogc nothrow
    ProdAccumulator!T opUnary(string op : "-")() const
    {
        return typeof(return)(exp, -mantissa);
    }

    ///
    @safe pure @nogc nothrow
    ProdAccumulator!T opUnary(string op : "+")() const
    {
        return typeof(return)(exp, +mantissa);
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    ProdAccumulator!float x;
    x.put([1, 2, 3].sliced);
    assert(x.prod == 6f);
    x.put(4);
    assert(x.prod == 24f);
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    static immutable a = [1, 2, 3];
    ProdAccumulator!float x;
    x.put(a);
    assert(x.prod == 6f);
    x.put(4);
    assert(x.prod == 24f);
    static assert(is(typeof(x.prod) == float));
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    ProdAccumulator!double x;
    x.put([1.0, 2.0, 3.0]);
    assert(x.prod == 6.0);
    x.put(4.0);
    assert(x.prod == 24.0);
    static assert(is(typeof(x.prod) == double));
}

package template prodType(T)
{
    import mir.math.sum: elementType;

    alias U = elementType!T;
    
    static if (__traits(compiles, {
        auto temp = U.init * U.init;
        temp *= U.init;
    })) {
        import mir.math.stat: statType;

        alias V = typeof(U.init * U.init);
        alias prodType = statType!(V, false);
    } else {
        static assert(0, "prodType: Can't prod elements of type " ~ U.stringof);
    }
}

/++
Calculates the product of the elements of the input.

This function uses a separate exponential accumulation algorithm to calculate the
product. A consequence of this is that the result must be a floating point type.
To calculate the product of a type that is not implicitly convertible to a 
floating point type, use $(MREF mir, algorithm, iteration, reduce) or $(MREF mir, algorithm, iteration, fold). 

/++
Params:
    r = finite iterable range
Returns:
    The prduct of all the elements in `r`
+/

See_also: 
$(MREF mir, algorithm, iteration, reduce)
$(MREF mir, algorithm, iteration, fold)
+/
F prod(F, Range)(Range r)
    if (isFloatingPoint!F && isIterable!Range)
{
    import core.lifetime: move;

    ProdAccumulator!F prod;
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
F prod(F, Range)(Range r, ref long exp)
    if (isFloatingPoint!F && isIterable!Range)
{
    import core.lifetime: move;

    ProdAccumulator!F prod;
    prod.put(r.move);
    exp = prod.exp;
    return prod.x;
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
    return .prod!(F, Range)(r.move);
}

/++
Params:
    r = finite iterable range
    exp = value of exponent
Returns:
    The mantissa, such that the product equals the mantissa times 2^^exp
+/
prodType!Range prod(Range)(Range r, ref long exp)
    if (isIterable!Range)
{
    import core.lifetime: move;

    alias F = typeof(return);
    return .prod!(F, Range)(r.move, exp);
}

/++
Params:
    ar = values
Returns:
    The prduct of all the elements in `ar`
+/
prodType!T prod(T)(scope const T[] ar...)
{
    alias F = typeof(return);
    ProdAccumulator!F prod;
    prod.put(ar);
    return prod.prod;
}

/// Product of arbitrary inputs
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    assert(prod(1.0, 3, 4) == 12.0);
    assert(prod!float(1, 3, 4) == 12f);
}

/// Product of arrays and ranges
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.math.common: approxEqual;

    enum l = 2.0 ^^ (double.max_exp - 1);
    enum s = 2.0 ^^ -(double.max_exp - 1);
    auto r = [l, l, l, s, s, s, 0.8 * 2.0 ^^ 10];
    
    assert(r.prod == 0.8 * 2.0 ^^ 10);
    
    // Can get the mantissa and exponent
    long e;
    assert(r.prod(e).approxEqual(0.8));
    assert(e == 10);
}

/// Product of vector
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: reduce;
    import mir.math.common: approxEqual;

    enum l = 2.0 ^^ (double.max_exp - 1);
    enum s = 2.0 ^^ -(double.max_exp - 1);
    auto c = 0.8;
    auto u = c * 2.0 ^^ 10;
    auto r = [l, l, l, s, s, s, u, u, u].sliced;
              
    assert(r.prod == reduce!"a * b"(1.0, [u, u, u]));

    long e;
    assert(r.prod(e).approxEqual(reduce!"a * b"(1.0, [c, c, c])));
    assert(e == 30);
}

/// Product of matrix
version(mir_test)
@safe pure
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
@safe pure
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

/// Can also set output type
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.math.common: approxEqual;
    import mir.ndslice.topology: repeat;

    auto x = [1, 2, 3].sliced;
    assert(x.prod!float == 6f);
}

/// Product of variables whose underlying types are implicitly convertible to double also have type double
version(mir_test)
@safe pure nothrow
unittest
{
    static struct Foo
    {
        int x;
        alias x this;
    }

    auto x = prod(1, 2, 3);
    assert(x == 6.0);
    static assert(is(typeof(x) == double));
    
    auto y = prod([Foo(1), Foo(2), Foo(3)]);
    assert(y == 6.0);
    static assert(is(typeof(y) == double));
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: reduce;
    import mir.math.common: approxEqual;

    enum l = 2.0 ^^ (double.max_exp - 1);
    enum s = 2.0 ^^ -(double.max_exp - 1);
    enum c = 0.8;
    enum u = c * 2.0 ^^ 10;
    static immutable r = [l, l, l, s, s, s, u, u, u];
    static immutable result1 = [u, u, u];
    static immutable result2 = [c, c, c];
              
    assert(r.sliced.prod.approxEqual(reduce!"a * b"(1.0, result1)));

    long e;
    assert(r.sliced.prod(e).approxEqual(reduce!"a * b"(1.0, result2)));
    assert(e == 30);
}

version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: reduce;
    import mir.math.common: approxEqual;

    enum l = 2.0 ^^ (float.max_exp - 1);
    enum s = 2.0 ^^ -(float.max_exp - 1);
    enum c = 0.8;
    enum u = c * 2.0 ^^ 10;
    static immutable r = [l, l, l, s, s, s, u, u, u];
    static immutable result1 = [u, u, u];
    static immutable result2 = [c, c, c];
              
    assert(r.sliced.prod!double.approxEqual(reduce!"a * b"(1.0, result1)));

    long e;
    assert(r.sliced.prod!double(e).approxEqual(reduce!"a * b"(1.0, result2)));
    assert(e == 30);
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
@safe pure
unittest
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

/++
Quickly computes factorial using extended
precision floating point type $(MREF mir,bignum,fp).

Params:
    count = number of product members
    start = initial member value (optional)
Returns: `(count + start - 1)! / (start - 1)!`
+/
auto factorial
    (size_t coefficientSize = 128, Exp = sizediff_t)
    (ulong count, ulong start = 1)
    if (coefficientSize % (size_t.sizeof * 8) == 0 && coefficientSize >= (size_t.sizeof * 8))
    in (start)
{
    import mir.utility: _expect;
    import mir.bignum.fp: Fp;
    alias R = Fp!(coefficientSize, Exp);
    R prod = 1LU;
    import mir.checkedint: addu, mulu;

    if (count)
    {
        ulong tempProd = start;
        while(--count)
        {
            bool overflow;
            ulong nextTempProd = mulu(tempProd, ++start, overflow);
            if (_expect(!overflow, true))
            {
                tempProd = nextTempProd;
                continue;
            }
            else
            {
                prod *= R(tempProd);
                tempProd = start;
            }
        }
        prod *= R(tempProd);
    }

    return prod;
}

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.bignum.fp: Fp;
    import mir.math.common: approxEqual;
    import mir.math.numeric: prod;
    import mir.ndslice.topology: iota;

    static assert(is(typeof(factorial(33)) == Fp!128));
    static assert(is(typeof(factorial!256(33)) == Fp!256));
    static assert(cast(double) factorial(33) == 8.68331761881188649551819440128e+36);

    assert(cast(double) factorial(0) == 1);
    assert(cast(double) factorial(0, 100) == 1);
    assert(cast(double) factorial(1, 100) == 100);
    assert(approxEqual(cast(double) factorial(100, 1000), iota([100], 1000).prod!double));
}
