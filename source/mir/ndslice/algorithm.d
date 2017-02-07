/++
This is a submodule of $(MREF mir,ndslice).

It contains basic multidimensional iteration algorithms.

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
$(T2 reduce, Accumulates all elements.)
$(T2 each, Iterates all elements.)
$(T2 find, Finds backward index.)
$(T2 any, Checks if at least one element satisfy to a predicate.)
$(T2 all, Checks if all elements satisfy to a predicate.)
$(T2 count, Counts elements in a slices according to a predicate.)
$(T2 cmp, Compares two slices.)
$(T2 equal, Compares two slices for equality.)
)


All operators are suitable to change slices using `ref` argument qualification in a function declaration.
Note, that string lambdas in Mir are `auto ref` functions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.algorithm;

import std.traits;
import std.meta;

import mir.ndslice.internal;
import mir.ndslice.slice;

private void checkShapesMatch(
    string fun = __FUNCTION__,
    string pfun = __PRETTY_FUNCTION__,
    Slices...)
    (Slices slices)
{
    enum msg = "all arguments must be slices" ~ tailErrorMessage!(fun, pfun);
    enum msgShape = "all slices must have the same shape"  ~ tailErrorMessage!(fun, pfun);
    foreach (i, Slice; Slices)
    {
        static assert (slices[i].shape.length == slices[0].shape.length, msgShape);
        assert(slices[i].shape == slices[0].shape, msgShape);
    }
}

@fastmath:

private auto ref frontOf(alias slice)() { return slice.front; };


S reduceImpl(alias fun, S, Slices...)(S seed, Slices slices)
{
    do
    {
        static if (slices[0].shape.length == 1)
            seed = fun(seed, staticMap!(frontOf, slices));
        else
            seed = .reduceImpl!fun(seed, staticMap!(frontOf, slices));
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return seed;
}

/++
Implements the homonym function (also known as `accumulate`,
`compress`, `inject`, or `fold`) present in various programming
languages of functional flavor. The call `reduce!(fun)(seed, slice1, ..., sliceN)`
first assigns `seed` to an internal variable `result`,
also called the accumulator. Then, for each set of element `x1, ..., xN` in
`slice1, ..., sliceN`, `result = fun(result, x1, ..., xN)` gets evaluated. Finally,
`result` is returned.

`reduce` allows to iterate multiple slices in the lockstep.

Note:
    $(SUBREF topology, pack) can be used to specify dimensions.
Params:
    fun = A function.
See_Also:
    $(HTTP llvm.org/docs/LangRef.html#fast-math-flags, LLVM IR: Fast Math Flags)

    $(HTTP en.wikipedia.org/wiki/Fold_(higher-order_function), Fold (higher-order function))
+/
template reduce(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    /++
    Params:
        seed = An initial accumulation value.
        slices = One or more slices.
    Returns:
        the accumulated `result`
    +/
    @fastmath auto reduce(S, Slices...)(S seed, Slices slices)
        if (Slices.length && allSatisfy!(isSlice, Slices))
    {
        slices.checkShapesMatch;
        if (slices[0].anyEmpty)
            return cast(Unqual!S) seed;
        static if (is(S : Unqual!S))
            alias UT = Unqual!S;
        else
            alias UT = S;
        return reduceImpl!(fun, UT, Slices)(seed, slices);
    }
    else
        alias reduce = .reduce!(naryFun!fun);

}

/// Single slice
unittest
{
    import mir.ndslice.topology : iota;

    //| 0 1 2 | => 3  |
    //| 3 4 5 | => 12 | => 15
    auto sl = iota(2, 3);

    // sum of all element in the slice
    auto res = size_t(0).reduce!"a + b"(sl);

    assert(res == 15);
}

/// Multiple slices, dot product
//version(none)
unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;
    import mir.ndslice.internal : fastmath;

    static @fastmath T fmuladd(T)(const T a, const T b, const T c)
    {
        return a + b * c;
    }

    //| 0 1 2 |
    //| 3 4 5 |
    auto a = iota([2, 3], 0).as!double.slice;
    //| 1 2 3 |
    //| 4 5 6 |
    auto b = iota([2, 3], 1).as!double.slice;

    alias dot = reduce!fmuladd;
    auto res = dot(0.0, a, b);

    // check the result:
    import mir.ndslice.topology : flattened;
    import std.numeric : dotProduct;
    assert(res == dotProduct(a.flattened, b.flattened));
}

/// Zipped slices, dot product
pure unittest
{
    import std.typecons : Yes;
    import std.numeric : dotProduct;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota, zip, universal;
    import mir.ndslice.internal : fastmath;

    static @fastmath T fmuladd(T, Z)(const T a, Z z)
    {
        return a + z.a * z.b;
    }

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3).as!double.slice.universal;
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1).as!double.slice;

    // slices must have the same strides for `zip!true`.
    assert(sl1.strides == sl2.strides);

    auto z = zip!true(sl1, sl2);

    auto dot = reduce!fmuladd(0.0, z);

    assert(dot == dotProduct(iota(6), iota([6], 1)));
}

/// Tensor mutation on-the-fly
unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;
    import mir.ndslice.internal : fastmath;

    static @fastmath T fun(T)(const T a, ref T b)
    {
        return a + b++;
    }

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota(2, 3).as!double.slice;

    auto res = reduce!fun(double(0), sl);

    assert(res == 15);

    //| 1 2 3 |
    //| 4 5 6 |
    assert(sl == iota([2, 3], 1));
}

/++
Packed slices.

Computes minimum value of maximum values for each row.
+/
unittest
{
    // LDC is LLVM D Compiler
    version(LDC)
        import ldc.intrinsics : fmax = llvm_maxnum, fmin = llvm_minnum;
    // std.math prevents vectorization for now
    else
        import std.math : fmax, fmin;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.dynamic : transposed;
    import mir.ndslice.topology : as, iota, pack, map, universal;

    alias maxVal = (a) => reduce!fmax(-double.infinity, a);
    alias minVal = (a) => reduce!fmin(double.infinity, a);
    alias minimaxVal = (a) => minVal(a.pack!1.map!maxVal);

    auto sl = iota(2, 3).as!double.slice;

    // Vectorized computation: row stride equals 1.
    //| 0 1 2 | => | 2 |
    //| 3 4 5 | => | 5 | => 2
    auto res = minimaxVal(sl);
    assert(res == 2);

    // Common computation: row stride does not equal 1.
    //| 0 1 2 |    | 0 3 | => | 3 |
    //| 3 4 5 | => | 1 4 | => | 4 |
    //             | 2 5 | => | 5 | => 3
    auto resT = minimaxVal(sl.universal.transposed);
    assert(resT == 3);
}

@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;
    auto a = reduce!"a + b"(size_t(7), iota([0, 1], 1));
    assert(a == 7);
}

void eachImpl(alias fun, Slices...)(Slices slices)
{
    do
    {
        static if (slices[0].shape.length == 1)
            fun(staticMap!(frontOf, slices));
        else
            .eachImpl!fun(staticMap!(frontOf, slices));
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
}

/++
The call `each!(fun)(slice1, ..., sliceN)`
evaluates `fun` for each set of elements `x1, ..., xN` in
`slice1, ..., sliceN` respectively.

`each` allows to iterate multiple slices in the lockstep.
Params:
    fun = A function.
Note:
    $(SUBREF dynamic, transposed) and
    $(SUBREF topology, pack) can be used to specify dimensions.
See_Also:
    This is functionally similar to $(LREF reduce) but has not seed.
+/
template each(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    /++
    Params:
        slices = One or more slices.
    +/
    @fastmath auto each(Slices...)(Slices slices)
        if (Slices.length && allSatisfy!(isSlice, Slices))
    {
        slices.checkShapesMatch;
        if (slices[0].anyEmpty)
            return;
        eachImpl!fun(slices);
    }
    else
        alias each = .each!(naryFun!fun);
}

/// Single slice, multiply-add
unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota(2, 3).as!double.slice;

    sl.each!((ref a) { a = a * 10 + 5; });

    import std.stdio;
    assert(sl ==
        [[ 5, 15, 25],
         [35, 45, 55]]);
}

/// Swap two slices
unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto a = iota([2, 3], 0).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    auto b = iota([2, 3], 10).as!double.slice;

    each!swap(a, b);

    assert(a == iota([2, 3], 10));
    assert(b == iota([2, 3], 0));
}

/// Swap two zipped slices
unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, zip, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto a = iota([2, 3], 0).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    auto b = iota([2, 3], 10).as!double.slice;

    auto z = zip(a, b);

    z.each!(z => swap(z.a, z.b));

    assert(a == iota([2, 3], 10));
    assert(b == iota([2, 3], 0));
}

@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    size_t i;
    iota(0, 2).each!((a){i++;});
    assert(i == 0);
}

size_t findImpl(alias fun, size_t N, Slices...)(ref size_t[N] backwardIndex, Slices slices)
    if (Slices.length && allSatisfy!(isSlice, Slices))
{
    do
    {
        static if (slices[0].shape.length == 1)
        {
            if (fun(staticMap!(frontOf, slices)))
            {
                backwardIndex[0] = slices[0].length;
                return 1;
            }
        }
        else
        {
            if (findImpl!fun(backwardIndex[1 .. $], staticMap!(frontOf, slices)))
            {
                backwardIndex[0] = slices[0].length;
                return 1;
            }
        }
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return 0;
}

/++
Finds a backward index for which
`pred(slices[0].backward(index), ..., slices[$-1].backward(index))` equals `true`.

Params:
    pred = A predicate.

Optimization:
    To check if any element was found
    use the last dimension (row index).
    This will slightly optimize the code.
--------
// $-1 instead of 0
if (backwardIndex[$-1])
{
    auto elem1 = slice1.backward(backwardIndex);
    //...
    auto elemK = sliceK.backward(backwardIndex);
}
else
{
    // not found
}
--------

See_also:
    $(LREF any)

    $(REF Slice.backward, mir,ndslice,slice)
+/
template find(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        The variable passing by reference to be filled with the multidimensional backward index for which the predicate is true.
        Backward index equals zeros, if the predicate evaluates `false` for all indexes.
    Constraints:
        All slices must have the same shape.
    +/
    @fastmath size_t[isSlice!(Slices[0])[0]] find(Slices...)(Slices slices)
        if (Slices.length && allSatisfy!(isSlice, Slices))
    {
        slices.checkShapesMatch;
        typeof(return) ret;
        if (!slices[0].anyEmpty)
            findImpl!pred(ret, slices);
        return ret;
    }
    else
        alias find = .find!(naryFun!pred);
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;
    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);
    size_t[2] bi = sl.find!"a == 3";
    assert(sl.backward(bi) == 3);

    bi = sl.find!"a == 6";
    assert(bi[0] == 0);
    assert(bi[1] == 0);
}

/// Multiple slices
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    size_t[2] bi = find!((a, b) => a * b == 39)(a, b);
    assert(a.backward(bi) == 3);
    assert(b.backward(bi) == 13);
}

/// Zipped slices
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    size_t[2] bi = zip!true(a, b).find!"a.a * a.b == 39";

    assert(a.backward(bi) == 3);
    assert(b.backward(bi) == 13);
}

/// Mutation on-the-fly
pure nothrow unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3).as!double.slice;

    static bool pred(T)(ref T a)
    {
        if (a == 5)
            return true;
        a = 8;
        return false;
    }

    size_t[2] bi = sl.find!pred;

    assert(bi == [1, 1]);
    assert(sl.backward(bi) == 5);

    // sl was changed
    assert(sl == [[8, 8, 8],
                  [8, 8, 5]]);
}

@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    size_t i;
    size_t[2] bi = iota(2, 0).find!((elem){i++; return true;});
    assert(i == 0);
    assert(bi == [0, 0]);
}

size_t anyImpl(alias fun, Slices...)(Slices slices)
    if (Slices.length && allSatisfy!(isSlice, Slices))
{
    do
    {
        static if (slices[0].shape.length == 1)
        {
            if (fun(staticMap!(frontOf, slices)))
                return true;
        }
        else
        {
            if (anyImpl!fun(staticMap!(frontOf, slices)))
                return true;
        }
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return false;
}

/++
Like $(LREF find), but only returns whether or not the search was successful.

Params:
    pred = The predicate.
+/
template any(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        `true` if the search was successful and `false` otherwise.
    Constraints:
        All slices must have the same shape.
    +/
    @fastmath bool any(Slices...)(Slices slices)
        if (Slices.length && allSatisfy!(isSlice, Slices))
    {
        slices.checkShapesMatch;
        return !slices[0].anyEmpty && anyImpl!pred(slices);
    }
    else
        alias any = .any!(naryFun!pred);
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;
    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    assert(sl.any!"a == 3");
    assert(!sl.any!"a == 6");
}

/// Multiple slices
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    assert(any!((a, b) => a * b == 39)(a, b));
}

/// Zipped slices
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    // slices must have the same strides

    assert(zip!true(a, b).any!"a.a * a.b == 39");
}

/// Mutation on-the-fly
pure nothrow unittest
{
    import std.conv : to;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3).as!double.slice;

    static bool pred(T)(ref T a)
    {
        if (a == 5)
            return true;
        a = 8;
        return false;
    }

    assert(sl.any!pred);

    // sl was changed
    assert(sl == [[8, 8, 8],
                  [8, 8, 5]]);
}

size_t allImpl(alias fun, Slices...)(Slices slices)
    if (Slices.length && allSatisfy!(isSlice, Slices))
{
    do
    {
        static if (slices[0].shape.length == 1)
        {
            if (!fun(staticMap!(frontOf, slices)))
                return false;
        }
        else
        {
            if (!allImpl!fun(staticMap!(frontOf, slices)))
                return false;
        }
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return true;
}

/++
Checks if all of the elements verify `pred`.

Params:
    pred = The predicate.

+/
template all(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        `true` all of the elements verify `pred` and `false` otherwise.
    Constraints:
        All slices must have the same shape.
    +/
    @fastmath bool all(Slices...)(Slices slices)
        if (Slices.length && allSatisfy!(isSlice, Slices))
    {
        slices.checkShapesMatch;
        return slices[0].anyEmpty || allImpl!pred(slices);
    }
    else
        alias all = .all!(naryFun!pred);
}

///
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    assert(sl.all!"a < 6");
    assert(!sl.all!"a < 5");
}

/// Multiple slices
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    assert(all!"a - b == 0"(sl, sl));
}

/// Zipped slices
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);


    assert(zip!true(sl, sl).all!"a.a - a.b == 0");
}

/// Mutation on-the-fly
pure nothrow unittest
{
    import std.conv : to;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3).as!double.slice;

    static bool pred(T)(ref T a)
    {
        if (a < 4)
        {
            a = 8;
            return true;
        }
        return false;
    }

    assert(!sl.all!pred);

    // sl was changed
    assert(sl == [[8, 8, 8],
                  [8, 4, 5]]);
}

@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    size_t i;
    assert(iota(2, 0).all!((elem){i++; return true;}));
    assert(i == 0);
}

/++
Counts elements in slices according to the `fun`.
Params:
    fun = A predicate.

Optimization:
    `count!"a"` has accelerated specialization for slices created with $(REF bitwise, mir,ndslice,topology).
+/
template count(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    /++
    Params:
        slices = One or more slices.

    Returns: The number elements according to the `fun`.

    Constraints:
        All slices must have the same shape.
    +/
    @fastmath size_t count(Slices...)(Slices slices)
        if (Slices.length && allSatisfy!(isSlice, Slices))
    {
        static if (__traits(isSame, fun, naryFun!"true"))
        {
            return slices[0].elementsCount;
        }
        else
        static if (Slices.length == 1 && kindOf!(Slices[0]) == Contiguous && isSlice!(Slices[0]) != [1])
        {
            import mir.ndslice.topology: flattened;
            return .count!(naryFun!fun)(slices[0].flattened);
        }
        else
        {
            slices.checkShapesMatch;
            if (slices[0].anyEmpty)
                return 0;
            return countImpl!(fun, Slices)(slices);
        }
    }
    else
        alias count = .count!(naryFun!fun);

}

/// Single slice
unittest
{
    import mir.ndslice.topology : iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota(2, 3);

    assert(sl.count!"true" == 6);
    assert(sl.count!"a" == 5);
    assert(sl.count!"a % 2" == 3);
}

/// Accelerated set bit count
unittest
{
    import mir.ndslice.topology: iota, bitwise;
    import mir.ndslice.allocation: slice;

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota(2, 3).bitwise;

    assert(sl.count!"true" == 6 * size_t.sizeof * 8);

    // accelerated
    assert(sl.count!"a" == 7);
    assert(sl.slice.count!"a" == 7);

    auto sl2 = iota!ubyte([6], 128).bitwise;
    assert(sl2.count!"a" == 13);
    assert(sl2[4 .. $].count!"a" == 13);
    assert(sl2[4 .. $ - 1].count!"a" == 12);
    assert(sl2[4 .. $ - 1].count!"a" == 12);
    assert(sl2[41 .. $ - 1].count!"a" == 1);
}

/++
Compares two or more slices for equality, as defined by predicate `pred`.

Params:
    pred = The predicate.
+/
template equal(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = Two or more slices.

    Returns:
        `true` any of the elements verify `pred` and `false` otherwise.
    +/
    bool equal(Slices...)(Slices slices)
        if (Slices.length >= 2)
    {
        enum msg = "all arguments must be slices" ~ tailErrorMessage!();
        enum msgShape = "all slices must have the same dimension count"  ~ tailErrorMessage!();
        import mir.internal.utility;
        foreach (i, Slice; Slices)
        {
            static assert (isSlice!Slice, msg);
            static if (i)
            {
                static assert (isSlice!(Slices[i])[0] == isSlice!(Slices[0])[0]);
                foreach (j; Iota!(isSlice!(Slices[0])[0]))
                    if (slices[i].shape[j] != slices[0].shape[j])
                        goto False;
            }
        }
        return all!pred(slices);
        False: return false;
    }
    else
        alias equal = .equal!(naryFun!pred);
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    assert(equal!"a == b"(sl1, sl1));
    assert(equal!"a < b"(sl1, sl2));

    assert(!equal!"a == b"(sl1[0 .. $ - 1], sl1));
    assert(!equal!"a == b"(sl1[0 .. $, 0 .. $ - 1], sl1));
}

ptrdiff_t cmpImpl(alias pred, SliceKind kindA, SliceKind kindB, size_t[] packsA, size_t[] packsB, IteratorA, IteratorB)
    (Slice!(kindA, packsA, IteratorA) sl1, Slice!(kindB, packsB, IteratorB) sl2)
    if (packsA[0] == packsB[0])
{
    for (;;)
    {
        static if (packsA[0] == 1)
        {
            import mir.functional : naryFun;
            if (naryFun!pred(sl1.front, sl2.front))
                return -1;
            if (naryFun!pred(sl2.front, sl1.front))
                return 1;
        }
        else
        {
            if (auto res = .cmpImpl!pred(sl1.front, sl2.front))
                return res;
        }
        sl1.popFront;
        if (sl1.empty)
            return -cast(ptrdiff_t)(sl2.length > 1);
        sl2.popFront;
        if (sl2.empty)
            return 1;
    }
}

/++
Performs three-way recursive lexicographical comparison on two slices according to predicate `pred`.
Iterating `sl1` and `sl2` in lockstep, `cmp` compares each `N-1` dimensional element `e1` of `sl1`
with the corresponding element `e2` in `sl2` recursively.
If one of the slices has been finished,`cmp` returns a negative value if `sl1` has fewer elements than `sl2`,
a positive value if `sl1` has more elements than `sl2`,
and `0` if the ranges have the same number of elements.

Params:
    pred = The predicate.
+/
template cmp(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        sl1 = First slice.
        sl2 = Second slice.

    Returns:
        `0` if both ranges compare equal.
        Negative value if the first differing element of `sl1` is less than the corresponding
        element of `sl2` according to `pred`.
        Positive value if the first differing element of `sl2` is less than the corresponding
        element of `sl1` according to `pred`.
    +/
    ptrdiff_t cmp(SliceKind kindA, SliceKind kindB, size_t[] packsA, size_t[] packsB, IteratorA, IteratorB)
        (Slice!(kindA, packsA, IteratorA) sl1, Slice!(kindB, packsB, IteratorB) sl2)
        if (packsA[0] == packsB[0])
    {
        auto b = sl2.anyEmpty;
        if (sl1.anyEmpty)
        {
            if (!b)
                return -1;
            import mir.internal.utility;
            foreach (i; Iota!(packsA[0]))
                if (ptrdiff_t ret = sl1.length!i - sl2.length!i)
                    return ret;
            return 0;
        }
        if (b)
            return 1;
        return cmpImpl!pred(sl1, sl2);
    }
    else
        alias cmp = .cmp!(naryFun!pred);
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    assert(cmp(sl1, sl1) == 0);
    assert(cmp(sl1, sl2) < 0);
    assert(cmp!"a >= b"(sl1, sl2) > 0);
}

@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;

    auto sl1 = iota(2, 3);
    auto sl2 = iota([2, 3], 1);

    assert(cmp(sl1[0 .. $ - 1], sl1) < 0);
    assert(cmp(sl1, sl1[0 .. $, 0 .. $ - 1]) > 0);

    assert(cmp(sl1[0 .. $ - 2], sl1) < 0);
    assert(cmp(sl1, sl1[0 .. $, 0 .. $ - 3]) > 0);
    assert(cmp(sl1[0 .. $, 0 .. $ - 3], sl1[0 .. $, 0 .. $ - 3]) == 0);
    assert(cmp(sl1[0 .. $, 0 .. $ - 3], sl1[0 .. $ - 1, 0 .. $ - 3]) > 0);
    assert(cmp(sl1[0 .. $ - 1, 0 .. $ - 3], sl1[0 .. $, 0 .. $ - 3]) < 0);
}

size_t countImpl(alias fun, Slices...)(Slices slices)
{
    size_t ret;
    alias S = Slices[0];
    import mir.functional: naryFun;
    import mir.ndslice.iterator: FieldIterator;
    import mir.ndslice.field: BitwiseField;
    static if (__traits(isSame, fun, naryFun!"a") && 
        is(S : Slice!(Contiguous, [1], Iterator),
            Iterator : FieldIterator!BWF,
            BWF : BitwiseField!Field, Field))
    {
        version(LDC)
            import ldc.intrinsics: ctpop = llvm_ctpop;
        else
            import core.bitop: ctpop = popcnt;
        auto index = slices[0]._iterator._index;
        auto field = slices[0]._iterator._field;
        auto length = slices[0]._lengths[0];
        while (length && (index & field.mask))
        {
            if (field[index])
                ret++;
            index++;
            length--;
        }
        auto j = index >> field.shift;
        foreach(i; size_t(j) .. (length >> field.shift) + j)
            ret += cast(typeof(ret)) ctpop(field._field[i]);
        index += length & ~field.mask;
        length &= field.mask;
        while(length)
        {
            if (field[index])
                ret++;
            index++;
            length--;
        }
    }
    else
    do
    {
        static if (slices[0].shape.length == 1)
        {
            if(fun(staticMap!(frontOf, slices)))
                ret++;
        }
        else
            ret += .countImpl!fun(staticMap!(frontOf, slices));
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return ret;
}
