/++
$(H2 Multidimensional iteration algorithms)

This is a submodule of $(MREF mir,ndslice).

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
$(T2 all, Checks if all elements satisfy to a predicate.)
$(T2 any, Checks if at least one element satisfy to a predicate.)
$(T2 cmp, Compares two slices.)
$(T2 count, Counts elements in a slices according to a predicate.)
$(T2 each, Iterates all elements.)
$(T2 equal, Compares two slices for equality.)
$(T2 find, Finds backward index.)
$(T2 findIndex, Finds index.)
$(T2 isSymmetric, Checks if the matrix is symmetric.)
$(T2 maxIndex, Finds index of the maximum.)
$(T2 maxPos, Finds backward index of the maximum.)
$(T2 minIndex, Finds index of the minimum.)
$(T2 minmaxIndex, Finds indexes of the minimum and the maximum.)
$(T2 minmaxPos, Finds backward indexes of the minimum and the maximum.)
$(T2 minPos, Finds backward index of the minimum.)
$(T2 reduce, Accumulates all elements.)
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

import mir.primitives;
import mir.ndslice.internal;
import mir.internal.utility;
import mir.ndslice.slice;

@fastmath:

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

template frontOf(size_t N)
{
    static if (N == 0)
        enum frontOf = "";
    else
    {
        enum i = N - 1;
        enum frontOf = frontOf!i ~ "slices[" ~ i.stringof ~ "].front, ";
    }
}

S reduceImpl(alias fun, S, Slices...)(S seed, Slices slices)
{
    do
    {
        static if (slices[0].shape.length == 1)
            seed = mixin("fun(seed, " ~ frontOf!(Slices.length) ~ ")");
        else
            seed = mixin(".reduceImpl!fun(seed," ~ frontOf!(Slices.length) ~ ")");
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
        slices = One or more slices, range, and arrays.
    Returns:
        the accumulated `result`
    +/
    @fastmath auto reduce(S, Slices...)(S seed, Slices slices)
        if (Slices.length)
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

/// Ranges and arrays
unittest
{
    auto ar = [1, 2, 3];
    auto s = 0.reduce!"a + b"(ar);
    assert (s == 6);
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

    //| 0 1 2 |
    //| 3 4 5 |
    auto a = iota([2, 3], 0).as!double.slice;
    //| 1 2 3 |
    //| 4 5 6 |
    auto b = iota([2, 3], 1).as!double.slice;

    alias dot = reduce!"a + b * c";
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
    import mir.math.common;
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
            mixin("fun(" ~ frontOf!(Slices.length) ~ ");");
        else
            mixin(".eachImpl!fun(" ~ frontOf!(Slices.length) ~ ");");
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
        slices = One or more slices, ranges, and arrays.
    +/
    @fastmath auto each(Slices...)(Slices slices)
        if (Slices.length)
    {
        slices.checkShapesMatch;
        if (slices[0].anyEmpty)
            return;
        eachImpl!fun(slices);
    }
    else
        alias each = .each!(naryFun!fun);
}

/// Ranges and arrays
unittest
{
    auto ar = [1, 2, 3];
    ar.each!"a *= 2";
    assert (ar == [2, 4, 6]);
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

/++
The call `eachUploPair!(fun)(matrix)`
evaluates `fun` for each pair (`matrix[j, i]`, `matrix[i, j]`),
for i <= j (default) or i < j (if includeDiagonal is false).

Params:
    fun = A function.
    includeDiagonal = true (default) if applying function to diagonal, 
                      false otherwise.
+/
template eachUploPair(alias fun, bool includeDiagonal = true)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    {
        /++
        Params:
            matrix = Square matrix.
        +/
        auto eachUploPair(SliceKind kind, Iterator)
                                            (Slice!(kind, [2], Iterator) matrix)
        in
        {
            assert(matrix.length!0 == matrix.length!1, "matrix must be square.");
        }
        body
        {
            static if (kind == Contiguous)
            {
                import mir.ndslice.topology: canonical;

                .eachUploPair!(fun, includeDiagonal)(matrix.canonical);
            }
            else
            {
                if (!matrix.empty)
                {
                    import mir.ndslice.algorithm: eachImpl;

                    static if (includeDiagonal == true)
                    {
                        do
                        {
                            eachImpl!fun(matrix.front!0, matrix.front!1);
                            matrix.popFront!1;
                            matrix.popFront!0;
                        }
                        while (matrix.length);
                    }
                    else
                    {
                        do
                        {
                            eachImpl!fun(matrix.front!0[1 .. $],
                                         matrix.front!1[1 .. $]);
                            matrix.popFront!1;
                            matrix.popFront!0;
                        }
                        while (matrix.length - 1);
                    }
                }
            }
        }
    }
    else
    {
        alias eachUploPair = .eachUploPair!(naryFun!fun, includeDiagonal);
    }
}

/// Transpose matrix in place.
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota, universal;
    import mir.ndslice.dynamic: transposed;
    import mir.utility: swap;

    auto m = iota(4, 4).slice;

    m.eachUploPair!swap;

    assert(m == iota(4, 4).universal.transposed);
}

/// Reflect Upper matrix part to lower part.
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota, universal;
    import mir.ndslice.dynamic: transposed;
    import mir.utility: swap;

    // 0 1 2
    // 3 4 5
    // 6 7 8
    auto m = iota(3, 3).slice;

    m.eachUploPair!((u, ref l) { l = u; });

    assert(m == [
        [0, 1, 2],
        [1, 4, 5],
        [2, 5, 8]]);
}

/// Fill lower triangle with zeroes.
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    // 1 2 3
    // 4 5 6
    // 7 8 9
    auto m = iota([3, 3], 1).slice;

    m.eachUploPair!((u, ref l) { l = 0; }, false);

    assert(m == [
        [1, 2, 3],
        [0, 5, 6],
        [0, 0, 9]]);
}

unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    // 0 1 2
    // 3 4 5
    // 6 7 8
    auto m = iota(3, 3).slice;
    m.eachUploPair!((u, ref l) { l = l + 1; }, true);
    assert(m == [
        [1, 1, 2],
        [4, 5, 5],
        [7, 8, 9]]);
}

unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    // 0 1 2
    // 3 4 5
    // 6 7 8
    auto m = iota(3, 3).slice;
    m.eachUploPair!((u, ref l) { l = l + 1; }, false);

    assert(m == [
        [0, 1, 2],
        [4, 4, 5],
        [7, 8, 8]]);
}

/++
Checks if the matrix is symmetric.
+/
template isSymmetric(alias fun = "a == b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    /++
    Params:
        matrix = 2D ndslice.
    +/
    bool isSymmetric(SliceKind kind, Iterator)(Slice!(kind, [2], Iterator) matrix)
    {
        static if (kind == Contiguous)
        {
            import mir.ndslice.topology: canonical;
            return .isSymmetric!fun(matrix.canonical);
        }
        else
        {
            if (matrix.length!0 != matrix.length!1)
                return false;
            if (!matrix.empty)
            do
            {
                import mir.ndslice.algorithm: eachImpl;
                if (!allImpl!fun(matrix.front!0, matrix.front!1))
                {
                    return false;
                }
                matrix.popFront!1;
                matrix.popFront!0;
            }
            while (matrix.length);
            return true;
        }
    }
    else
        alias isSymmetric = .isSymmetric!(naryFun!fun);
}

///
unittest
{
    import mir.ndslice.topology: iota;
    assert(iota(2, 2).isSymmetric == false);

    assert(
        [1, 2,
         2, 3].sliced(2, 2).isSymmetric == true);
}

bool minPosImpl(alias fun, SliceKind kind, size_t[] packs, Iterator)(ref size_t[packs[0]] backwardIndex, ref Iterator iterator, Slice!(kind, packs, Iterator) slice)
    if (packs.length == 1)
{
    auto bis = backwardIndex[0];
    do
    {
        static if (slice.shape.length == 1)
        {
            if (fun(*slice._iterator, *iterator))
            {
                backwardIndex[0] = slice.length;
                iterator = slice._iterator;
            }
        }
        else
        {
            if (minPosImpl!(fun, kind, [packs[0] - 1], Iterator)(backwardIndex[1 .. $], iterator, slice.front))
            {
                backwardIndex[0] = slice.length;
            }
        }
        slice.popFront;
    }
    while(!slice.empty);
    return bis != backwardIndex[0];
}

bool[2] minmaxPosImpl(alias fun, SliceKind kind, size_t[] packs, Iterator)(ref size_t[2][packs[0]] backwardIndex, ref Iterator[2] iterator, Slice!(kind, packs, Iterator) slice)
    if (packs.length == 1)
{
    size_t[2] bis = backwardIndex[0];
    do
    {
        static if (slice.shape.length == 1)
        {
            if (fun(*slice._iterator, *iterator[0]))
            {
                backwardIndex[0][0] = slice.length;
                iterator[0] = slice._iterator;
            }
            else
            if (fun(*iterator[1], *slice._iterator))
            {
                backwardIndex[0][1] = slice.length;
                iterator[1] = slice._iterator;
            }
        }
        else
        {
            auto r = minmaxPosImpl!(fun, kind, [packs[0] - 1], Iterator)(backwardIndex[1 .. $], iterator, slice.front);
            if (r[0])
            {
                backwardIndex[0][0] = slice.length;
            }
            if (r[1])
            {
                backwardIndex[0][1] = slice.length;
            }
        }
        slice.popFront;
    }
    while(!slice.empty);
    return [bis[0] != backwardIndex[0][0], bis[1] != backwardIndex[0][1]];
}

/++
Finds a positions (ndslices) such that
`position[0].first` is minimal and `position[1].first` is maximal elements in the slice.

Position is sub-ndslice of the same dimension in the right-$(RPAREN)down-$(RPAREN)etc$(LPAREN)$(LPAREN) corner.

Params:
    pred = A predicate.

See_also:
    $(LREF minmaxIndex),
    $(LREF minPos),
    $(LREF maxPos),
    $(SUBREF slice, Slice.backward).
+/
template minmaxPos(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        2 subslices with minimal and maximal `first` elements.
    +/
    @fastmath Slice!(kind == Contiguous && packs[0] > 1 ? Canonical : kind, packs, Iterator)[2]
        minmaxPos(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    {
        import mir.ndslice.topology: map;
        typeof(return) pret;
        if (!slice.anyEmpty)
        {
            size_t[2][packs[0]] ret;
            auto it = slice.map!"a"._iterator;
            Iterator[2] iterator = [it, it];
            minmaxPosImpl!(pred, kind, packs, Iterator)(ret, iterator, slice);
            foreach (i; Iota!(packs[0]))
            {
                pret[0]._lengths[i] = ret[i][0];
                pret[1]._lengths[i] = ret[i][1];
            }
            static if (packs.length > 1)
            {
                pret[0]._iterator = iterator[0]._iterator;
                pret[1]._iterator = iterator[1]._iterator;
            }
            else
            {
                pret[0]._iterator = iterator[0];
                pret[1]._iterator = iterator[1];
            }
        }
        static if (packs.length > 1)
        {
            foreach (i; Iota!(packs[0], slice.N))
            {
                pret[0]._lengths[i] = slice._lengths[i];
                pret[1]._lengths[i] = slice._lengths[i];
            }
        }
        auto strides = slice.strides;
        foreach(i; Iota!(0, pret[0].S))
        {
            pret[0]._strides[i] = strides[i];
            pret[1]._strides[i] = strides[i];
        }
        return pret;
    }
    else
        alias minmaxPos = .minmaxPos!(naryFun!pred);
}

///
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 2,
        ].sliced(3, 4);

    auto pos = s.minmaxPos;

    assert(pos[0] == s[$ - 2 .. $, $ - 3 .. $]);
    assert(pos[1] == s[$ - 1 .. $, $ - 2 .. $]);

    assert(pos[0].first == -4);
    assert(s.backward(pos[0].shape) == -4);
    assert(pos[1].first ==  7);
    assert(s.backward(pos[1].shape) ==  7);
}

/++
Finds a backward indexes such that
`slice[indexes[0]]` is minimal and `slice[indexes[1]]` is maximal elements in the slice.

Params:
    pred = A predicate.

See_also:
    $(LREF minmaxIndex),
    $(LREF minPos),
    $(LREF maxPos),
    $(REF Slice.backward, mir,ndslice,slice).
+/
template minmaxIndex(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        Subslice with minimal (maximal) `first` element.
    +/
    @fastmath size_t[packs[0]][2] minmaxIndex(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    {
        import mir.ndslice.topology: map;
        typeof(return) pret = size_t.max;
        if (!slice.anyEmpty)
        {
            size_t[2][packs[0]] ret = [slice.shape, slice.shape];
            auto it = slice.map!"a"._iterator;
            Iterator[2] iterator = [it, it];
            minmaxPosImpl!(pred, kind, packs, Iterator)(ret, iterator, slice);
            foreach (i; Iota!(packs[0]))
            {
                pret[0][i] = slice._lengths[i] - ret[i][0];
                pret[1][i] = slice._lengths[i] - ret[i][1];
            }
        }
        return pret;
    }
    else
        alias minmaxIndex = .minmaxIndex!(naryFun!pred);
}

///
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 8,
        ].sliced(3, 4);

    auto indexes = s.minmaxIndex;

    assert(indexes == [[1, 1], [2, 3]]);
    assert(s[indexes[0]] == -4);
    assert(s[indexes[1]] ==  8);
}

/++
Finds a backward index such that
`slice.backward(index)` is minimal(maximal).

Params:
    pred = A predicate.

See_also:
    $(LREF minIndex),
    $(LREF maxPos),
    $(LREF maxIndex),
    $(REF Slice.backward, mir,ndslice,slice).
+/
template minPos(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        Multidimensional backward index such that element is minimal(maximal).
        Backward index equals zeros, if slice is empty.
    +/
    @fastmath Slice!(kind == Contiguous && packs[0] > 1 ? Canonical : kind, packs, Iterator)
        minPos(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    {
        typeof(return) ret;
        import mir.ndslice.topology: map;
        if (!slice.anyEmpty)
        {
            auto iterator = slice.map!"a"._iterator;
            minPosImpl!(pred, kind, packs, Iterator)(ret._lengths, iterator, slice);
            static if (packs.length > 1)
            {
                ret._iterator = iterator._iterator;
            }
            else
            {
                ret._iterator = iterator;
            }
        }
        static if (packs.length > 1)
        {
            foreach (i; Iota!(packs[0], slice.N))
            {
                ret._lengths[i] = slice._lengths[i];
            }
        }
        auto strides = slice.strides;
        foreach(i; Iota!(0, ret.S))
        {
            ret._strides[i] = strides[i];
        }
        return ret;
    }
    else
        alias minPos = .minPos!(naryFun!pred);
}

/// ditto
template maxPos(alias pred = "a < b")
{
    import mir.functional: naryFun, reverseArgs;
    alias maxPos = minPos!(reverseArgs!(naryFun!pred));
}

///
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 2,
        ].sliced(3, 4);

    auto pos = s.minPos;

    assert(pos == s[$ - 2 .. $, $ - 3 .. $]);
    assert(pos.first == -4);
    assert(s.backward(pos.shape) == -4);

    pos = s.maxPos;

    assert(pos == s[$ - 1 .. $, $ - 2 .. $]);
    assert(pos.first == 7);
    assert(s.backward(pos.shape) == 7);
}

/++
Finds an index such that
`slice[index]` is minimal(maximal).

Params:
    pred = A predicate.

See_also:
    $(LREF minIndex),
    $(LREF maxPos),
    $(LREF maxIndex).
+/
template minIndex(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        Multidimensional index such that element is minimal(maximal).
        Index elements equal to `size_t.max`, if slice is empty.
    +/
    @fastmath size_t[packs[0]] minIndex(SliceKind kind, ptrdiff_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    {
        size_t[packs[0]] ret = size_t.max;
        import mir.ndslice.topology: map;
        if (!slice.anyEmpty)
        {
            ret = slice.shape;
            auto iterator = slice.map!"a"._iterator;
            minPosImpl!(pred, kind, packs, Iterator)(ret, iterator, slice);
            foreach (i; Iota!(packs[0]))
                ret[i] = slice._lengths[i] - ret[i];
        }
        return ret;
    }
    else
        alias minIndex = .minIndex!(naryFun!pred);
}

/// ditto
template maxIndex(alias pred = "a < b")
{
    import mir.functional: naryFun, reverseArgs;
    alias maxIndex = minIndex!(reverseArgs!(naryFun!pred));
}

///
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 8,
        ].sliced(3, 4);

    auto index = s.minIndex;

    assert(index == [1, 1]);
    assert(s[index] == -4);

    index = s.maxIndex;

    assert(index == [2, 3]);
    assert(s[index] == 8);
}

///
unittest
{
    auto s = [
        -8, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 8,
        ].sliced(3, 4);

    auto index = s.minIndex;

    assert(index == [0, 0]);
    assert(s[index] == -8);
}

bool findImpl(alias fun, size_t N, Slices...)(ref size_t[N] backwardIndex, Slices slices)
    if (Slices.length)
{
    do
    {
        static if (slices[0].shape.length == 1)
        {
            if (mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
            {
                backwardIndex[0] = slices[0].length;
                return true;
            }
        }
        else
        {
            if (mixin("findImpl!fun(backwardIndex[1 .. $], " ~ frontOf!(Slices.length) ~ ")"))
            {
                backwardIndex[0] = slices[0].length;
                return true;
            }
        }
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return false;
}

/++
Finds an index such that
`pred(slices[0][index], ..., slices[$-1][index])` is `true`.

Params:
    pred = A predicate.

See_also:
    $(LREF find),
    $(LREF any).
+/
template findIndex(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        Multidimensional index such that the predicate is true.
        Index equals `size_t.max`, if the predicate evaluates `false` for all indexes.
    Constraints:
        All slices must have the same shape.
    +/
    @fastmath size_t[DimensionCount!(Slices[0])] findIndex(Slices...)(Slices slices)
        if (Slices.length)
    {
        slices.checkShapesMatch;
        typeof(return) ret = -1;
        auto lengths = slices[0].shape;
        if (!slices[0].anyEmpty && findImpl!pred(ret, slices))
            foreach (i; Iota!(typeof(return).length))
                ret[i] = lengths[i] - ret[i];
        return ret;
    }
    else
        alias findIndex = .findIndex!(naryFun!pred);
}

/// Ranges and arrays
unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto sl = iota(5);
    size_t index = sl.findIndex!"a == 3"[0];

    assert(index == 3);
    assert(sl[index] == 3);
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;
    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);
    size_t[2] index = sl.findIndex!"a == 3";

    assert(sl[index] == 3);

    index = sl.findIndex!"a == 6";
    assert(index[0] == size_t.max);
    assert(index[1] == size_t.max);
}

/++
Finds a backward index such that
`pred(slices[0].backward(index), ..., slices[$-1].backward(index))` is `true`.

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
    $(LREF findIndex),
    $(LREF any),
    $(REF Slice.backward, mir,ndslice,slice).
+/
template find(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        Multidimensional backward index such that the predicate is true.
        Backward index equals zeros, if the predicate evaluates `false` for all indexes.
    Constraints:
        All slices must have the same shape.
    +/
    @fastmath size_t[DimensionCount!(Slices[0])] find(Slices...)(Slices slices)
        if (Slices.length)
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

/// Ranges and arrays
unittest
{
    import std.range : iota;

    auto sl = iota(10);
    size_t index = sl.find!"a == 3"[0];

    assert(sl[$ - index] == 3);
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
    if (Slices.length)
{
    do
    {
        static if (slices[0].shape.length == 1)
        {
            if (mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
                return true;
        }
        else
        {
            if (mixin("anyImpl!fun(" ~ frontOf!(Slices.length) ~ ")"))
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
template any(alias pred = "a")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices, ranges, and arrays.
    Returns:
        `true` if the search was successful and `false` otherwise.
    Constraints:
        All slices must have the same shape.
    +/
    @fastmath bool any(Slices...)(Slices slices)
        if ((Slices.length == 1 || !__traits(isSame, pred, "a")) && Slices.length)
    {
        slices.checkShapesMatch;
        return !slices[0].anyEmpty && anyImpl!pred(slices);
    }
    else
        alias any = .any!(naryFun!pred);
}

/// Ranges and arrays
@safe pure nothrow @nogc unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto r = iota(6);

    assert(r.any!"a == 3");
    assert(!r.any!"a == 6");
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
    if (Slices.length)
{
    do
    {
        static if (slices[0].shape.length == 1)
        {
            if (!mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
                return false;
        }
        else
        {
            if (!mixin("allImpl!fun(" ~ frontOf!(Slices.length) ~ ")"))
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
template all(alias pred = "a")
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
        if ((Slices.length == 1 || !__traits(isSame, pred, "a")) && Slices.length)
    {
        slices.checkShapesMatch;
        return slices[0].anyEmpty || allImpl!pred(slices);
    }
    else
        alias all = .all!(naryFun!pred);
}

/// Ranges and arrays
@safe pure nothrow @nogc unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto r = iota(6);

    assert(r.all!"a < 6");
    assert(!r.all!"a < 5");
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
        slices = One or more slices, ranges, and arrays.

    Returns: The number elements according to the `fun`.

    Constraints:
        All slices must have the same shape.
    +/
    @fastmath size_t count(Slices...)(Slices slices)
        if (Slices.length)
    {
        static if (__traits(isSame, fun, naryFun!"true"))
        {
            return slices[0].elementsCount;
        }
        else
        {
            static if (isSlice!(Slices[0]))
                enum flat = Slices.length == 1 && kindOf!(Slices[0]) == Contiguous && packsOf!(Slices[0]) != [1];
            else
                enum flat = false;
            static if (flat)
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
    }
    else
        alias count = .count!(naryFun!fun);

}

/// Ranges and arrays
@safe pure nothrow @nogc unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto r = iota(6);

    assert(r.count!"true" == 6);
    assert(r.count!"a" == 5);
    assert(r.count!"a % 2" == 3);
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

See_also: $(SUBREF slice, Slice.opEquals)

Params:
    pred = The predicate.
+/
template equal(alias pred = "a == b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = Two or more slices, slices, ranges, and arrays.

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
            // static assert (isSlice!Slice, msg);
            static if (i)
            {
                static assert (DimensionCount!(Slices[i]) == DimensionCount!(Slices[0]));
                foreach (j; Iota!(DimensionCount!(Slices[0])))
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

/// Ranges and arrays
@safe pure nothrow unittest
{
    import std.range : iota;
    auto r = iota(6);
    assert(r.equal([0, 1, 2, 3, 4, 5]));
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

    assert(equal(sl1, sl1));
    assert(sl1 == sl1); //can also use opEquals for two Slices
    assert(equal!"2 * a == b + c"(sl1, sl1, sl1));
    
    assert(equal!"a < b"(sl1, sl2));

    assert(!equal(sl1[0 .. $ - 1], sl1));
    assert(!equal(sl1[0 .. $, 0 .. $ - 1], sl1));
}

ptrdiff_t cmpImpl(alias pred, A, B)
    (A sl1, B sl2)
    if (DimensionCount!A == DimensionCount!B)
{
    for (;;)
    {
        static if (DimensionCount!A == 1)
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
        sl1 = First slice, range, or array.
        sl2 = Second slice, range, or array.

    Returns:
        `0` if both ranges compare equal.
        Negative value if the first differing element of `sl1` is less than the corresponding
        element of `sl2` according to `pred`.
        Positive value if the first differing element of `sl2` is less than the corresponding
        element of `sl1` according to `pred`.
    +/
    ptrdiff_t cmp(A, B)
        (A sl1, B sl2)
        if (DimensionCount!A == DimensionCount!B)
    {
        auto b = sl2.anyEmpty;
        if (sl1.anyEmpty)
        {
            if (!b)
                return -1;
            auto sh1 = sl1.shape;
            auto sh2 = sl2.shape;
            foreach (i; Iota!(DimensionCount!A))
                if (ptrdiff_t ret = sh1[i] - sh2[i])
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

/// Ranges and arrays
@safe pure nothrow unittest
{
    import std.range : iota;

    // 0 1 2 3 4 5
    auto r1 = iota(0, 6);
    // 1 2 3 4 5 6
    auto r2 = iota(1, 7);

    assert(cmp(r1, r1) == 0);
    assert(cmp(r1, r2) < 0);
    assert(cmp!"a >= b"(r1, r2) > 0);
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
            if(mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
                ret++;
        }
        else
            ret += mixin(".countImpl!fun(" ~ frontOf!(Slices.length) ~ ")");
        foreach(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return ret;
}
