/++
$(SCRIPT inhibitQuickIndex = 1;)

This is a submodule of $(MREF mir,ndslice).
It contains basic multidimensional iteration algorithms.

$(BOOKTABLE Iteration operators,
$(TR $(TH Operator Name) $(TH Type) $(TH Functions / Seeds #)  $(TH Vectorization) $(TH Tensors #) $(TH Returns) $(TH First Argument)  $(TH Triangular and Half Selection))
$(T8 fold, Eagerly, `>=1`, No, `1`, Scalar, Tensor, No)
$(T8 reduce, Eagerly, `1`, Optional, `>=1`, Scalar, Seed, Yes)
$(T8 each, Eagerly, `1`/`0`, Optional, `>=1`, `void`, Tensor, Yes)
)

$(BOOKTABLE Eagerly iteration operators with stop condition,
$(TR $(TH Operator Name) $(TH Has Needle) $(TH Finds Index) $(TH Tensors #) $(TH Returns) $(TH Requires Equal Shapes) $(TH Triangular and Half Selection))
$(T7 find, No, Yes, `>=1`, `void`, Yes, Yes)
$(T7 any, No, No, `>=1`, `bool`, Yes, Yes)
$(T7 all, No, No, `>=1`, `bool`, Yes, Yes)
$(T7 equal, No, No, `>=2`, `bool`, No, Yes)
$(T7 cmp, No, No, `2`, `int`, No, No)
)

All operators are suitable to change tensors using `ref` argument qualification in a function declaration.

$(H3 Lockstep Iteration)

$(REF_ALTTEXT assumeSameStructure, assumeSameStructure, mir,ndslice,slice)
can be used as multidimensional `zip` analog if tensors have the same structure (shape and strides).
`assumeSameStructure` allows to mutate elements of zipped tensors, which is not possible with common
$(REF zip, std,range).

Also tensors zipped with `assumeSameStructure` uses single set of lengths and strides.
Thus, `assumeSameStructure` may significantly optimize iteration.

If tensors have different strides, then most of existing operators in this module still
can be used as they accept a set of tensors instead of single one.

$(H3 Selection)
$(LREF Select) allows to specify subset of elements to iterate.
$(LREF Select) is useful in combination with $(SUBREF dynamic, transposed) and $(SUBREF dynamic, reversed).

Note:
    $(SUBREF dynamic, transposed) and
    $(SUBREF topology, pack) can be used to specify dimensions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).

Copyright: Copyright © 2016, Ilya Yaroshenko

Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T7=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4) $(TD $5) $(TD $6) $(TD $7))
T8=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4) $(TD $5) $(TD $6) $(TD $7) $(TD $8))
+/
module mir.ndslice.algorithm;

import std.traits;
import std.meta;

import mir.ndslice.internal;
import mir.ndslice.slice;

@fastmath:

private auto ref frontOf(alias slice)() { return slice.front; };

/++
Implements the homonym function (also known as `accumulate`,
`compress`, `inject`, or `foldl`) present in various programming
languages of functional flavor. The call `fold!(fun)(seed, tensors1, ..., tesnsorN)`
first assigns `seed` to an internal variable `result`,
also called the accumulator. Then, for each set of element `x1, ..., xN` in
`tensors1, ..., tensorN`, `result = fun(result, x1, ..., xN)` gets evaluated. Finally,
`result` is returned.

`reduce` allows to iterate multiple tensors in the lockstep.

Note:
    $(SUBREF dynamic, transposed) and
    $(SUBREF topology, pack) can be used to specify dimensions.
Params:
    fun = A function.
    select = Selection type.
    vec = Use vectorization friendly iteration without manual unrolling
        in case of all tensors has the last (row) stride equal to 1.
    fm = Allow a compiler to use unsafe floating-point mathematic transformations,
        such as commutative transformation. `fm` is enabled by default if `vec` is enabled.
    seed = An initial accumulation value.
    tensors = One or more tensors.
Returns:
    the accumulated `result`
See_Also:
    $(HTTP llvm.org/docs/LangRef.html#fast-math-flags, LLVM IR: Fast Math Flags)

    This is functionally similar to $(LREF reduce) with the argument order reversed.
    $(LREF fold) allows to compute values for multiple functions.

    $(REF reduce, std,algorithm,iteration)

    $(HTTP en.wikipedia.org/wiki/Fold_(higher-order_function), Fold (higher-order function))
+/
template reduce(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    ///
    @fastmath auto reduce(S, Slices...)(S seed, Slices slices)
        if (Slices.length)
    {
        //slices.checkShapesMatch;
        if (slices[0].anyEmpty)
            return cast(Unqual!S) seed;
        static if (is(S : Unqual!S))
            alias UT = Unqual!S;
        else
            alias UT = S;
        import mir.functional: naryFun;
        return reduceImpl!(naryFun!fun, UT, Slices)(seed, slices);
    }
    else
        alias reduce = .reduce!(naryFun!fun);

}

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


/// Single tensor
unittest
{
    import mir.ndslice.topology : iota;

    //| 0 1 2 | => 3  |
    //| 3 4 5 | => 12 | => 15
    auto sl = iota(2, 3);

    // sum of all element in the tensor
    auto res = size_t(0).reduce!"a + b"(sl);

    assert(res == 15);
}

/// Multiple tensors, dot product
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

/// Zipped tensors, dot product
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

    // tensors must have the same strides for `zip!true`.
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
Packed tensors.

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


/++
The call `each!(fun)(tensors1, ..., tesnsorN)`
evaluates `fun` for each set of elements `x1, ..., xN` in
`tensors1, ..., tensorN` respectively.

`each` allows to iterate multiple tensors in the lockstep.

Note:
    $(SUBREF dynamic, transposed) and
    $(SUBREF topology, pack) can be used to specify dimensions.
Params:
    fun = A function.
    select = Selection type.
    vec = Use vectorization friendly iteration without manual unrolling
        in case of all tensors has the last (row) stride equal to 1.
    fm = Allow a compiler to use unsafe floating-point mathematic transformations,
        such as commutative transformation. `fm` is enabled by default if `vec` is enabled.
    tensors = One or more tensors.
See_Also:
    $(HTTP llvm.org/docs/LangRef.html#fast-math-flags, LLVM IR: Fast Math Flags)

    This is functionally similar to $(LREF reduce) but has not seed.

    $(REF each, std,algorithm,iteration)
+/
template each(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    ///
    @fastmath auto each(Slices...)(Slices slices)
        if (Slices.length)
    {
        //slices.checkShapesMatch;
        if (slices[0].anyEmpty)
            return;
        eachImpl!(naryFun!fun, Slices)(slices);
    }
    else
        alias each = .each!(naryFun!fun);
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

/// Single tensor, multiply-add
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

/// Swap two tensors
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

/// Swap two zipped tensors
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

version(none):

// one ring to rule them all
private template implement(Iteration iteration, alias fun)
{
    static if (fm)
        alias attr = fastmath;
    else
        alias attr = fastmathDummy;

    static if (iteration == Iteration.reduce)
        enum argStr = "S, Tensors...)(S seed, Tensors tensors)";
    else
    static if (iteration == Iteration.find)
        enum argStr = "size_t M, Tensors...)(ref size_t[M] backwardIndex, Tensors tensors)";
    else
        enum argStr = "Tensors...)(Tensors tensors)";

    auto implement(size_t N, Select select, Tensors...)(Tensors tensors) {
        static if (iteration == Iteration.find)
        {
            static if (select == Select.halfPacked || select == Select.triangularPacked)
                enum S = N + tensors[0].front.N;
            else
                enum S = N;
            static assert (M == S, "backwardIndex length should be equal to " ~ S.stringof);
        }
        static if (select == Select.half)
        {
            immutable lengthSave = tensors[0].length;
            tensors[0].popBackExactly(tensors[0].length / 2 + tensors[0].length % 2);
            if (tensors[0].length == 0)
                goto End;
        }
        static if (select == Select.halfPacked)
            static if (packs[0] == 1)
                enum nextSelect = Select.half;
            else
                enum nextSelect = Select.halfPacked;
        else
        static if (select == Select.triangularPacked)
            static if (packs[0] == 1)
                enum nextSelect = Select.triangular;
            else
                enum nextSelect = Select.triangularPacked;
        else
        static if (packs[0] == 1)
            enum nextSelect = -1;
        else
        static if (select == Select.half)
            enum nextSelect = Select.full;
        else
            enum nextSelect = select;
        static if (select == Select.triangular)
            alias popSeq = Iota!(0, N);
        else
            alias popSeq = AliasSeq!(size_t(0));
        static if (N == 1 && (select == Select.halfPacked || select == Select.triangularPacked))
            enum M = tensors[0].front.shape.length;
        else
            enum M = packs[0] - 1;
        static if (iteration == Iteration.reduce)
            static if (nextSelect == -1)
                enum compute = `seed = naryFun!(true, Tensors.length, fun)(seed, ` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
                enum compute = `seed = implement!(M, nextSelect)(seed, ` ~ TensorFronts!(Tensors.length) ~ `);`;
        else
        static if (iteration == Iteration.each)
            static if (nextSelect == -1)
                enum compute = `naryFun!(false, Tensors.length, fun)(` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
                enum compute = `implement!(M, nextSelect)(` ~ TensorFronts!(Tensors.length) ~ `);`;
        else
        static if (iteration == Iteration.find)
            static if (nextSelect == -1)
                enum compute = `auto val = naryFun!(false, Tensors.length, fun)(` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
                enum compute = `implement!(M, nextSelect)(backwardIndex[1 .. $] , ` ~ TensorFronts!(Tensors.length) ~ `);`;
        else
        static if (iteration == Iteration.all)
            static if (nextSelect == -1)
                enum compute = `auto val = naryFun!(false, Tensors.length, fun)(` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
                enum compute = `auto val = implement!(M, nextSelect)(` ~ TensorFronts!(Tensors.length) ~ `);`;
        else
        static assert(0);
        enum breakStr = q{
            static if (iteration == Iteration.find)
            {
                static if (nextSelect != -1)
                    auto val = backwardIndex[$ - 1];
                if (val)
                {
                    backwardIndex[0] = tensors[0].length;
                    static if (select == Select.half)
                        backwardIndex[0] += lengthSave - (lengthSave >> 1);
                    return;
                }
            }
            else
            static if (iteration == Iteration.all)
            {
                if (!val)
                    return false;
            }
        };
        do
        {
            mixin(compute);
            mixin(breakStr);
            foreach_reverse (t, ref tensor; tensors)
            {
                foreach (d; popSeq)
                {
                    static if (d == M && vec && __VERSION__ < 2072)
                    {
                        ++tensor._ptr;
                        static if (t == 0)
                            --tensors[0]._lengths[0];
                    }
                    else
                    {
                        tensor.popFront!d;
                    }
                }
            }
        }
        while (tensors[0].length);
        End:
        static if (select == Select.half && N > 1)
        {
            static if (iteration == Iteration.reduce)
                enum computeHalf = `seed = implement!(packs[0] - 1, Select.half)(seed, ` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
            static if (iteration == Iteration.each)
                enum computeHalf = `implement!(packs[0] - 1, Select.half)(` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
            static if (iteration == Iteration.find)
                enum computeHalf = `implement!(packs[0] - 1, Select.half)(backwardIndex[1 .. $] , ` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
            static if (iteration == Iteration.all)
                enum computeHalf = `auto val = implement!(packs[0] - 1, Select.half)(` ~ TensorFronts!(Tensors.length) ~ `);`;
            else
            static assert(0);
            if (lengthSave & 1)
            {
                tensors[0].popBackN(tensors[0].length - 1);
                mixin(computeHalf);
                mixin(breakStr);
            }
        }
        static if (iteration == Iteration.reduce)
            return seed;
        else
        static if (iteration == Iteration.all)
            return true;
    };
}

/++
Finds a backward index for which
`pred(tensors[0].backward(index), ..., tensors[$-1].backward(index))` equals `true`.

Params:
    pred = The predicate.
    select = Selection type.
    backwardIndex = The variable passing by reference to be filled with the multidimensional backward index for which the predicate is true.
        `backwardIndex` equals zeros, if the predicate evaluates `false` for all indexes.
    tensors = One or more tensors.

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

Constraints:
    All tensors must have the same shape.

See_also:
    $(LREF any)

    $(REF Slice.backward, mir,ndslice,slice)
+/
template find(alias pred, Select select = Select.full)
{
    ///
    void find(size_t N, Args...)(out size_t[N] backwardIndex, Args tensors)
        if (Args.length)
    {
        tensors.checkShapesMatch!(false, select);
        if (!anyEmpty!select(tensors[0]))
        {
            prepareTensors!select(tensors);
            alias impl = implement!(Iteration.find, pred, No.vectorized, No.fastmath);
            impl!(Args[0].N, select)(backwardIndex, tensors);
        }
    }
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;
    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);
    size_t[2] bi;

    find!"a == 3"(bi, sl);
    assert(sl.backward(bi) == 3);

    find!"a == 6"(bi, sl);
    assert(bi[0] == 0);
    assert(bi[1] == 0);
}

/// Multiple tensors
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    size_t[2] bi;

    find!((a, b) => a * b == 39)(bi, a, b);
    assert(a.backward(bi) == 3);
    assert(b.backward(bi) == 13);
}

/// Zipped tensors
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    // tensors must have the same strides
    auto zip = assumeSameStructure!("a", "b")(a, b);
    size_t[2] bi;

    find!((z) => z.a * z.b == 39)(bi, zip);

    assert(a.backward(bi) == 3);
    assert(b.backward(bi) == 13);
}

/// Mutation on-the-fly
pure nothrow unittest
{
    import std.conv : to;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : iota;

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

    size_t[2] bi;
    find!pred(bi, sl);

    assert(bi == [1, 1]);
    assert(sl.backward(bi) == 5);

    // sl was changed
    assert(sl == [[8, 8, 8],
                  [8, 8, 5]]);
}

/// Search in triangular matrix
pure nothrow unittest
{
    import std.conv : to;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : iota;

    // |_0 1 2
    // 3 |_4 5
    // 6 7 |_8
    auto sl = iota(3, 3).as!double.slice;
    size_t[2] bi;
    find!("a > 5", Select.triangular)(bi, sl);
    assert(sl.backward(bi) == 8);
}

/// Search of first non-palindrome row
pure nothrow unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.dynamic : reversed;
    import mir.ndslice.topology : iota, pack;

    auto sl = slice!double(4, 5);
    sl[] =
        [[0, 1, 2, 1, 0],
         [2, 3, 4, 3, 2],
         [6, 9, 8, 5, 6],
         [6, 5, 8, 5, 6]];

    size_t[2] bi;
    find!("a != b", Select.halfPacked)(bi, sl.pack!1, sl.reversed!1.pack!1);
    assert(sl.backward(bi) == 9);
}

@safe pure nothrow unittest
{
    import mir.ndslice.dynamic : dropOne;
    import mir.ndslice.topology : iota;
    size_t i;
    size_t[2] bi;
    find!((elem){i++; return true;})
        (bi, iota(2, 1).dropOne!1);
    assert(i == 0);
    assert(bi == [0, 0]);
}

/++
Selection type.
`Select` can be used with
$(LREF reduce),
$(LREF each),
$(LREF find),
$(LREF any),
$(LREF all),
$(LREF equal),
$(LREF cmp).

Any dimension count is supported.
Types has examples for 1D, 2D, and 3D cases.
+/
enum Select
{
    /++
    `full` is the default topology type.

    1D Example:
    -----
    1 2 3
    -----
    2D Example:
    -----
    | 1 2 3 |
    | 4 5 6 |
    | 7 8 9 |
    -----
    3D Example:
    -----
    | 1  2  3 | | 10 11 12 | | 19 20 21 |
    | 4  5  6 | | 13 14 15 | | 22 23 24 |
    | 7  8  9 | | 16 17 18 | | 25 26 27 |
    -----
    +/
    full,
    /++
    `half` can be used to reverse elements in a tensor.

    1D Example:
    -----
    1 x x
    -----
    2D Example:
    -----
    | 1 2 3 |
    | 4 x x |
    | x x x |
    -----
    3D Example:
    -----
    | 1  2  3 | | 10 11 12 | |  x  x  x |
    | 4  5  6 | | 13  x  x | |  x  x  x |
    | 7  8  9 | |  x  x  x | |  x  x  x |
    -----
    +/
    half,
    /++
    `halfPacked` requires packed tensors.
    For the first pack of dimensions elements are selected using `full` topology.
    For the second pack of dimensions elements are selected using `half` topology.
    +/
    halfPacked,
    /++
    `upper` can be used to iterate on upper or lower triangular matrix.

    1D Example:
    -----
    1 2 3
    -----
    2D Example #1:
    -----
    | 1 2 3 |
    | x 4 5 |
    | x x 6 |
    -----
    2D Example #2:
    -----
    | 1 2 3 4 |
    | x 5 6 7 |
    | x x 8 9 |
    -----
    2D Example #3:
    -----
    | 1 2 3 |
    | x 4 5 |
    | x x 6 |
    | x x x |
    -----
    3D Example:
    -----
    |  1  2  3 | |  x  7  8 | |  x  x 10 |
    |  x  4  5 | |  x  x  9 | |  x  x  x |
    |  x  x  6 | |  x  x  x | |  x  x  x |
    -----
    +/
    triangular,
    /++
    `triangularPacked` requires packed tensors.
    For the first pack of dimensions elements are selected using `full` topology.
    For the second pack of dimensions elements are selected using `triangular` topology.
    +/
    triangularPacked,
}

/++
Like $(LREF find), but only returns whether or not the search was successful.

Params:
    pred = The predicate.
    select = Selection type.
    tensors = One or more tensors.

Returns:
    `true` if the search was successful and `false` otherwise.

Constraints:
    All tensors must have the same shape.
+/
template any(alias pred, Select select = Select.full)
{
    ///
    bool any(Args...)(Args tensors)
        if (Args.length)
    {
        tensors.checkShapesMatch!(false, select);
        if (anyEmpty!select(tensors[0]))
            return false;
        size_t[Args[0].N] backwardIndex = void;
        backwardIndex[$-1] = 0;
        prepareTensors!select(tensors);
        alias impl = implement!(Iteration.find, pred, No.vectorized, No.fastmath);
        impl!(Args[0].N, select)(backwardIndex, tensors);
        return cast(bool) backwardIndex[$-1];
    }
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

/// Multiple tensors
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

/// Zipped tensors
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    // tensors must have the same strides
    auto zip = assumeSameStructure!("a", "b")(a, b);

    assert(zip.any!((z) => z.a * z.b == 39));
}

/// Mutation on-the-fly
pure nothrow unittest
{
    import std.conv : to;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : iota;

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

/++
Checks if all of the elements verify `pred`.
Params:
    pred = The predicate.
    select = Selection type.
    tensors = One or more tensors.
Returns:
    `true` all of the elements verify `pred` and `false` otherwise.
Constraints:
    All tensors must have the same shape.
+/
template all(alias pred, Select select = Select.full)
{
    ///
    bool all(Args...)(Args tensors)
        if (Args.length)
    {
        tensors.checkShapesMatch!(false, select);
        prepareTensors!select(tensors);
        alias impl = implement!(Iteration.all, pred, No.vectorized, No.fastmath);
        return anyEmpty!select(tensors[0]) || impl!(Args[0].N, select)(tensors);
    }
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

/// Multiple tensors
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    assert(all!"a - b == 0"(sl, sl));
}

/// Zipped tensors
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    // tensors must have the same strides
    auto zip = assumeSameStructure!("a", "b")(sl, sl);

    assert(zip.all!"a.a - a.b == 0");
}

/// Mutation on-the-fly
pure nothrow unittest
{
    import std.conv : to;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : iota;

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
    import mir.ndslice.dynamic : dropOne;
    import mir.ndslice.topology : iota;
    size_t i;
    assert(all!((elem){i++; return true;})
        (iota(2, 1).dropOne!1));
    assert(i == 0);
}

/++
Compares two or more tensors for equality, as defined by predicate `pred`.

Params:
    pred = The predicate.
    select = Selection type.
    tensors = Two or more tensors.

Returns:
    `true` any of the elements verify `pred` and `false` otherwise.
+/
template equal(alias pred, Select select = Select.full)
{
    ///
    bool equal(Args...)(Args tensors)
        if (Args.length >= 2)
    {
        enum msg = "all arguments must be tensors" ~ tailErrorMessage!();
        enum msgShape = "all tensors must have the same dimension count"  ~ tailErrorMessage!();
        prepareTensors!select(tensors);
        foreach (i, Arg; Args)
        {
            static assert (is(Arg == Slice!(kind,packs, Iterator), size_t[] packs, Iterator), msg);
            static if (i)
            {
                static assert (tensors[i].N == tensors[0].N, msgShape);
                foreach (j; Iota!(0, tensors[0].N))
                    if (tensors[i].shape[j] != tensors[0].shape[j])
                        goto False;
            }
        }
        return all!(pred, select)(tensors);
        False: return false;
    }
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.dynamic : dropBackOne;
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    assert(equal!"a == b"(sl1, sl1));
    assert(equal!"a < b"(sl1, sl2));

    assert(!equal!"a == b"(sl1.dropBackOne!0, sl1));
    assert(!equal!"a == b"(sl1.dropBackOne!1, sl1));
}

/// check if matrix is symmetric
pure nothrow unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.dynamic : transposed;

    auto a = slice!double(3, 3);
    a[] = [[1, 3, 4],
           [3, 5, 8],
           [4, 8, 2]];

    alias isSymmetric = matrix => equal!("a == b", Select.triangular)(matrix, matrix.transposed);

    assert(isSymmetric(a));

    a[0, 0] = double.nan;
    assert(!isSymmetric(a)); // nan != nan
    a[0, 0] = 1;

    a[1, 0] = 2;
    assert(!isSymmetric(a)); // 2 != 3
    a[1, 0] = 3;

    a.popFront;
    assert(!isSymmetric(a)); // a is not square
}

/++
Performs three-way recursive lexicographical comparison on two tensors according to predicate `pred`.
Iterating `sl1` and `sl2` in lockstep, `cmp` compares each `N-1` dimensional element `e1` of `sl1`
with the corresponding element `e2` in `sl2` recursively.
If one of the tensors has been finished,`cmp` returns a negative value if `sl1` has fewer elements than `sl2`,
a positive value if `sl1` has more elements than `sl2`,
and `0` if the ranges have the same number of elements.

Params:
    pred = The predicate.
    sl1 = First tensor.
    sl2 = Second tensor.

Returns:
    `0` if both ranges compare equal.
    Negative value if the first differing element of `sl1` is less than the corresponding
    element of `sl2` according to `pred`.
    Positive value if the first differing element of `sl2` is less than the corresponding
    element of `sl1` according to `pred`.
+/
template cmp(alias pred = "a < b")
{
    ///
    int cmp(size_t[] packs, IteratorA, IteratorB)(Slice!(packs, IteratorA) sl1, Slice!(packs, IteratorB) sl2)
    {
        auto b = sl2.anyEmpty;
        if (sl1.anyEmpty)
        {
            if (!b)
                return -1;
            foreach (i; Iota!(0, N))
                if (sl1.length!i < sl2.length!i)
                    return -1;
                else
                if (sl1.length!i > sl2.length!i)
                    return 1;
            return 0;
        }
        if (b)
            return 1;
        return cmpImpl(sl1, sl2);
    }

    private int cmpImpl(size_t[] packs, IteratorA, IteratorB)(Slice!(packs, IteratorA) sl1, Slice!(packs, IteratorB) sl2)
    {
        for (;;)
        {
            auto a = sl1.front;
            auto b = sl2.front;
            static if (packs[0] == 1)
            {
                import mir.functional : naryFun;
                if (naryFun!pred(a, b))
                    return -1;
                if (naryFun!pred(b, a))
                    return 1;
            }
            else
            {
                if (auto res = cmpImpl(a, b))
                    return res;
            }
            sl1.popFront;
            if (sl1.empty)
                return -cast(int)(sl2.length > 1);
            sl2.popFront;
            if (sl2.empty)
                return 1;
        }
    }
}

///
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.dynamic : dropBackOne;
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
    import mir.ndslice.dynamic : dropBackOne, dropExactly;
    import mir.ndslice.topology : iota;

    auto sl1 = iota(2, 3);
    auto sl2 = iota([2, 3], 1);

    assert(cmp(sl1.dropBackOne!0, sl1) < 0);
    assert(cmp(sl1, sl1.dropBackOne!1) > 0);

    assert(cmp(sl1.dropExactly!0(2), sl1) < 0);
    assert(cmp(sl1, sl1.dropExactly!1(3)) > 0);
    assert(cmp(sl1.dropExactly!1(3), sl1.dropExactly!1(3)) == 0);
    assert(cmp(sl1.dropExactly!1(3), sl1.dropExactly!(0, 1)(1, 3)) > 0);
    assert(cmp(sl1.dropExactly!(0, 1)(1, 3), sl1.dropExactly!1(3)) < 0);
}
