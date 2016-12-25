/**
$(SCRIPT inhibitQuickIndex = 1;)

This is a submodule of $(MREF mir, ndslice).

Operators only change strides and lengths of a slice.
The range of a slice remains unmodified.
All operators return slice of the same type as the type of the argument.

$(BOOKTABLE $(H2 Transpose operators),

$(TR $(TH Function Name) $(TH Description))
$(T2 transposed, Permutes dimensions. $(BR)
    `iota(3, 4, 5, 6, 7).transposed!(4, 0, 1).shape` returns `[7, 3, 4, 5, 6]`.)
$(T2 swapped, Swaps dimensions $(BR)
    `iota(3, 4, 5).swapped!(1, 2).shape` returns `[3, 5, 4]`.)
$(T2 everted, Reverses the order of dimensions $(BR)
    `iota(3, 4, 5).everted.shape` returns `[5, 4, 3]`.)
)
See also $(SUBREF topology, evertPack).

$(BOOKTABLE $(H2 Iteration operators),

$(TR $(TH Function Name) $(TH Description))
$(T2 strided, Multiplies the stride of a selected dimension by a factor.$(BR)
    `iota(13, 40).strided!(0, 1)(2, 5).shape` equals to `[7, 8]`.)
$(T2 reversed, Reverses the direction of iteration for selected dimensions. $(BR)
    `slice.reversed!0` returns the slice with reversed direction of iteration for top level dimension.)
$(T2 allReversed, Reverses the direction of iteration for all dimensions. $(BR)
    `iota(4, 5).allReversed` equals to `20.iota.retro.sliced(4, 5)`.)
)

$(BOOKTABLE $(H2 Other operators),
$(TR $(TH Function Name) $(TH Description))
$(T2 rotated, Rotates two selected dimensions by `k*90` degrees. $(BR)
    `iota(2, 3).rotated` equals to `[[2, 5], [1, 4], [0, 3]]`.)
)

$(H4 Drop operators)

$(LREF dropToHypercube)

$(H2 Bifacial operators)

Some operators are bifacial,
i.e. they have two versions: one with template parameters, and another one
with function parameters. Versions with template parameters are preferable
because they allow compile time checks and can be optimized better.

$(BOOKTABLE ,

$(TR $(TH Function Name) $(TH Variadic) $(TH Template) $(TH Function))
$(T4 swapped, No, `slice.swapped!(2, 3)`, `slice.swapped(2, 3)`)
$(T4 rotated, No, `slice.rotated!(2, 3)(-1)`, `slice.rotated(2, 3, -1)`)
$(T4 strided, Yes/No, `slice.strided!(1, 2)(20, 40)`, `slice.strided(1, 20).strided(2, 40)`)
$(T4 transposed, Yes, `slice.transposed!(1, 4, 3)`, `slice.transposed(1, 4, 3)`)
$(T4 reversed, Yes, `slice.reversed!(0, 2)`, `slice.reversed(0, 2)`)
)

Bifacial interface of $(LREF drop), $(LREF dropBack)
$(LREF dropExactly), and $(LREF dropBackExactly)
is identical to that of $(LREF strided).

Bifacial interface of $(LREF dropOne) and $(LREF dropBackOne)
is identical to that of $(LREF reversed).

License:   BSD 3-Clause License

Copyright: Copyright © 2016, Ilya Yaroshenko

Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
*/
module mir.ndslice.dynamic;


import std.traits;
import std.meta;

import mir.internal.utility;
import mir.ndslice.internal;
import mir.ndslice.slice;

@fastmath:


private enum _swappedCode = q{
    with (slice)
    {
        auto tl = _lengths[dimensionA];
        auto ts = _strides[dimensionA];
        _lengths[dimensionA] = _lengths[dimensionB];
        _strides[dimensionA] = _strides[dimensionB];
        _lengths[dimensionB] = tl;
        _strides[dimensionB] = ts;
    }
    return slice;
};

/++
Swaps two dimensions.

Params:
    slice = input slice
    dimensionA = first dimension
    dimensionB = second dimension
Returns:
    n-dimensional slice of the same type
See_also: $(LREF everted), $(LREF transposed)
+/
template swapped(size_t dimensionA, size_t dimensionB)
{
    @fastmath auto swapped(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice)
    {
        {
            enum i = 0;
            alias dimension = dimensionA;
            mixin DimensionCTError;
        }
        {
            enum i = 1;
            alias dimension = dimensionB;
            mixin DimensionCTError;
        }
        mixin (_swappedCode);
    }
}

/// ditto
Slice!(SliceKind.universal, packs, Iterator) swapped(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice, size_t dimensionA, size_t dimensionB)
in{
    {
        alias dimension = dimensionA;
        mixin (DimensionRTError);
    }
    {
        alias dimension = dimensionB;
        mixin (DimensionRTError);
    }
}
body
{
    mixin (_swappedCode);
}

/// ditto
Slice!(SliceKind.universal, [2], Iterator) swapped(Iterator)(Slice!(SliceKind.universal, [2], Iterator) slice)
body
{
    return slice.swapped!(0, 1);
}

/// Template
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4, 5, 6)
        .universal
        .swapped!(3, 1)
        .shape == cast(size_t[4])[3, 6, 5, 4]);
}

/// Function
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4, 5, 6)
        .universal
        .swapped(1, 3)
        .shape == cast(size_t[4])[3, 6, 5, 4]);
}

/// 2D
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4)
        .universal
        .swapped
        .shape == cast(size_t[2])[4, 3]);
}

private enum _rotatedCode = q{
    k &= 0b11;
    if (k == 0)
        return slice;
    if (k == 2)
        return slice.allReversed;
    static if (__traits(compiles, { enum _enum = dimensionA + dimensionB; }))
    {
        slice = slice.swapped!(dimensionA, dimensionB);
        if (k == 1)
            return slice.reversed!dimensionA;
        else
            return slice.reversed!dimensionB;
    }
    else
    {
        slice = slice.swapped (dimensionA, dimensionB);
        if (k == 1)
            return slice.reversed(dimensionA);
        else
            return slice.reversed(dimensionB);
    }
};

/++
Rotates two selected dimensions by `k*90` degrees.
The order of dimensions is important.
If the slice has two dimensions, the default direction is counterclockwise.

Params:
    slice = input slice
    dimensionA = first dimension
    dimensionB = second dimension
    k = rotation counter, can be negative
Returns:
    n-dimensional slice of the same type
+/
template rotated(size_t dimensionA, size_t dimensionB)
{
    @fastmath auto rotated(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice, sizediff_t k = 1)
    {
        {
            enum i = 0;
            alias dimension = dimensionA;
            mixin DimensionCTError;
        }
        {
            enum i = 1;
            alias dimension = dimensionB;
            mixin DimensionCTError;
        }
        mixin (_rotatedCode);
    }
}

/// ditto
Slice!(SliceKind.universal, packs, Iterator) rotated(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice,
    size_t dimensionA, size_t dimensionB, sizediff_t k = 1)
in{
    {
        alias dimension = dimensionA;
        mixin (DimensionRTError);
    }
    {
        alias dimension = dimensionB;
        mixin (DimensionRTError);
    }
}
body
{
    mixin (_rotatedCode);
}

/// ditto
Slice!(SliceKind.universal, [2], Iterator) rotated(Iterator)(Slice!(SliceKind.universal, [2], Iterator) slice, sizediff_t k = 1)
body
{
    return slice.rotated!(0, 1)(k);
}

/// Template
@safe pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    auto slice = iota(2, 3).universal;

    auto a = [[0, 1, 2],
              [3, 4, 5]];

    auto b = [[2, 5],
              [1, 4],
              [0, 3]];

    auto c = [[5, 4, 3],
              [2, 1, 0]];

    auto d = [[3, 0],
              [4, 1],
              [5, 2]];

    assert(slice.rotated       ( 4) == a);
    assert(slice.rotated!(0, 1)(-4) == a);
    assert(slice.rotated (1, 0,  8) == a);

    assert(slice.rotated            == b);
    assert(slice.rotated!(0, 1)(-3) == b);
    assert(slice.rotated (1, 0,  3) == b);

    assert(slice.rotated       ( 6) == c);
    assert(slice.rotated!(0, 1)( 2) == c);
    assert(slice.rotated (0, 1, -2) == c);

    assert(slice.rotated       ( 7) == d);
    assert(slice.rotated!(0, 1)( 3) == d);
    assert(slice.rotated (1, 0,   ) == d);
}

/++
Reverses the order of dimensions.

Params:
    slice = input slice
Returns:
    n-dimensional slice of the same type
See_also: $(LREF swapped), $(LREF transposed)
+/
Slice!(SliceKind.universal, packs, Iterator) everted(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice)
{
    mixin _DefineRet;
    with (slice)
    {
         foreach (i; Iota!(packs[0]))
        {
            ret._lengths[N - 1 - i] = _lengths[i];
            ret._strides[N - 1 - i] = _strides[i];
        }
        foreach (i; Iota!(packs[0], slice.N))
        {
            ret._lengths[i] = _lengths[i];
            ret._strides[i] = _strides[i];
        }
        ret._iterator = _iterator;
        return ret;
    }
}

///
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4, 5)
        .universal
        .everted
        .shape == cast(size_t[3])[5, 4, 3]);
}

private enum _transposedCode = q{
    mixin _DefineRet;
    with (slice)
    {
        foreach (i; Iota!(packs[0]))
        {
            ret._lengths[i] = _lengths[perm[i]];
            ret._strides[i] = _strides[perm[i]];
        }
        foreach (i; Iota!(packs[0], slice.N))
        {
            ret._lengths[i] = _lengths[i];
            ret._strides[i] = _strides[i];
        }
        ret._iterator = _iterator;
        return ret;
    }
};

private size_t[N] completeTranspose(size_t N)(size_t[] dimensions)
{
    assert(dimensions.length <= N);
    size_t[N] ctr;
    uint[N] mask;
    foreach (i, ref dimension; dimensions)
    {
        mask[dimension] = true;
        ctr[i] = dimension;
    }
    size_t j = dimensions.length;
    foreach (i, e; mask)
        if (e == false)
            ctr[j++] = i;
    return ctr;
}

/++
N-dimensional transpose operator.
Brings selected dimensions to the first position.
Params:
    slice = input slice
    Dimensions = indexes of dimensions to be brought to the first position
    dimensions = indexes of dimensions to be brought to the first position
    dimension = index of dimension to be brought to the first position
Returns:
    n-dimensional slice of the same type
See_also: $(LREF swapped), $(LREF everted)
+/
template transposed(Dimensions...)
    if (Dimensions.length)
{
    static if (!allSatisfy!(isSize_t, Dimensions))
        alias transposed = .transposed!(staticMap!(toSize_t, Dimensions));
    else
    @fastmath Slice!(SliceKind.universal, packs, Iterator) transposed(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice)
    {
        mixin DimensionsCountCTError;
        foreach (i, dimension; Dimensions)
            mixin DimensionCTError;
        static assert(isValidPartialPermutation!(packs[0])([Dimensions]),
            "Failed to complete permutation of dimensions " ~ Dimensions.stringof
            ~ tailErrorMessage!());
        enum perm = completeTranspose!(packs[0])([Dimensions]);
        static assert(perm.isPermutation, __PRETTY_FUNCTION__ ~ ": internal error.");
        mixin (_transposedCode);
    }
}

///ditto
Slice!(SliceKind.universal, packs, Iterator) transposed(size_t[] packs, Iterator, size_t M)(Slice!(SliceKind.universal, packs, Iterator) slice, size_t[M] dimensions...)
in
{
    mixin (DimensionsCountRTError);
    foreach (dimension; dimensions)
        mixin (DimensionRTError);
}
body
{
    assert(dimensions.isValidPartialPermutation!(packs[0]),
        "Failed to complete permutation of dimensions."
        ~ tailErrorMessage!());
    immutable perm = completeTranspose!(packs[0])(dimensions);
    assert(perm.isPermutation, __PRETTY_FUNCTION__ ~ ": internal error.");
    mixin (_transposedCode);
}

///ditto
Slice!(SliceKind.universal, [2], Iterator) transposed(Iterator)(Slice!(SliceKind.universal, [2], Iterator) slice)
{
    return .transposed!(1, 0)(slice);
}

/// Template
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4, 5, 6, 7)
        .universal
        .transposed!(4, 1, 0)
        .shape == cast(size_t[5])[7, 4, 3, 5, 6]);
}

/// Function
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4, 5, 6, 7)
        .universal
        .transposed(4, 1, 0)
        .shape == cast(size_t[5])[7, 4, 3, 5, 6]);
}

/// Single-argument function
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4, 5, 6, 7)
        .universal
        .transposed(4)
        .shape == cast(size_t[5])[7, 3, 4, 5, 6]);
}

/// _2-dimensional transpose
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology : iota;
    assert(iota(3, 4)
        .universal
        .transposed
        .shape == cast(size_t[2])[4, 3]);
}

private enum _reversedCode = q{
    with (slice)
    {
        if (_lengths[dimension])
            _iterator += _strides[dimension] * (_lengths[dimension] - 1);
        _strides[dimension] = -_strides[dimension];
    }
};

/++
Reverses the direction of iteration for all dimensions.
Params:
    slice = input slice
Returns:
    n-dimensional slice of the same type
+/
Slice!(SliceKind.universal, packs, Iterator) allReversed(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice)
{
    foreach (dimension; Iota!(packs[0]))
    {
        mixin (_reversedCode);
    }
    return slice;
}

/////
//@safe @nogc pure nothrow unittest
//{
//    import mir.ndslice.slice;
//    import std.range : iota, retro;
//    auto a = 20.iota
//        .sliced(4, 5)
//        .allReversed;
//    auto b = 20.iota.retro.sliced(4, 5);
//    assert(a == b);
//}

/++
Reverses the direction of iteration for selected dimensions.

Params:
    slice = input slice
    Dimensions = indexes of dimensions to reverse order of iteration
    dimensions = indexes of dimensions to reverse order of iteration
    dimension = index of dimension to reverse order of iteration
Returns:
    n-dimensional slice of the same type
+/
template reversed(Dimensions...)
    if (Dimensions.length)
{
    static if (!allSatisfy!(isSize_t, Dimensions))
        alias reversed = .reversed!(staticMap!(toSize_t, Dimensions));
    else
    @fastmath auto reversed(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice)
    {
        foreach (i, dimension; Dimensions)
        {
            mixin DimensionCTError;
            mixin (_reversedCode);
        }
        return slice;
    }
}

///ditto
Slice!(SliceKind.universal, packs, Iterator) reversed(size_t[] packs, Iterator, size_t M)(Slice!(SliceKind.universal, packs, Iterator) slice, size_t[M] dimensions...)
in
{
    foreach (dimension; dimensions)
        mixin (DimensionRTError);
}
body
{
    foreach (i; Iota!(0, M))
    {
        auto dimension = dimensions[i];
        mixin (_reversedCode);
    }
    return slice;
}

///
pure nothrow unittest
{
    import mir.ndslice.slice;
    auto slice = [1, 2, 3, 4].sliced(2, 2).universal;
    assert(slice                    == [[1, 2], [3, 4]]);

    // Template
    assert(slice.reversed! 0        == [[3, 4], [1, 2]]);
    assert(slice.reversed! 1        == [[2, 1], [4, 3]]);
    assert(slice.reversed!(0, 1)    == [[4, 3], [2, 1]]);
    assert(slice.reversed!(1, 0)    == [[4, 3], [2, 1]]);
    assert(slice.reversed!(1, 1)    == [[1, 2], [3, 4]]);
    assert(slice.reversed!(0, 0, 0) == [[3, 4], [1, 2]]);

    // Function
    assert(slice.reversed (0)       == [[3, 4], [1, 2]]);
    assert(slice.reversed (1)       == [[2, 1], [4, 3]]);
    assert(slice.reversed (0, 1)    == [[4, 3], [2, 1]]);
    assert(slice.reversed (1, 0)    == [[4, 3], [2, 1]]);
    assert(slice.reversed (1, 1)    == [[1, 2], [3, 4]]);
    assert(slice.reversed (0, 0, 0) == [[3, 4], [1, 2]]);
}

//@safe @nogc pure nothrow unittest
//{
//    import mir.ndslice.slice;
//    import mir.ndslice.topology;
//    import std.algorithm.comparison : equal;
//    import std.range : iota, retro, chain;
//    auto i0 = iota(0,  4); auto r0 = i0.retro;
//    auto i1 = iota(4,  8); auto r1 = i1.retro;
//    auto i2 = iota(8, 12); auto r2 = i2.retro;
//    auto slice = 12.iota.sliced(3, 4).universal;
//    assert(slice                   .flattened.equal(chain(i0, i1, i2)));
//    // Template
//    assert(slice.reversed!(0)      .flattened.equal(chain(i2, i1, i0)));
//    assert(slice.reversed!(1)      .flattened.equal(chain(r0, r1, r2)));
//    assert(slice.reversed!(0, 1)   .flattened.equal(chain(r2, r1, r0)));
//    assert(slice.reversed!(1, 0)   .flattened.equal(chain(r2, r1, r0)));
//    assert(slice.reversed!(1, 1)   .flattened.equal(chain(i0, i1, i2)));
//    assert(slice.reversed!(0, 0, 0).flattened.equal(chain(i2, i1, i0)));
//    // Function
//    assert(slice.reversed (0)      .flattened.equal(chain(i2, i1, i0)));
//    assert(slice.reversed (1)      .flattened.equal(chain(r0, r1, r2)));
//    assert(slice.reversed (0, 1)   .flattened.equal(chain(r2, r1, r0)));
//    assert(slice.reversed (1, 0)   .flattened.equal(chain(r2, r1, r0)));
//    assert(slice.reversed (1, 1)   .flattened.equal(chain(i0, i1, i2)));
//    assert(slice.reversed (0, 0, 0).flattened.equal(chain(i2, i1, i0)));
//}

private enum _stridedCode = q{
    assert(factor > 0, "factor must be positive"
        ~ tailErrorMessage!());
    immutable rem = slice._lengths[dimension] % factor;
    slice._lengths[dimension] /= factor;
    if (slice._lengths[dimension]) //do not remove `if (...)`
        slice._strides[dimension] *= factor;
    if (rem)
        slice._lengths[dimension]++;
};

/++
Multiplies the stride of the selected dimension by a factor.

Params:
    slice = input slice
    Dimensions = indexes of dimensions to be strided
    dimensions = indexes of dimensions to be strided
    factors = list of step extension factors
    factor = step extension factors
Returns:
    n-dimensional slice of the same type
+/
template strided(Dimensions...)
    if (Dimensions.length)
{
    static if (!allSatisfy!(isSize_t, Dimensions))
        alias strided = .strided!(staticMap!(toSize_t, Dimensions));
    else
    @fastmath auto strided(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice, Repeat!(Dimensions.length, size_t) factors)
    body
    {
        foreach (i, dimension; Dimensions)
        {
            mixin DimensionCTError;
            immutable factor = factors[i];
            mixin (_stridedCode);
        }
        return slice;
    }
}

///ditto
Slice!(SliceKind.universal, packs, Iterator) strided(size_t[] packs, Iterator)(Slice!(SliceKind.universal, packs, Iterator) slice, size_t dimension, size_t factor)
in
{
    mixin (DimensionRTError);
}
body
{
    mixin (_stridedCode);
    return slice;
}

///
pure nothrow unittest
{
    import mir.ndslice.slice;
    auto slice
         = [0,1,2,3,    4,5,6,7,   8,9,10,11].sliced(3, 4).universal;

    assert(slice
        == [[0,1,2,3], [4,5,6,7], [8,9,10,11]]);

    // Template
    assert(slice.strided!0(2)
        == [[0,1,2,3],            [8,9,10,11]]);

    assert(slice.strided!1(3)
        == [[0,    3], [4,    7], [8,     11]]);

    assert(slice.strided!(0, 1)(2, 3)
        == [[0,    3],            [8,     11]]);

    // Function
    assert(slice.strided(0, 2)
        == [[0,1,2,3],            [8,9,10,11]]);

    assert(slice.strided(1, 3)
        == [[0,    3], [4,    7], [8,     11]]);

    assert(slice.strided(0, 2).strided(1, 3)
        == [[0,    3],            [8,     11]]);
}

///
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    static assert(iota(13, 40).universal.strided!(0, 1)(2, 5).shape == [7, 8]);
    static assert(iota(93).universal.strided!(0, 0)(7, 3).shape == [5]);
}

//@safe @nogc pure nothrow unittest
//{
//    import mir.ndslice.slice;
//    import mir.ndslice.topology;
//    import std.algorithm.comparison : equal;
//    import std.range : iota, stride, chain;
//    auto i0 = iota(0,  4); auto s0 = i0.stride(3);
//    auto i1 = iota(4,  8); auto s1 = i1.stride(3);
//    auto i2 = iota(8, 12); auto s2 = i2.stride(3);
//    auto slice = 12.iota.sliced(3, 4);
//    assert(slice              .flattened.equal(chain(i0, i1, i2)));
//    // Template
//    assert(slice.strided!0(2) .flattened.equal(chain(i0, i2)));
//    assert(slice.strided!1(3) .flattened.equal(chain(s0, s1, s2)));
//    assert(slice.strided!(0, 1)(2, 3).flattened.equal(chain(s0, s2)));
//    // Function
//    assert(slice.strided(0, 2).flattened.equal(chain(i0, i2)));
//    assert(slice.strided(1, 3).flattened.equal(chain(s0, s1, s2)));
//    assert(slice.strided(0, 2).strided(1, 3).flattened.equal(chain(s0, s2)));
//}

/++
Returns maximal multidimensional cube.

Params:
    slice = input slice
Returns:
    n-dimensional slice of the same type
+/
Slice!(kind, packs, Iterator) dropToHypercube(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    if (kind == SliceKind.canonical || kind == SliceKind.universal)
body
{
    size_t length = slice._lengths[0];
    foreach (i; Iota!(1, packs[0]))
        if (length > slice._lengths[i])
            length = slice._lengths[i];
    foreach (i; Iota!(packs[0]))
        slice._lengths[i] = length;
    return slice;
}

///
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    assert(iota(5, 3, 6, 7)
        .universal
        .dropToHypercube
        .shape == cast(size_t[4])[3, 3, 3, 3]);
}
