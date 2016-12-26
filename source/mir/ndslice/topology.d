/**
$(SCRIPT inhibitQuickIndex = 1;)

This is a submodule of $(MREF mir, ndslice).

Selectors create new views and iteration patterns over the same data, without copying.

$(H2 Subspace selectors)

Subspace selectors serve to generalize and combine other selectors easily.
For a slice of `Slice!(N, Iterator)` type `slice.pack!K` creates a slice of
slices of `Slice!(N-K, Slice!(K+1, Iterator))` type by packing
the last `K` dimensions of the top dimension pack,
and the type of element of `slice.flattened` is `Slice!(K, Iterator)`.
Another way to use $(LREF pack) is transposition of dimension packs using
$(LREF evertPack). Examples of use of subspace selectors are available for selectors,
$(SUBREF slice, Slice.shape), and $(SUBREF slice, Slice.elementsCount).

$(BOOKTABLE ,

$(TR $(TH Function Name) $(TH Description))
$(T2 pack     , returns slice of slices)
$(T2 unpack   , merges all dimension packs)
$(T2 evertPack, reverses dimension packs)
)

$(BOOKTABLE $(H2 Selectors),

$(TR $(TH Function Name) $(TH Description))
$(T2 blocks, n-dimensional slice composed of n-dimensional non-overlapping blocks.
    If the slice has two dimensions, it is a block matrix.)
$(T2 flattened, flat, random access range of all elements with `index` property)
$(T2 diagonal, 1-dimensional slice composed of diagonal elements)
$(T2 ndiota, lazy slice with initial multidimensional index)
$(T2 iota, lazy slice with initial flattened (continuous) index)
$(T2 map, lazy multidimensional functional map)
$(T2 repeat, slice with identical values)
$(T2 reshape, new slice with changed dimensions for the same data)
$(T2 windows, n-dimensional slice of n-dimensional overlapping windows.
    If the slice has two dimensions, it is a sliding window.)
)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).

Copyright: Copyright © 2016, Ilya Yaroshenko

Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, std,experimental, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
*/
module mir.ndslice.topology;

import std.traits;
import std.meta; //: allSatisfy;

import mir.ndslice.internal;
import mir.internal.utility;
import mir.ndslice.slice; //: Slice;
import mir.ndslice.iterator;
import mir.ndslice.field;


auto universal(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
{
    static if (kind == SliceKind.universal)
    {
        return slice;
    }
    else
    static if (is(Iterator : RetroIterator!It, It))
    {
        return slice.retro.universal;
    }
    else
    {
        alias Ret = Slice!(SliceKind.universal, packs, Iterator);
        mixin _DefineRet_;
        foreach (i; Iota!(slice.N))
            ret._lengths[i] = slice._lengths[i];
        static if (kind == SliceKind.canonical)
        {
            foreach (i; Iota!(slice.S))
                ret._strides[i] = slice._strides[i];
            ret._strides[$-1] = 1;
        }
        else
        {
            ptrdiff_t ball = 1;
            foreach_reverse (i; Iota!(ret.S))
            {
                ret._strides[i] = ball;
                static if (i)
                    ball *= slice._lengths[i];
            }
        }
        ret._iterator = slice._iterator;
        return ret;
    }
}

Slice!(packs.sum == 1 ? SliceKind.continuous : SliceKind.canonical, packs, Iterator)
    canonical
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
    if (kind == SliceKind.continuous || kind == SliceKind.canonical)
{
    static if (kind == SliceKind.canonical || packs.sum == 1)
        return slice;
    else
    {
        mixin _DefineRet;
        foreach (i; Iota!(slice.N))
            ret._lengths[i] = slice._lengths[i];
        ptrdiff_t ball = 1;
        foreach_reverse (i; Iota!(ret.S))
        {
            ball *= slice._lengths[i + 1];
            ret._strides[i] = ball;
        }
        ret._iterator = slice._iterator;
        return ret;
    }
}

Slice!(SliceKind.canonical, packs, Iterator)
    assumeCanonical
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
{
    static if (kind == SliceKind.continuous)
        return slice.canonical;
    static if (kind == SliceKind.canonical)
        return slice;
    else
    {
        mixin _DefineRet;
        foreach (i; Iota!(slice.N))
            ret._lengths[i] = slice._lengths[i];
        foreach (i; Iota!(ret.S))
            ret._strides[i] = slice._strides[i];
        ret._iterator = slice._iterator;
        return ret;
    }
}

Slice!(SliceKind.continuous, packs, Iterator)
    assumeContinious
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
{
    static if (kind == SliceKind.continuous)
        return slice;
    else
    {
        mixin _DefineRet;
        foreach (i; Iota!(slice.N))
            ret._lengths[i] = slice._lengths[i];
        ret._iterator = slice._iterator;
        return ret;
    }
}

/++
Creates a packed slice, i.e. slice of slices.
The function does not carry out any calculations, it simply returns the same
binary data presented differently.

Params:
    K = sizes of dimension packs
Returns:
    `pack!K` returns `Slice!(N-K, Slice!(K+1, Iterator))`;
    `slice.pack!(K1, K2, ..., Kn)` is the same as `slice.pack!K1.pack!K2. ... pack!Kn`.
+/
Slice!(kind, [packs[0] - p, p] ~ packs[1 .. $], Iterator)
pack(size_t p, SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    if (p)
{
    static assert(p < packs[0], "pack = " ~ p.stringof
                ~ " should be less than packs[0] = "~ packs[0].stringof
                ~ tailErrorMessage!());
    return typeof(return)(slice._lengths, slice._strides, slice._iterator);
}

Slice!(kind, [p, packs[0] - p] ~ packs[1 .. $], Iterator)
ipack(size_t p, SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    if (p)
{
    static assert(p < packs[0], "pack = " ~ p.stringof
                ~ " should be less than packs[0] = "~ packs[0].stringof
                ~ tailErrorMessage!());
    return typeof(return)(slice._lengths, slice._strides, slice._iterator);
}

///
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice : sliced, Slice;

    auto a = iota(3, 4, 5, 6);
    auto b = a.pack!2;

    static immutable res1 = [3, 4];
    static immutable res2 = [5, 6];
    assert(b.shape == res1);
    assert(b[0, 0].shape == res2);
    assert(a == b);
    static assert(is(typeof(b) == typeof(a.pack!2)));
    static assert(is(typeof(b) == Slice!(SliceKind.continuous, [2, 2], IotaIterator!size_t)));
}

@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    auto a = iota(3, 4, 5, 6, 7, 8, 9, 10, 11);
    auto b = a.pack!2.pack!3;
    auto c = b[1, 2, 3, 4];
    auto d = c[5, 6, 7];
    auto e = d[8, 9];
    auto g = a[1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert(e == g);
    assert(a == b);
    assert(c == a[1, 2, 3, 4]);
    static assert(is(typeof(b) == typeof(a.pack!2.pack!3)));
    static assert(is(typeof(b) == Slice!(SliceKind.continuous, [4, 3, 2], IotaIterator!size_t)));
    static assert(is(typeof(c) == Slice!(SliceKind.continuous, [3, 2], IotaIterator!size_t)));
    static assert(is(typeof(d) == Slice!(SliceKind.continuous, [2], IotaIterator!size_t)));
    static assert(is(typeof(e) == size_t));
}

@safe @nogc pure nothrow unittest
{
    auto a = iota(3, 4, 5, 6, 7, 8, 9, 10, 11);
    auto b = a.pack!2.pack!3;
    static assert(b.shape.length == 4);
    static assert(b.strides.length == 4);
    static assert(b
        .flattened.front
        .shape.length == 3);
    static assert(b
        .flattened.front
        .flattened.front
        .shape.length == 2);
    // test save
    b.flattened.save.popFront;
    static assert(b
        .flattened.front
        .shape.length == 3);
}

/++
Unpacks a packed slice.

The function does not carry out any calculations, it simply returns the same
binary data presented differently.

Params:
    slice = packed slice
Returns:
    unpacked slice

See_also: $(LREF pack), $(LREF evertPack)
+/
Slice!(kind, [packs.sum], Iterator) unpack(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
{
    static if (packs.length == 1)
        return slice;
    else
        return typeof(return)(slice._lengths, slice._strides, slice._iterator);
}

/++
Reverses the order of dimension packs.
This function is used in a functional pipeline with other selectors.

Params:
    slice = packed slice
Returns:
    packed slice

See_also: $(LREF pack), $(LREF unpack)
+/
Slice!(SliceKind.universal, reverse(packs), Iterator)
//auto
evertPack(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    if (packs.length > 1)
{
    static if (kind != SliceKind.universal)
    {
        return slice.universal.evertPack;
    }
    else
    {

        mixin _DefineRet;
        with (slice)
        {
            alias C = Snowball!(aliasSeqOf!packs);
            alias D = Reverse!(Snowball!(aliasSeqOf!(reverse(packs))));
            foreach (i, _; Iota!(packs.length))
            {
                foreach (j; Iota!(0, C[i + 1] - C[i]))
                {
                    ret._lengths[j + D[i + 1]] = _lengths[j + C[i]];
                    ret._strides[j + D[i + 1]] = _strides[j + C[i]];
                }
            }
            ret._iterator = _iterator;
        }
        return ret;
    }
}

///
Slice!(kind, packs, Iterator) 
evertPack(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    if (packs.length == 1)
{
    return slice;
}

///
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.dynamic : transposed;
    auto slice = iota(3, 4, 5, 6, 7, 8, 9, 10, 11).universal;
    assert(slice
        .pack!2
        .evertPack
        .unpack
             == slice.transposed!(
                slice.shape.length-2,
                slice.shape.length-1));
}

///
pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.dynamic : transposed;
    auto a = iota(3, 4, 5, 6, 7, 8, 9, 10, 11).universal;
    auto b = a
        .pack!2
        .pack!3
        .evertPack;
    auto c = b[8, 9];
    auto d = c[5, 6, 7];
    auto e = d[1, 2, 3, 4];
    auto g = a[1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert(e == g);
    assert(a == b.evertPack);
    assert(c == a.transposed!(7, 8, 4, 5, 6)[8, 9]);
    static assert(is(typeof(b) == Slice!(SliceKind.universal, [2, 3, 4], IotaIterator!size_t)));
    static assert(is(typeof(c) == Slice!(SliceKind.universal, [3, 4], IotaIterator!size_t)));
    static assert(is(typeof(d) == Slice!(SliceKind.universal, [4], IotaIterator!size_t)));
    static assert(is(typeof(e) == size_t));
}

unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation;
    static assert(is(typeof(slice!int(20)
        .evertPack)
         == Slice!(SliceKind.continuous, [1], int*)));
    static assert(is(typeof(slice!int(20)
        .sliced(20)
        .evertPack())
         == Slice!(SliceKind.continuous, [1], int*)));
    static assert(is(typeof(slice!int(6)
        .sliced(1,2,3)
        .sliced(3)
        .evertPack()
        )
         == Slice!(SliceKind.universal, [2, 1], int*)));
    static assert(is(typeof(
        slice!int(6)
        .universal
        .sliced(1,2,3)
        .evertPack)
         == Slice!(SliceKind.universal, [3], int*)));
}


///
pure nothrow unittest
{
    auto a = iota(3, 4, 5, 6, 7, 8, 9, 10, 11);
    auto b = a.pack!2.unpack;
    static assert(is(typeof(a) == typeof(b)));
    assert(a == b);
}

/++
Returns a slice, the elements of which are equal to the initial flattened index value.
For a multidimensional index, see $(LREF ndiota).

Params:
    N = dimension count
    lengths = list of dimension lengths
    start = value of the first element in a slice (optional for integer `I`)
    stride = value of the stride between elements (optional)
Returns:
    `N`-dimensional slice composed of indexes
See_also: $(LREF IotaSlice), $(LREF ndiota)
+/
Slice!(SliceKind.continuous, [N], IotaIterator!I)
iota(I = size_t, size_t N)(size_t[N] lengths...)
    if (isIntegral!I)
{
    import mir.ndslice.slice : sliced;
    return IotaIterator!I.init.sliced(lengths);
}

///ditto
Slice!(SliceKind.continuous, [N], IotaIterator!I)
iota(I = size_t, size_t N)(size_t[N] lengths, I start)
    if (isIntegral!I || isPointer!I)
{
    import mir.ndslice.slice : sliced;
    return IotaIterator!I(start).sliced(lengths);
}

///ditto
Slice!(SliceKind.continuous, [N], StrideIterator!(IotaIterator!I))
iota(I = size_t, size_t N)(size_t[N] lengths, I start, size_t stride)
    if (isIntegral!I || isPointer!I)
{
    import mir.ndslice.slice : sliced;
    return StrideIterator!(IotaIterator!I)(stride, IotaIterator!I(start)).sliced(lengths);
}

///
@safe pure nothrow @nogc unittest
{
    auto slice = iota(2, 3);
    static immutable array =
        [[0, 1, 2],
         [3, 4, 5]];

    assert(slice == array);
}

///
pure nothrow unittest
{
    int[6] data;
    auto slice = iota([2, 3], data.ptr);
    auto array =
        [[data.ptr + 0, data.ptr + 1, data.ptr + 2],
         [data.ptr + 3, data.ptr + 4, data.ptr + 5]];

    assert(slice == array);
}

///
@safe pure nothrow @nogc
unittest
{
    auto im = iota([10, 5], 100);
    assert(im[2, 1] == 111); // 100 + 2 * 5 + 1

    //slicing works correctly
    auto cm = im[1 .. $, 3 .. $];
    assert(cm[2, 1] == 119); // 119 = 100 + (1 + 2) * 5 + (3 + 1)
}

/// `iota` with step
@safe pure nothrow unittest
{
    auto sl = iota([2, 3], 10, 10);

    assert(sl == [[10, 20, 30],
                  [40, 50, 60]]);
}

/++
Returns a 1-dimensional slice over the main diagonal of an n-dimensional slice.
`diagonal` can be generalized with other selectors such as
$(LREF blocks) (diagonal blocks) and $(LREF windows) (multi-diagonal slice).

Params:
    N = dimension count
    slice = input slice
Returns:
    1-dimensional slice composed of diagonal elements
+/
Slice!(packs[0] == 1 ? kind : SliceKind.universal, 1 ~ packs[1 .. $], Iterator) 
    diagonal
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
{
    static if (packs[0] == 1)
    {
        return slice;
    }
    else
    {
        mixin _DefineRet;
        ret._lengths[0] = slice._lengths[0];
        foreach (i; Iota!(1, packs[0]))
            if (ret._lengths[0] > slice._lengths[i])
                ret._lengths[0] = slice._lengths[i];
        foreach (i; Iota!(1, ret.N))
            ret._lengths[i] = slice._lengths[i + packs[0] - 1];
        auto strides = slice.unpack.strides;
        ret._strides[0] = strides[0];
        foreach (i; Iota!(1, packs[0]))
            ret._strides[0] += strides[i];
        foreach (i; Iota!(1, ret.S))
            ret._strides[i] = strides[i + packs[0] - 1];
        ret._iterator = slice._iterator;
        return ret;
    }
}

/// Matrix, main diagonal
@safe @nogc pure nothrow unittest
{
    //  -------
    // | 0 1 2 |
    // | 3 4 5 |
    //  -------
    //->
    // | 0 4 |
    static immutable d = [0, 4];
    assert(iota(2, 3).diagonal == d);
}

/// Non-square matrix
@safe pure nothrow unittest
{
    //  -------
    // | 0 1 |
    // | 2 3 |
    // | 4 5 |
    //  -------
    //->
    // | 0 3 |

    assert(iota(3, 2).diagonal == iota([2], 0, 3));
}

/// Loop through diagonal
pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation;

    auto slice = slice!int(3, 3);
    int i;
    foreach (ref e; slice.diagonal)
        e = ++i;
    assert(slice == [
        [1, 0, 0],
        [0, 2, 0],
        [0, 0, 3]]);
}

/// Matrix, subdiagonal
@safe @nogc pure nothrow
unittest
{
    //  -------
    // | 0 1 2 |
    // | 3 4 5 |
    //  -------
    //->
    // | 1 5 |
    static immutable d = [1, 5];
    auto a = iota(2, 3).canonical;
    a.popFront!1;
    assert(a.diagonal == d);
}

/// Matrix, antidiagonal
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.dynamic : dropToHypercube, reversed;
    //  -------
    // | 0 1 2 |
    // | 3 4 5 |
    //  -------
    //->
    // | 1 3 |
    static immutable d = [1, 3];
    assert(iota(2, 3).universal.dropToHypercube.reversed!1.diagonal == d);
}

/// 3D, main diagonal
@safe @nogc pure nothrow unittest
{
    //  -----------
    // |  0   1  2 |
    // |  3   4  5 |
    //  - - - - - -
    // |  6   7  8 |
    // |  9  10 11 |
    //  -----------
    //->
    // | 0 10 |
    static immutable d = [0, 10];
    assert(iota(2, 2, 3).diagonal == d);
}

/// 3D, subdiagonal
@safe @nogc pure nothrow unittest
{
    //  -----------
    // |  0   1  2 |
    // |  3   4  5 |
    //  - - - - - -
    // |  6   7  8 |
    // |  9  10 11 |
    //  -----------
    //->
    // | 1 11 |
    static immutable d = [1, 11];
    auto a = iota(2, 2, 3).canonical;
    a.popFront!2;
    assert(a.diagonal == d);
}

/// 3D, diagonal plain
@nogc @safe pure nothrow
unittest
{
    //  -----------
    // |  0   1  2 |
    // |  3   4  5 |
    // |  6   7  8 |
    //  - - - - - -
    // |  9  10 11 |
    // | 12  13 14 |
    // | 15  16 17 |
    //  - - - - - -
    // | 18  20 21 |
    // | 22  23 24 |
    // | 24  25 26 |
    //  -----------
    //->
    //  -----------
    // |  0   4  8 |
    // |  9  13 17 |
    // | 18  23 26 |
    //  -----------

    static immutable d =
        [[ 0,  4,  8],
         [ 9, 13, 17],
         [18, 22, 26]];

    auto slice = iota(3, 3, 3)
        .pack!2
        .evertPack
        .diagonal
        .evertPack;

    assert(slice == d);
}

/++
Returns an n-dimensional slice of n-dimensional non-overlapping blocks.
`blocks` can be generalized with other selectors.
For example, `blocks` in combination with $(LREF diagonal) can be used to get a slice of diagonal blocks.
For overlapped blocks, combine $(LREF windows) with $(SUBREF iteration, strided).

Params:
    N = dimension count
    slice = slice to be split into blocks
    lengths = dimensions of block, residual blocks are ignored
Returns:
    packed `N`-dimensional slice composed of `N`-dimensional slices
+/
Slice!(kind == SliceKind.continuous ? SliceKind.canonical : kind, packs[0] ~ packs, Iterator) 
    blocks
    (SliceKind kind, size_t[] packs, Iterator, size_t N)
    (Slice!(kind, packs, Iterator) slice, size_t[N] lengths...)
        if (packs[0] == N)
in
{
    foreach (i, length; lengths)
        assert(length > 0, "length of dimension = " ~ i.stringof ~ " must be positive"
            ~ tailErrorMessage!());
}
body
{
    mixin _DefineRet;
    foreach (dimension; Iota!(packs[0]))
    {
        ret._lengths[dimension] = slice._lengths[dimension] / lengths[dimension];
        ret._lengths[dimension + packs[0]] = lengths[dimension];
    }
    foreach (dimension; Iota!(packs[0], slice.N))
    {
        ret._lengths[dimension + packs[0]] = slice._lengths[dimension];
    }
    auto strides = slice.unpack.strides;
    foreach (dimension; Iota!(packs[0]))
    {
        ret._strides[dimension] = strides[dimension];
        if (ret._lengths[dimension]) //do not remove `if (...)`
            ret._strides[dimension] *= lengths[dimension];
    }
    foreach (dimension; Iota!(packs[0], ret.S))
    {
        ret._strides[dimension] = strides[dimension - packs[0]];
    }
    ret._iterator = slice._iterator;
    return ret;
}

///
pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation;
    auto slice = slice!int(5, 8);
    auto blocks = slice.blocks(2, 3);
    int i;
    foreach (blocksRaw; blocks)
        foreach (block; blocksRaw)
            block[] = ++i;

    assert(blocks ==
        [[[[1, 1, 1], [1, 1, 1]],
          [[2, 2, 2], [2, 2, 2]]],
         [[[3, 3, 3], [3, 3, 3]],
          [[4, 4, 4], [4, 4, 4]]]]);

    assert(    slice ==
        [[1, 1, 1,  2, 2, 2,  0, 0],
         [1, 1, 1,  2, 2, 2,  0, 0],

         [3, 3, 3,  4, 4, 4,  0, 0],
         [3, 3, 3,  4, 4, 4,  0, 0],

         [0, 0, 0,  0, 0, 0,  0, 0]]);
}

/// Diagonal blocks
pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation;
    auto slice = slice!int(5, 8);
    auto blocks = slice.blocks(2, 3);
    auto diagonalBlocks = blocks.diagonal.unpack;

    diagonalBlocks[0][] = 1;
    diagonalBlocks[1][] = 2;

    assert(diagonalBlocks ==
        [[[1, 1, 1], [1, 1, 1]],
         [[2, 2, 2], [2, 2, 2]]]);

    assert(blocks ==
        [[[[1, 1, 1], [1, 1, 1]],
          [[0, 0, 0], [0, 0, 0]]],
         [[[0, 0, 0], [0, 0, 0]],
          [[2, 2, 2], [2, 2, 2]]]]);

    assert(slice ==
        [[1, 1, 1,  0, 0, 0,  0, 0],
         [1, 1, 1,  0, 0, 0,  0, 0],

         [0, 0, 0,  2, 2, 2,  0, 0],
         [0, 0, 0,  2, 2, 2,  0, 0],

         [0, 0, 0, 0, 0, 0, 0, 0]]);
}

/// Matrix divided into vertical blocks
//pure nothrow
unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto slice = slice!int(5, 13);
    auto blocks = slice
        .pack!1
        .evertPack
        .blocks(3)
        .unpack
        .pack!2;

    int i;
    foreach (block; blocks)
        block[] = ++i;

    assert(slice ==
        [[1, 1, 1,  2, 2, 2,  3, 3, 3,  4, 4, 4,  0],
         [1, 1, 1,  2, 2, 2,  3, 3, 3,  4, 4, 4,  0],
         [1, 1, 1,  2, 2, 2,  3, 3, 3,  4, 4, 4,  0],
         [1, 1, 1,  2, 2, 2,  3, 3, 3,  4, 4, 4,  0],
         [1, 1, 1,  2, 2, 2,  3, 3, 3,  4, 4, 4,  0]]);
}

/++
Returns an n-dimensional slice of n-dimensional overlapping windows.
`windows` can be generalized with other selectors.
For example, `windows` in combination with $(LREF diagonal) can be used to get a multi-diagonal slice.

Params:
    N = dimension count
    slice = slice to be iterated
    lengths = dimensions of windows
Returns:
    packed `N`-dimensional slice composed of `N`-dimensional slices
+/
Slice!(kind == SliceKind.continuous ? SliceKind.canonical : kind, packs[0] ~ packs, Iterator) 
    windows
    (SliceKind kind, size_t[] packs, Iterator, size_t N)
    (Slice!(kind, packs, Iterator) slice, size_t[N] lengths...)
        if (packs[0] == N)
in
{
    foreach (i, length; lengths)
        assert(length > 0, "length of dimension = " ~ i.stringof ~ " must be positive"
            ~ tailErrorMessage!());
}
body
{
    mixin _DefineRet;
    foreach (dimension; Iota!(0, packs[0]))
    {
        ret._lengths[dimension] = slice._lengths[dimension] >= lengths[dimension] ?
                                  slice._lengths[dimension] - lengths[dimension] + 1: 0;
        ret._lengths[dimension + packs[0]] = lengths[dimension];
    }
    foreach (dimension; Iota!(packs[0], slice.N))
    {
        ret._lengths[dimension + packs[0]] = slice._lengths[dimension];
    }
    auto strides = slice.unpack.strides;
    foreach (dimension; Iota!(packs[0]))
    {
        ret._strides[dimension] = strides[dimension];
    }
    foreach (dimension; Iota!(packs[0], ret.S))
    {
        ret._strides[dimension] = strides[dimension - packs[0]];
    }
    ret._iterator = slice._iterator;
    return ret;
}

///
pure nothrow
unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto slice = slice!int(5, 8);
    auto windows = slice.windows(2, 3);

    int i;
    foreach (windowsRaw; windows)
        foreach (window; windowsRaw)
            ++window[];

    assert(slice ==
        [[1,  2,  3, 3, 3, 3,  2,  1],

         [2,  4,  6, 6, 6, 6,  4,  2],
         [2,  4,  6, 6, 6, 6,  4,  2],
         [2,  4,  6, 6, 6, 6,  4,  2],

         [1,  2,  3, 3, 3, 3,  2,  1]]);
}

///
pure nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto slice = slice!int(5, 8);
    auto windows = slice.windows(2, 3);
    windows[1, 2][] = 1;
    windows[1, 2][0, 1] += 1;
    windows.unpack[1, 2, 0, 1] += 1;

    assert(slice ==
        [[0, 0,  0, 0, 0,  0, 0, 0],

         [0, 0,  1, 3, 1,  0, 0, 0],
         [0, 0,  1, 1, 1,  0, 0, 0],

         [0, 0,  0, 0, 0,  0, 0, 0],
         [0, 0,  0, 0, 0,  0, 0, 0]]);
}

/// Multi-diagonal matrix
pure nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto slice = slice!int(8, 8);
    auto windows = slice.windows(3, 3);

    auto multidiagonal = windows
        .diagonal
        .unpack;
    foreach (window; multidiagonal)
        window[] += 1;

    assert(slice ==
        [[ 1, 1, 1,  0, 0, 0, 0, 0],
         [ 1, 2, 2, 1,  0, 0, 0, 0],
         [ 1, 2, 3, 2, 1,  0, 0, 0],
         [0,  1, 2, 3, 2, 1,  0, 0],
         [0, 0,  1, 2, 3, 2, 1,  0],
         [0, 0, 0,  1, 2, 3, 2, 1],
         [0, 0, 0, 0,  1, 2, 2, 1],
         [0, 0, 0, 0, 0,  1, 1, 1]]);
}

/// Sliding window over matrix columns
pure nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto slice = slice!int(5, 8);
    auto windows = slice
        .pack!1
        .evertPack
        .windows(3)
        .unpack
        .pack!2;


    foreach (window; windows)
        window[] += 1;

    assert(slice ==
        [[1,  2,  3, 3, 3, 3,  2,  1],
         [1,  2,  3, 3, 3, 3,  2,  1],
         [1,  2,  3, 3, 3, 3,  2,  1],
         [1,  2,  3, 3, 3, 3,  2,  1],
         [1,  2,  3, 3, 3, 3,  2,  1]]);
}

/// Overlapping blocks using windows
pure nothrow unittest
{
    //  ----------------
    // |  0  1  2  3  4 |
    // |  5  6  7  8  9 |
    // | 10 11 12 13 14 |
    // | 15 16 17 18 19 |
    // | 20 21 22 23 24 |
    //  ----------------
    //->
    //  ---------------------
    // |  0  1  2 |  2  3  4 |
    // |  5  6  7 |  7  8  9 |
    // | 10 11 12 | 12 13 14 |
    // | - - - - - - - - - - |
    // | 10 11 13 | 12 13 14 |
    // | 15 16 17 | 17 18 19 |
    // | 20 21 22 | 22 23 24 |
    //  ---------------------

    import mir.ndslice.slice;
    import mir.ndslice.dynamic : strided;

    auto overlappingBlocks = iota(5, 5)
        .windows(3, 3)
        .universal
        .strided!(0, 1)(2, 2);

    assert(overlappingBlocks ==
            [[[[ 0,  1,  2], [ 5,  6,  7], [10, 11, 12]],
              [[ 2,  3,  4], [ 7,  8,  9], [12, 13, 14]]],
             [[[10, 11, 12], [15, 16, 17], [20, 21, 22]],
              [[12, 13, 14], [17, 18, 19], [22, 23, 24]]]]);
}

/++
Error codes for $(LREF reshape).
+/
enum ReshapeError
{
    /// No error
    none,
    /// Slice should be not empty
    empty,
    /// Total element count should be the same
    total,
    /// Structure is incompatible with new shape
    incompatible,
}

/++
Returns a new slice for the same data with different dimensions.

Params:
    slice = slice to be reshaped
    lengths = list of new dimensions. One of the lengths can be set to `-1`.
        In this case, the corresponding dimension is inferable.
    err = $(LREF ReshapeError) code
Returns:
    reshaped slice
+/
Slice!(kind, M ~ packs[1 .. $], Iterator) reshape
        (SliceKind kind, size_t[] packs, Iterator, size_t M)
        (Slice!(kind, packs, Iterator) slice, ptrdiff_t[M] lengths, ref int err)
{
    static if (kind == SliceKind.canonical)
    {
        auto r = slice.universal.reshape(err);
        assert(err || r._strides[$-1] == 1);
        r._strides[$-1] = 1;
        return r.assumeCanonical;
    }
    else
    {
        mixin _DefineRet;
        foreach (i; Iota!M)
            ret._lengths[i] = lengths[i];
        /// Code size optimization
        goto B;
    R:
            return ret;
    B:
        immutable size_t eco = slice.elementsCount;
        if (eco == 0)
        {
            err = ReshapeError.empty;
            goto R;
        }
        size_t ecn = ret.elementsCount;
        foreach (i; Iota!M)
            if (ret._lengths[i] == -1)
            {
                ecn = -ecn;
                ret._lengths[i] = eco / ecn;
                ecn *= ret._lengths[i];
                break;
            }
        if (eco != ecn)
        {
            err = ReshapeError.total;
            goto R;
        }
        static if (kind == SliceKind.universal)
        {
            for (size_t oi, ni, oj, nj; oi < packs[0] && ni < M; oi = oj, ni = nj)
            {
                size_t op = slice._lengths[oj++];
                size_t np = ret  ._lengths[nj++];

                for (;;)
                {
                    if (op < np)
                        op *= slice._lengths[oj++];
                    if (op > np)
                        np *= ret  ._lengths[nj++];
                    if (op == np)
                        break;
                }
                while (oj < packs[0] && slice._lengths[oj] == 1) oj++;
                while (nj < M        && ret  ._lengths[nj] == 1) nj++;

                for (size_t l = oi, r = oi + 1; r < oj; r++)
                    if (slice._lengths[r] != 1)
                    {
                        if (slice._strides[l] != slice._lengths[r] * slice._strides[r])
                        {
                            err = ReshapeError.incompatible;
                            goto R;
                        }
                        l = r;
                    }
                assert((oi == packs[0]) == (ni == M));

                ret._strides[nj - 1] = slice._strides[oj - 1];
                foreach_reverse (i; ni .. nj - 1)
                    ret._strides[i] = ret._lengths[i + 1] * ret._strides[i + 1];
            }
        }
        foreach (i; Iota!(M, ret.N))
            ret._lengths[i] = slice._lengths[i + packs[0] - M];
        static if (M < ret.S)
        foreach (i; Iota!(M, ret.S))
            ret._strides[i] = slice._strides[i + packs[0] - M];
        ret._iterator = slice._iterator;
        err = 0;
        goto R;
    }
}

///
nothrow @safe pure
unittest
{
    import mir.ndslice.dynamic : allReversed;
    int err;
    auto slice = iota(3, 4)
        .universal
        .allReversed
        .reshape([-1, 3], err);
    assert(err == 0);
    assert(slice ==
        [[11, 10, 9],
         [ 8,  7, 6],
         [ 5,  4, 3],
         [ 2,  1, 0]]);
}

/// Reshaping with memory allocation
//pure 
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.dynamic : reversed;

    auto reshape2(S, size_t M)(S sl, ptrdiff_t[M] lengths)
    {
        int err;
        // Tries to reshape without allocation
        auto ret = sl.reshape(lengths, err);
        if (!err)
            return ret;
        if (err == ReshapeError.incompatible)
            // allocates, flattens, reshapes with `sliced`, converts to universal kind
            return sl.slice.flattened.sliced(cast(size_t[M])lengths).universal;
        throw new Exception("total elements count is different or equals to zero");
    }

    auto sl =
        .iota!int(3, 4)
        .slice
        .universal
        .reversed!0;

    assert(reshape2(sl, [4, 3]) ==
        [[ 8, 9, 10],
         [11, 4,  5],
         [ 6, 7,  0],
         [ 1, 2,  3]]);
}

nothrow @safe pure unittest
{
    import mir.ndslice.dynamic : allReversed;
    auto slice = iota(1, 1, 3, 2, 1, 2, 1).universal.allReversed;
    int err;
    assert(slice.reshape([1, -1, 1, 1, 3, 1], err) ==
        [[[[[[11], [10], [9]]]],
          [[[[ 8], [ 7], [6]]]],
          [[[[ 5], [ 4], [3]]]],
          [[[[ 2], [ 1], [0]]]]]]);
    assert(err == 0);
}

// Issue 15919
nothrow @nogc @safe pure
unittest
{
    int err;
    assert(iota(3, 4, 5, 6, 7).pack!2.reshape([4, 3, 5], err)[0, 0, 0].shape == cast(size_t[2])[6, 7]);
    assert(err == 0);
}

nothrow @nogc @safe pure unittest
{
    import mir.ndslice.slice;

    int err;
    auto e = iota(1);
    // resize to the wrong dimension
    auto s = e.reshape([2], err);
    assert(err == ReshapeError.total);
    e.popFront;
    // test with an empty slice
    e.reshape([1], err);
    assert(err == ReshapeError.empty);
}

unittest
{
    auto pElements = iota(3, 4, 5, 6, 7)
        .pack!2
        .flattened;
    assert(pElements[0][0] == iota(7));
    assert(pElements[$-1][$-1] == iota([7], 2513));
}

/++
Returns a random access range of all elements of a slice.
The order of elements is preserved.
`flattened` can be generalized with other selectors.

Params:
    N = dimension count
    slice = slice to be iterated
Returns:
    random access range composed of elements of the `slice`
+/
Slice!(SliceKind.continuous, [1], FlattenedIterator!(kind, packs, Iterator))
    flattened
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
    if (kind == SliceKind.canonical || kind == SliceKind.universal)
{
    mixin _DefineRet;
    ret._lengths[0] = slice.elementsCount;
    foreach(i; Iota!(ret._iterator._indexes.length))
        ret._iterator._indexes[i] = 0;
    ret._iterator._slice = slice;
    return ret;
}

/// ditto
Slice!(SliceKind.continuous, 1 ~ packs[1 .. $], Iterator) 
    flattened
    (size_t[] packs, Iterator)
    (Slice!(SliceKind.continuous, packs, Iterator) slice)
{
    static if (packs[0] == 1)
    {
        return slice;
    }
    else
    {
        mixin _DefineRet;
        ret._lengths[0] = slice._lengths[0 .. packs[0]].lengthsProduct;
        foreach(i; Iota!(1, ret.N))
            ret._lengths[i] = slice._lengths[i - 1 + packs[0]];
        ret._iterator = slice._iterator;
        return ret;
    }
}

/// Regular slice
@safe @nogc pure nothrow unittest
{
    assert(iota(4, 5).flattened == iota(20));
    assert(iota(4, 5).canonical.flattened == iota(20));
    assert(iota(4, 5).universal.flattened == iota(20));
}

/// Packed slice
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.dynamic;
    assert(iota(3, 4, 5, 6, 7).pack!2.flattened()[1] == iota([6, 7], 6 * 7));
}

/// Properties
pure nothrow unittest
{
    auto elems = iota(3, 4).universal.flattened;

    elems.popFrontExactly(2);
    assert(elems.front == 2);
    /// `_index` is availble only for canonical and universal ndslices.
    assert(elems._iterator._indexes == [0, 2]);

    elems.popBackExactly(2);
    assert(elems.back == 9);
    assert(elems.length == 8);
}

/// Index property
pure nothrow unittest
{
    import mir.ndslice.slice;
    auto slice = new long[20].sliced(5, 4);

    for (auto elems = slice.universal.flattened; !elems.empty; elems.popFront)
    {
        ptrdiff_t[2] index = elems._iterator._indexes;
        elems.front = index[0] * 10 + index[1] * 3;
    }
    assert(slice ==
        [[ 0,  3,  6,  9],
         [10, 13, 16, 19],
         [20, 23, 26, 29],
         [30, 33, 36, 39],
         [40, 43, 46, 49]]);
}

pure nothrow unittest
{
    auto elems = iota(3, 4).universal.flattened;
    assert(elems.front == 0);
    assert(elems.save[1] == 1);
}

/++
Random access and slicing
+/
nothrow unittest
{
    import mir.ndslice.allocation: slice;

    auto elems = iota(4, 5).slice.flattened;

    elems = elems[11 .. $ - 2];

    assert(elems.length == 7);
    assert(elems.front == 11);
    assert(elems.back == 17);

    foreach (i; 0 .. 7)
        assert(elems[i] == i + 11);

    // assign an element
    elems[2 .. 6] = -1;
    assert(elems[2 .. 6] == repeat(-1, 4));

    // assign an array
    static ar = [-1, -2, -3, -4];
    elems[2 .. 6] = ar;
    assert(elems[2 .. 6] == ar);

    // assign a slice
    ar[] *= 2;
    auto sl = ar.sliced(ar.length);
    elems[2 .. 6] = sl;
    assert(elems[2 .. 6] == sl);
}

@safe @nogc pure nothrow unittest
{
    import mir.ndslice.dynamic : allReversed;

    auto slice = iota(3, 4, 5);

    foreach (ref e; slice.universal.flattened.retro)
    {
        //...
    }

    foreach_reverse (ref e; slice.universal.flattened)
    {
        //...
    }

    foreach (ref e; slice.universal.allReversed.flattened)
    {
        //...
    }
}

@safe @nogc pure nothrow unittest
{
    import std.range.primitives : isRandomAccessRange, hasSlicing;
    auto elems = iota(4, 5).flattened;
    static assert(isRandomAccessRange!(typeof(elems)));
    static assert(hasSlicing!(typeof(elems)));
}

// Checks strides
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.dynamic;
    import std.range.primitives : isRandomAccessRange;
    auto elems = iota(4, 5).universal.everted.flattened;
    static assert(isRandomAccessRange!(typeof(elems)));

    elems = elems[11 .. $ - 2];
    auto elems2 = elems;
    foreach (i; 0 .. 7)
    {
        assert(elems[i] == elems2.front);
        elems2.popFront;
    }
}

@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.dynamic;
    import std.range.primitives : isRandomAccessRange, hasLength;

    auto range = (3 * 4 * 5 * 6 * 7).iota;
    auto slice0 = range.sliced(3, 4, 5, 6, 7).universal;
    auto slice1 = slice0.transposed!(2, 1).pack!2;
    auto elems0 = slice0.flattened;
    auto elems1 = slice1.flattened;

    foreach (S; AliasSeq!(typeof(elems0), typeof(elems1)))
    {
        static assert(isRandomAccessRange!S);
        static assert(hasLength!S);
    }

    assert(elems0.length == slice0.elementsCount);
    assert(elems1.length == 5 * 4 * 3);

    auto elems2 = elems1;
    foreach (q; slice1)
        foreach (w; q)
            foreach (e; w)
            {
                assert(!elems2.empty);
                assert(e == elems2.front);
                elems2.popFront;
            }
    assert(elems2.empty);

    elems0.popFront();
    elems0.popFrontExactly(slice0.elementsCount - 14);
    assert(elems0.length == 13);
    assert(elems0 == range[slice0.elementsCount - 13 .. slice0.elementsCount]);

    foreach (elem; elems0) {}
}

// Issue 15549
unittest
{
    import std.range.primitives;
    import mir.ndslice.allocation;
    alias A = typeof(iota(2, 5).sliced(1, 1, 1, 1));
    static assert(isRandomAccessRange!A);
    static assert(hasLength!A);
    static assert(hasSlicing!A);
    alias B = typeof(slice!double(2, 5).sliced(1, 1, 1, 1));
    static assert(isRandomAccessRange!B);
    static assert(hasLength!B);
    static assert(hasSlicing!B);
}

// Issue 16010
unittest
{
    auto s = iota(3, 4).flattened;
    foreach (_; 0 .. s.length)
        s = s[1 .. $];
}

/++
Returns a slice, the elements of which are equal to the initial multidimensional index value.
This is multidimensional analog of $(REF iota, std, range).
For a flattened (continuous) index, see $(LREF iota).

Params:
    N = dimension count
    lengths = list of dimension lengths
Returns:
    `N`-dimensional slice composed of indexes
See_also: $(LREF ndIotaField), $(LREF iota)
+/
Slice!(SliceKind.continuous, [N], FieldIterator!(ndIotaField!N))
    ndiota
    (size_t N)
    (size_t[N] lengths...)
    if (N)
{
    return FieldIterator!(ndIotaField!N)(0, ndIotaField!N(lengths[1 .. $])).sliced(lengths);
}

///
@safe pure nothrow @nogc unittest
{
    auto slice = ndiota(2, 3);
    static immutable array =
        [[[0, 0], [0, 1], [0, 2]],
         [[1, 0], [1, 1], [1, 2]]];

    assert(slice == array);
}

///
@safe pure nothrow unittest
{
    auto im = ndiota(7, 9);

    assert(im[2, 1] == [2, 1]);

    //slicing works correctly
    auto cm = im[1 .. $, 4 .. $];
    assert(cm[2, 1] == [3, 5]);
}

unittest
{
    auto r = ndiota(1);
    auto d = r.front;
    r.popFront;
    import std.range.primitives;
    static assert(isRandomAccessRange!(typeof(r)));
}

/++
Returns a slice with identical elements.
`RepeatSlice` stores only single value.
Params:
    lengths = list of dimension lengths
Returns:
    `n`-dimensional slice composed of identical values, where `n` is dimension count.
See_also: $(REF repeat, std,range)
+/
Slice!(SliceKind.continuous, [M], FieldIterator!(RepeatField!T))
    repeat(T, size_t M)(T value, size_t[M] lengths...)
    if (M && !is(T : Slice!(kind, packs, Iterator), SliceKind kind, size_t[] packs, Iterator))
{
    mixin _DefineRet;
    foreach (i; Iota!M)
        ret._lengths[i] = lengths[i];
    ret._iterator = FieldIterator!(RepeatField!T)(0, RepeatField!T(cast(RepeatField!T.UT) value));
    return ret;
}

/// ditto
Slice!(kind == SliceKind.continuous ? SliceKind.canonical : kind, M ~ packs, Iterator)
    repeat
    (SliceKind kind, size_t[] packs, Iterator, size_t M)
    (Slice!(kind, packs, Iterator) slice, size_t[M] lengths...)
    if (M)
{
    mixin _DefineRet;
    foreach (i; Iota!M)
        ret._lengths[i] = lengths[i];
    foreach (i; Iota!(slice.N))
        ret._lengths[M + i] = slice._lengths[i];
    foreach (i; Iota!M)
        ret._strides[i] = 0;
    auto strides = slice.unpack.strides;
    foreach (i; Iota!(M, ret.S))
        ret._strides[i] = strides[i - M];
    ret._iterator = slice._iterator;
    return ret;
}

///
@safe pure nothrow
unittest
{
    auto sl = iota(3).repeat(4);
    assert(sl == [[0, 1, 2],
                  [0, 1, 2],
                  [0, 1, 2],
                  [0, 1, 2]]);
}

///
@safe pure nothrow unittest
{
    import mir.ndslice.dynamic : transposed;

    auto sl = iota(3)
        .repeat(4)
        .unpack
        .universal
        .transposed;

    assert(sl == [[0, 0, 0, 0],
                  [1, 1, 1, 1],
                  [2, 2, 2, 2]]);
}

///
pure nothrow unittest
{
    import mir.ndslice.allocation;

    auto sl = iota([3], 6).slice;
    auto slC = sl.repeat(2, 3);
    sl[1] = 4;
    assert(slC == [[[6, 4, 8],
                    [6, 4, 8],
                    [6, 4, 8]],
                   [[6, 4, 8],
                    [6, 4, 8],
                    [6, 4, 8]]]);
}

///
@safe pure nothrow unittest
{
    auto sl = repeat(4.0, 2, 3);
    assert(sl == [[4.0, 4.0, 4.0],
                  [4.0, 4.0, 4.0]]);

    static assert(is(DeepElementType!(typeof(sl)) == double));

    sl[1, 1] = 3;
    assert(sl == [[3.0, 3.0, 3.0],
                  [3.0, 3.0, 3.0]]);
}

/++
+/
auto stride
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice, ptrdiff_t factor)
    if (packs.sum == 1)
in
{
    assert (factor > 0, "factor must be positive.");
}
body
{
    static if (kind == SliceKind.continuous)
        return slice.universal.stride(factor);
    else
    {
        import mir.ndslice.dynamic: strided;
        return slice.strided!0(factor);
    }
}

/++
+/
auto retro
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
    if (packs.length == 1)
{
    static if (kind == SliceKind.continuous || kind == SliceKind.canonical)
    {
        import mir.ndslice.dynamic: allReversed;
        static if (kind == SliceKind.continuous)
        {
            ptrdiff_t shift = 1;
            foreach(i; Iota!(packs[0]))
                shift *= slice._lengths[i];
            --shift;
        }
        else
        {
            ptrdiff_t shift = 0;
            foreach(i; Iota!(packs[0]))
                shift += slice.backIndex!i;
        }
        static if (is(Iterator : RetroIterator!It, It))
        {
            alias Ret = Slice!(kind, packs, It);
            mixin _DefineRet_;
            ret._iterator = slice._iterator._iterator;
        }
        else
        {
            alias Ret = Slice!(kind, packs, RetroIterator!Iterator);
            mixin _DefineRet_;
            ret._iterator = RetroIterator!Iterator(slice._iterator);
        }
        ret._iterator -= shift;
        foreach (i; Iota!(ret.N))
            ret._lengths[i] = slice._lengths[i];
        foreach (i; Iota!(ret.S))
            ret._strdies[i] = slice._strdies[i];
        return ret;
    }
    else
    {
        import mir.ndslice.dynamic: allReversed;
        return slice.allReversed;
    }
}

/++
+/
auto bitwise
    (SliceKind kind, size_t[] packs, Iterator, I = typeof(Iterator.init[size_t.init]))
    (Slice!(kind, packs, Iterator) slice)
    if (isIntegral!I && (kind == SliceKind.continuous || kind == SliceKind.canonical))
{
    static if (is(Iterator : FieldIterator!Field, Field))
    {
        enum simplified = true;
        alias It = FieldIterator!(BitwiseField!Field);
    }
    else
    {
        enum simplified = false;
        alias It = FieldIterator!(BitwiseField!Iterator);
    }
    alias Ret = Slice!(kind, packs, It);
    mixin _DefineRet_;
    foreach(i; Iota!(ret.N))
        ret._lengths[i] = slice._lengths[i];
    ret._lengths[$ - 1] *= I.sizeof * 8;
    foreach(i; Iota!(ret.S))
        ret._strides[i] = slice._strides[i];
    static if (simplified)
        ret._iterator = It(slice._iterator._index * I.sizeof * 8, BitwiseField!Field(slice._iterator._field));
    else
        ret._iterator = It(0, BitwiseField!Iterator(slice._iterator));
    return ret;
}

///
unittest
{
    size_t[10] data;
    auto bits = data[].ptr.sliced(10).bitwise;
    assert(bits.length == data.length * size_t.sizeof * 8);
    bits[111] = true;
    assert(bits[111]);
    
    bits.popFront;
    assert(bits[110]);
    bits[] = true;
    bits[110] = false;
    bits = bits[10 .. $];
    assert(bits[100] == false);
}

unittest
{
    size_t[10] data;
    auto slice = FieldIterator!(size_t[])(0, data[]).sliced(10);
    slice.popFrontExactly(2);
    auto bits_normal = data[].ptr.sliced(10).bitwise;
    auto bits = slice.bitwise;
    assert(bits.length == (data.length - 2) * size_t.sizeof * 8);
    bits[111] = true;
    assert(bits[111]);
    assert(bits_normal[111 + size_t.sizeof * 2 * 8]);
    
    bits.popFront;
    assert(bits[110]);
    bits[] = true;
    bits[110] = false;
    bits = bits[10 .. $];
    assert(bits[100] == false);
}

version(none):

/++
Implements the homonym function (also known as `transform`) present
in many languages of functional flavor. The call `map!(fun)(tensor)`
returns a tensor of which elements are obtained by applying `fun`
for all elements in `tensor`. The original tensors are
not changed. Evaluation is done lazily.

Note:
    $(SUBREF iteration, transposed) and
    $(SUBREF topology, pack) can be used to specify dimensions.
Params:
    fun = One or more functions.
    tensor = An input tensor.
Returns:
    a tensor with each fun applied to all the elements. If there is more than one
    fun, the element type will be `Tuple` containing one element for each fun.
See_Also:
    $(REF map, std,algorithm,iteration)
    $(HTTP en.wikipedia.org/wiki/Map_(higher-order_function), Map (higher-order function))
+/
template map(fun...)
    if (fun.length)
{
    ///
    @fmb auto map(size_t N, Iterator)
        (Slice!(N, Iterator) tensor)
    {
        // this static if-else block
        // may be unified with std.algorithms.iteration.map
        // after ndslice be removed from the Mir library.
            import mir.functional : nary;

            alias _fun = nary!fun;
            alias _funs = AliasSeq!(_fun);

            // Do the validation separately for single parameters due to DMD issue #15777.
            static assert(!is(typeof(_fun(RE.init)) == void),
                "Mapping function(s) must not return void: " ~ _funs.stringof);

        // Specialization for packed tensors (tensors composed of tensors).
        static if (is(Iterator : Slice!(NI, IteratorI), size_t NI, IteratorI))
        {
            alias Ptr = Pack!(NI - 1, IteratorI);
            alias M = Map!(Ptr, _fun);
            alias R = Slice!(N, M);
            return R(tensor._lengths[0 .. N], tensor._strides[0 .. N],
                M(Ptr(tensor._lengths[N .. $], tensor._strides[N .. $], tensor._iterator)));
        }
        else
        {
            alias M = Map!(SlicePtr!Iterator, _fun);
            alias R = Slice!(N, M);
            return R(tensor._lengths, tensor._strides, M(tensor._iterator));
        }
    }
}

///
pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    auto s = iota(2, 3).map!(a => a * 3);
    assert(s == [[ 0,  3,  6],
                 [ 9, 12, 15]]);
}

pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    assert(iota(2, 3).slice.map!"a * 2" == [[0, 2, 4], [6, 8, 10]]);
}

/// Packed tensors.
pure nothrow unittest
{
    import mir.ndslice.topology : iota, windows;

    //  iota        windows     map  sums ( reduce!"a + b" )
    //                --------------
    //  -------      |  ---    ---  |      ------
    // | 0 1 2 |  => || 0 1 || 1 2 ||  => | 8 12 |
    // | 3 4 5 |     || 3 4 || 4 5 ||      ------
    //  -------      |  ---    ---  |
    //                --------------
    auto s = iota(2, 3)
        .windows(2, 2)
        .map!((a) {
            size_t s;
            foreach (r; a)
                foreach (e; r)
                    s += e;
            return s;
            });

    assert(s == [[8, 12]]);
}

pure nothrow unittest
{
    import mir.ndslice.topology : iota, windows;

    auto s = iota(2, 3)
        .slice
        .windows(2, 2)
        .map!((a) {
            size_t s;
            foreach (r; a)
                foreach (e; r)
                    s += e;
            return s;
            });

    assert(s == [[8, 12]]);
}

/// Zipped tensors
pure nothrow unittest
{
    import mir.ndslice.slice : assumeSameStructure;
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    // tensors must have the same strides
    assert(sl1.structure == sl2.structure);

    auto zip = assumeSameStructure!("a", "b")(sl1, sl2);

    auto lazySum = zip.map!(z => z.a + z.b);

    assert(lazySum == [[ 1,  3,  5],
                       [ 7,  9, 11]]);
}

/++
Multiple functions can be passed to `map`.
In that case, the element type of `map` is a tuple containing
one element for each function.
+/
pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    auto s = iota(2, 3).map!("a + a", "a * a");

    auto sums     = [[0, 2, 4], [6,  8, 10]];
    auto products = [[0, 1, 4], [9, 16, 25]];

    foreach (i; 0..s.length!0)
    foreach (j; 0..s.length!1)
    {
        auto values = s[i, j];
        assert(values[0] == sums[i][j]);
        assert(values[1] == products[i][j]);
    }
}

/++
You may alias `map` with some function(s) to a symbol and use it separately:
+/
pure nothrow unittest
{
    import std.conv : to;
    import mir.ndslice.topology : iota;

    alias stringize = map!(to!string);
    assert(stringize(iota(2, 3)) == [["0", "1", "2"], ["3", "4", "5"]]);
}
