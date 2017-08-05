/++
Selectors create new views and iteration patterns over the same data, without copying.

$(BOOKTABLE $(H2 Kind Selectors),
$(TR $(TH Function Name) $(TH Description))

$(T2 universal, Converts a slice to universal $(SUBREF slice, SliceKind).)
$(T2 canonical, Converts a slice to canonical $(SUBREF slice, SliceKind).)
$(T2 assumeCanonical, Converts a slice to canonical $(SUBREF slice, SliceKind) (unsafe).)
$(T2 assumeContiguous, Converts a slice to contiguous $(SUBREF slice, SliceKind) (unsafe).)

)

$(BOOKTABLE $(H2 Sequence Selectors),
$(TR $(TH Function Name) $(TH Description))

$(T2 repeat, Slice with identical values)
$(T2 iota, Contiguous Slice with initial flattened (contiguous) index.)
$(T2 ndiota, Contiguous Slice with initial multidimensional index.)
$(T2 linspace, Evenly spaced numbers over a specified interval.)
$(T2 magic, Magic square.)
)

$(BOOKTABLE $(H2 Products),
$(TR $(TH Function Name) $(TH Description))

$(T2 cartesian, Cartesian product.)
$(T2 kronecker, Kronecker product.)

)

$(BOOKTABLE $(H2 Representation Selectors),
$(TR $(TH Function Name) $(TH Description))

$(T2 as, Convenience function that creates a lazy view,
where each element of the original slice is converted to a type `T`.)
$(T2 bitpack, Bitpack slice over an unsigned integral slice.)
$(T2 bitwise, Bitwise slice over an unsigned integral slice.)
$(T2 diff, Differences between vector elements.)
$(T2 flattened, Contiguous 1-dimensional slice of all elements of a slice.)
$(T2 map, Multidimensional functional map.)
$(T2 pairwise, Pairwise map for vectors.)
$(T2 retro, Reverses order of iteration for all dimensions.)
$(T2 slide, Sliding map for vectors.)
$(T2 stairs, Two functions to pack, unpack, and iterate triangular and symmetric matrix storage.)
$(T2 stride, Strides 1-dimensional slice.)
$(T2 unzip, Selects a slice from a zipped slice.)
$(T2 zip, Zips slices into a slice of refTuples.)
)


$(BOOKTABLE $(H2 Shape Selectors),
$(TR $(TH Function Name) $(TH Description))

$(T2 blocks, n-dimensional slice composed of n-dimensional non-overlapping blocks. If the slice has two dimensions, it is a block matrix.)
$(T2 diagonal, 1-dimensional slice composed of diagonal elements)
$(T2 reshape, New slice with changed dimensions for the same data)
$(T2 windows, n-dimensional slice of n-dimensional overlapping windows. If the slice has two dimensions, it is a sliding window.)

)

$(BOOKTABLE $(H2 Subspace Selectors),
$(TR $(TH Function Name) $(TH Description))

$(T2 pack     , Returns slice of slices.)
$(T2 ipack    , Returns slice of slices.)
$(T2 unpack   , Merges all dimension packs.)
$(T2 evertPack, Reverses dimension packs.)
$(T2 byDim    , Returns a slice that can be iterated by dimension. Transposes dimensions on top and then packs them.)

)

Subspace selectors serve to generalize and combine other selectors easily.
For a slice of `Slice!(kind, [N], Iterator)` type `slice.pack!K` creates a slice of
slices of `Slice!(kind, [N - K, K], Iterator)` type by packing
the last `K` dimensions of the top dimension pack,
and the type of element of $(LREF flattened) is `Slice!(Contiguous, [K], IteratorX)`.
Another way to use $(LREF pack) is transposition of dimension packs using
$(LREF evertPack). Examples of use of subspace selectors are available for selectors,
$(SUBREF slice, Slice.shape), and $(SUBREF slice, Slice.elementsCount).


License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Sponsors: Part of this work has been sponsored by $(LINK2 http://symmetryinvestments.com, Symmetry Investments) and Kaleidic Associates.


Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
+/
module mir.ndslice.topology;

import std.traits;
import std.meta;

import mir.internal.utility;
import mir.ndslice.field;
import mir.ndslice.internal;
import mir.ndslice.iterator;
import mir.ndslice.ndfield;
import mir.ndslice.slice;
import mir.primitives;

@fastmath:

/++
Converts a slice to universal kind.

Params:
    slice = a slice
Returns:
    universal slice
See_also:
    $(LREF canonical),
    $(LREF assumeCanonical),
    $(LREF assumeContiguous).
+/
auto universal(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
{
    static if (kind == Universal)
    {
        return slice;
    }
    else
    static if (is(Iterator : RetroIterator!It, It))
    {
        return slice.retro.universal.retro;
    }
    else
    {
        alias Ret = Slice!(Universal, packs, Iterator);
        mixin _DefineRet_;
        foreach (i; Iota!(slice.N))
            ret._lengths[i] = slice._lengths[i];
        static if (kind == Canonical)
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

///
@safe pure nothrow
unittest
{
    auto slice = iota(2, 3).universal;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3, 1]);
}

@safe pure nothrow
unittest
{
    auto slice = iota(2, 3).canonical.universal;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3, 1]);
}


/++
Converts a slice to canonical kind.

Params:
    slice = contiguous or canonical slice
Returns:
    canonical slice
See_also:
    $(LREF universal),
    $(LREF assumeCanonical),
    $(LREF assumeContiguous).
+/
Slice!(packs == [1] ? Contiguous : Canonical, packs, Iterator)
    canonical
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
    if (kind == Contiguous || kind == Canonical)
{
    static if (kind == Canonical || packs == [1])
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

///
@safe pure nothrow
unittest
{
    auto slice = iota(2, 3).canonical;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3]);
}

/++
Converts a slice to canonical kind (unsafe).

Params:
    slice = a slice
Returns:
    canonical slice
See_also:
    $(LREF universal),
    $(LREF canonical),
    $(LREF assumeContiguous).
+/
Slice!(Canonical, packs, Iterator)
    assumeCanonical
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
{
    static if (kind == Contiguous)
        return slice.canonical;
    else
    static if (kind == Canonical)
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

///
@safe pure nothrow
unittest
{
    auto slice = iota(2, 3).universal.assumeCanonical;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3]);
}


/++
Converts a slice to contiguous kind (unsafe).

Params:
    slice = a slice
Returns:
    canonical slice
See_also:
    $(LREF universal),
    $(LREF canonical),
    $(LREF assumeCanonical).
+/
Slice!(Contiguous, packs, Iterator)
    assumeContiguous
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
{
    static if (kind == Contiguous)
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

///
@safe pure nothrow
unittest
{
    auto slice = iota(2, 3).universal.assumeContiguous;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == []);
}

/++
Creates a packed slice, i.e. slice of slices.
Packs the last `p` dimensions of the first pack.
The function does not carry out any calculations, it simply returns the same
binary data presented differently.

Params:
    p = size of dimension pack
    slice = a slice to pack
Returns:
    `slice.pack!p` returns `Slice!(kind, [packs[0] - p, p] ~ packs[1 .. $], Iterator)`
See_also: $(LREF ipack)
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
    static assert(is(typeof(b) == Slice!(Contiguous, [2, 2], IotaIterator!size_t)));
}

/++
Creates a packed slice, i.e. slice of slices.
Packs the first `p` dimensions of the first pack.
The function does not carry out any calculations, it simply returns the same
binary data presented differently.

Params:
    p = size of dimension pack
    slice = a slice to pack
Returns:
    `slice.ipack!p` returns `Slice!(kind, [p, packs[0] - p] ~ packs[1 .. $], Iterator)`
See_also: $(LREF pack)
+/
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
    auto b = a.ipack!2;

    static immutable res1 = [3, 4];
    static immutable res2 = [5, 6];
    assert(b.shape == res1);
    assert(b[0, 0].shape == res2);
    assert(a == b);
    static assert(is(typeof(b) == typeof(a.ipack!2)));
    static assert(is(typeof(b) == Slice!(Contiguous, [2, 2], IotaIterator!size_t)));
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
    static assert(is(typeof(b) == Slice!(Contiguous, [4, 3, 2], IotaIterator!size_t)));
    static assert(is(typeof(c) == Slice!(Contiguous, [3, 2], IotaIterator!size_t)));
    static assert(is(typeof(d) == Slice!(Contiguous, [2], IotaIterator!size_t)));
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
Slice!(Universal, reverse(packs), Iterator)
//auto
evertPack(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    if (packs.length > 1)
{
    static if (kind != Universal)
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
@safe pure nothrow unittest
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
    static assert(is(typeof(b) == Slice!(Universal, [2, 3, 4], IotaIterator!size_t)));
    static assert(is(typeof(c) == Slice!(Universal, [3, 4], IotaIterator!size_t)));
    static assert(is(typeof(d) == Slice!(Universal, [4], IotaIterator!size_t)));
    static assert(is(typeof(e) == size_t));
}

@safe pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation;
    static assert(is(typeof(slice!int(20)
        .evertPack)
         == Slice!(Contiguous, [1], int*)));
    static assert(is(typeof(slice!int(20)
        .sliced(20)
        .evertPack())
         == Slice!(Contiguous, [1], int*)));
    static assert(is(typeof(slice!int(6)
        .sliced(1,2,3)
        .sliced(3)
        .evertPack()
        )
         == Slice!(Universal, [2, 1], int*)));
    static assert(is(typeof(
        slice!int(6)
        .universal
        .sliced(1,2,3)
        .evertPack)
         == Slice!(Universal, [3], int*)));
}


///
@safe pure nothrow @nogc
unittest
{
    auto a = iota(3, 4, 5, 6, 7, 8, 9, 10, 11);
    auto b = a.pack!2.unpack;
    static assert(is(typeof(a) == typeof(b)));
    assert(a == b);
}

/++
Returns a slice, the elements of which are equal to the initial flattened index value.

Params:
    N = dimension count
    lengths = list of dimension lengths
    start = value of the first element in a slice (optional for integer `I`)
    stride = value of the stride between elements (optional)
Returns:
    n-dimensional slice composed of indexes
See_also: $(LREF ndiota)
+/
Slice!(Contiguous, [N], IotaIterator!I)
iota
    (I = size_t, size_t N)(size_t[N] lengths...)
    if (isIntegral!I)
{
    import mir.ndslice.slice : sliced;
    return IotaIterator!I(I.init).sliced(lengths);
}

///ditto
Slice!(Contiguous, [N], IotaIterator!I)
iota
    (I, size_t N)(size_t[N] lengths, I start)
    if (isIntegral!I || isPointer!I)
{
    import mir.ndslice.slice : sliced;
    return IotaIterator!I(start).sliced(lengths);
}

///ditto
Slice!(Contiguous, [N], StrideIterator!(IotaIterator!I))
iota
    (I, size_t N)(size_t[N] lengths, I start, size_t stride)
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
pure nothrow
unittest
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
    slice = input slice
Returns:
    1-dimensional slice composed of diagonal elements
+/
Slice!(packs[0] == 1 ? kind : Universal, 1 ~ packs[1 .. $], Iterator) 
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
@safe pure nothrow unittest
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
For overlapped blocks, combine $(LREF windows) with $(SUBREF dynamic, strided).

Params:
    N = dimension count
    slice = slice to be split into blocks
    lengths = dimensions of block, residual blocks are ignored
Returns:
    packed `N`-dimensional slice composed of `N`-dimensional slices

See_also: $(SUBREF chunks, ._chunks)
+/
Slice!(kind == Contiguous ? Canonical : kind, packs[0] ~ packs, Iterator) 
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
@safe pure nothrow unittest
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
@safe pure unittest
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
Slice!(kind == Contiguous ? Canonical : kind, packs[0] ~ packs, Iterator) 
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
@safe pure nothrow
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
@safe pure nothrow unittest
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
@safe pure nothrow unittest
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
@safe pure nothrow unittest
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
@safe pure nothrow unittest
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

unittest
{
    auto w = iota(9, 9).windows(3, 3);
    assert(w.front == w[0]);
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
    static if (kind == Canonical)
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
        static if (kind == Universal)
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
@safe nothrow pure
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
@safe pure unittest
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

nothrow @nogc @safe pure 
unittest
{
    auto pElements = iota(3, 4, 5, 6, 7)
        .pack!2
        .flattened;
    assert(pElements[0][0] == iota(7));
    assert(pElements[$-1][$-1] == iota([7], 2513));
}

/++
A contiguous 1-dimensional slice of all elements of a slice.
`flattened` iterates existing data.
The order of elements is preserved.

`flattened` can be generalized with other selectors.

Params:
    slice = slice to be iterated
Returns:
    contiguous 1-dimensional slice of elements of the `slice`
+/
Slice!(Contiguous, [1], FlattenedIterator!(kind, packs, Iterator))
    flattened
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
    if (packs[0] != 1 && kind != Contiguous)
{
    mixin _DefineRet;
    ret._lengths[0] = slice.elementsCount;
    foreach(i; Iota!(ret._iterator._indexes.length))
        ret._iterator._indexes[i] = 0;
    ret._iterator._slice = slice;
    return ret;
}

/// ditto
Slice!(Contiguous, 1 ~ packs[1 .. $], Iterator) 
    flattened
    (size_t[] packs, Iterator)
    (Slice!(Contiguous, packs, Iterator) slice)
{
    static if (packs == [1])
    {
        return slice;
    }
    else
    {
        mixin _DefineRet;
        ret._lengths[0] = slice.elementsCount;
        foreach(i; Iota!(1, ret.N))
            ret._lengths[i] = slice._lengths[i - 1 + packs[0]];
        ret._iterator = slice._iterator;
        return ret;
    }
}

/// ditto
Slice!(Contiguous, [1], StrideIterator!Iterator) 
    flattened
    (Iterator)
    (Slice!(Universal, [1], Iterator) slice)
{
    return slice.hideStride;
}

/// ditto
Slice!(Contiguous, [1], StrideIterator!(SliceIterator!(packs[1 .. $].sum == 1 && kind == Canonical ? Contiguous : kind, packs[1 .. $], Iterator)))
    flattened
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
    if (packs[0] == 1 && kind != Contiguous && packs.length > 1)
{
    mixin _DefineRet;
    ret._lengths[0] = slice._lengths[0];
    ret._iterator._stride = slice._strides[0];
    foreach(i; Iota!(ret._iterator._iterator.Elem.N))
        ret._iterator._iterator._lengths[i] = slice._lengths[i + 1];
    foreach(i; Iota!(ret._iterator._iterator.Elem.S))
        ret._iterator._iterator._strides[i] = slice._strides[i + 1];
    ret._iterator._iterator._iterator = slice._iterator;
    return ret;
}

unittest
{
    import mir.ndslice.allocation: slice;
    auto sl1 = iota(2, 3).slice.universal.pack!1.flattened;
    auto sl2 = iota(2, 3).slice.canonical.pack!1.flattened;
    auto sl3 = iota(2, 3).slice.pack!1.flattened;
}

/// Regular slice
@safe @nogc pure nothrow unittest
{
    assert(iota(4, 5).flattened == iota(20));
    assert(iota(4, 5).canonical.flattened == iota(20));
    assert(iota(4, 5).universal.flattened == iota(20));
}

@safe @nogc pure nothrow unittest
{
    assert(iota(4).flattened == iota(4));
    assert(iota(4).canonical.flattened == iota(4));
    assert(iota(4).universal.flattened == iota(4));
}

/// Packed slice
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.dynamic;
    assert(iota(3, 4, 5, 6, 7).pack!2.flattened[1] == iota([6, 7], 6 * 7));
}

/// Properties
@safe pure nothrow unittest
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
@safe pure nothrow unittest
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

@safe pure nothrow unittest
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
For a flattened (contiguous) index, see $(LREF iota).

Params:
    N = dimension count
    lengths = list of dimension lengths
Returns:
    `N`-dimensional slice composed of indexes
See_also: $(LREF iota)
+/
Slice!(Contiguous, [N], FieldIterator!(ndIotaField!N))
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
Evenly spaced numbers over a specified interval.

Params:
    T = floating point or complex numbers type
    lengths = list of dimension lengths. Each length must be greater then 1.
    intervals = list of [start, end] pairs.
Returns:
    `n`-dimensional grid of evenly spaced numbers over specified intervals.
See_also: $(LREF)
+/
auto linspace(T, size_t N)(size_t[N] lengths, T[2][N] intervals...)
    if (N && (isFloatingPoint!T || isComplex!T))
{
    Repeat!(N, LinspaceField!T) fields;
    foreach(i; Iota!N)
    {
        assert(lengths[i] > 1, "linspace: all lengths must be greater then 1.");
        fields[i] = LinspaceField!T(lengths[i], intervals[i][0], intervals[i][1]);
    }
    static if (N == 1)
        return slicedField(fields);
    else
        return cartesian(fields);
}

/// 1D
@safe pure nothrow
unittest
{
    auto s = linspace!double([5], [1.0, 2.0]);
    assert(s == [1.0, 1.25, 1.5, 1.75, 2.0]);

    // remove endpoint
    s.popBack;
    assert(s == [1.0, 1.25, 1.5, 1.75]);
}

/// 2D
@safe pure nothrow
unittest
{
    import mir.functional: refTuple;

    auto s = linspace!double([5, 3], [1.0, 2.0], [0.0, 1.0]);

    assert(s == [
        [refTuple(1.00, 0.00), refTuple(1.00, 0.5), refTuple(1.00, 1.0)],
        [refTuple(1.25, 0.00), refTuple(1.25, 0.5), refTuple(1.25, 1.0)],
        [refTuple(1.50, 0.00), refTuple(1.50, 0.5), refTuple(1.50, 1.0)],
        [refTuple(1.75, 0.00), refTuple(1.75, 0.5), refTuple(1.75, 1.0)],
        [refTuple(2.00, 0.00), refTuple(2.00, 0.5), refTuple(2.00, 1.0)],
        ]);

    assert(s.map!"a * b" == [
        [0.0, 0.500, 1.00],
        [0.0, 0.625, 1.25],
        [0.0, 0.750, 1.50],
        [0.0, 0.875, 1.75],
        [0.0, 1.000, 2.00],
        ]);
}

/// Complex numbers
@safe pure nothrow
unittest
{
    auto s = linspace!cdouble([3], [1.0 + 0i, 2.0 + 4i]);
    assert(s == [1.0 + 0i, 1.5 + 2i, 2.0 + 4i]);
}

/++
Returns a slice with identical elements.
`RepeatSlice` stores only single value.
Params:
    lengths = list of dimension lengths
Returns:
    `n`-dimensional slice composed of identical values, where `n` is dimension count.
+/
Slice!(Contiguous, [M], FieldIterator!(RepeatField!T))
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
Slice!(kind == Contiguous ? Canonical : kind, M ~ packs, Iterator)
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
@safe pure nothrow unittest
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
Strides 1-dimensional slice.
Params:
    slice = 1-dimensional unpacked slice.
    factor = positive stride size.
Returns:
    Contiguous slice with strided iterator.
See_also: $(SUBREF dynamic, strided)
+/
auto stride
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice, ptrdiff_t factor)
    if (packs == [1])
in
{
    assert (factor > 0, "factor must be positive.");
}
body
{
    static if (kind == Contiguous)
        return slice.universal.stride(factor);
    else
    {
        import mir.ndslice.dynamic: strided;
        return slice.strided!0(factor).hideStride;
    }
}

///
@safe pure nothrow @nogc unittest
{
    auto slice = iota(6);
    static immutable str = [0, 2, 4];
    assert(slice.stride(2) == str);
    assert(slice.universal.stride(2) == str);
}

/++
Reverses order of iteration for all dimensions.
Params:
    slice = Unpacked slice.
Returns:
    Slice with reversed order of iteration for all dimensions.
See_also: $(SUBREF dynamic, reversed), $(SUBREF dynamic, allReversed).
+/
auto retro
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
    @trusted
    if (packs.length == 1)
{
    static if (kind == Contiguous || kind == Canonical)
    {
        static if (is(Iterator : RetroIterator!It, It))
        {
            alias Ret = Slice!(kind, packs, It);
            mixin _DefineRet_;
            ret._iterator = slice._iterator._iterator - slice.lastIndex;
        }
        else
        {
            alias Ret = Slice!(kind, packs, RetroIterator!Iterator);
            mixin _DefineRet_;
            ret._iterator = RetroIterator!Iterator(slice._iterator + slice.lastIndex);
        }
        foreach (i; Iota!(ret.N))
            ret._lengths[i] = slice._lengths[i];
        foreach (i; Iota!(ret.S))
            ret._strides[i] = slice._strides[i];
        return ret;
    }
    else
    {
        import mir.ndslice.dynamic: allReversed;
        return slice.allReversed;
    }
}

///
@safe pure nothrow @nogc unittest
{
    auto slice = iota(2, 3);
    static immutable reversed = [[5, 4, 3], [2, 1, 0]];
    assert(slice.retro == reversed);
    assert(slice.canonical.retro == reversed);
    assert(slice.universal.retro == reversed);

    static assert(is(typeof(slice.retro.retro) == typeof(slice)));
    static assert(is(typeof(slice.canonical.retro.retro) == typeof(slice.canonical)));
    static assert(is(typeof(slice.universal.retro) == typeof(slice.universal)));
}

/++
Bitwise slice over an integral slice.
Params:
    slice = a contiguous or canonical slice on top of integral iterator.
Returns: A bitwise slice.
+/
auto bitwise
    (SliceKind kind, size_t[] packs, Iterator, I = typeof(Iterator.init[size_t.init]))
    (Slice!(kind, packs, Iterator) slice)
    if (isIntegral!I && (kind == Contiguous || kind == Canonical))
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
@safe pure nothrow @nogc
unittest
{
    size_t[10] data;
    auto bits = data[].sliced.bitwise;
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

@safe pure nothrow @nogc
unittest
{
    size_t[10] data;
    auto slice = FieldIterator!(size_t[])(0, data[]).sliced(10);
    slice.popFrontExactly(2);
    auto bits_normal = data[].sliced.bitwise;
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

/++
Bitpack slice over an integral slice.

Bitpack is used to represent unsigned integer slice with fewer number of bits in integer binary representation.

Params:
    pack = counts of bits in the integer.
    slice = a contiguous or canonical slice on top of integral iterator.
Returns: A bitpack slice.
+/
auto bitpack
    (size_t pack, SliceKind kind, size_t[] packs, Iterator, I = typeof(Iterator.init[size_t.init]))
    (Slice!(kind, packs, Iterator) slice)
    if (isIntegral!I && (kind == Contiguous || kind == Canonical) && pack > 1)
{
    static if (is(Iterator : FieldIterator!Field, Field) && I.sizeof * 8 % pack == 0)
    {
        enum simplified = true;
        alias It = FieldIterator!(BitpackField!(Field, pack));
    }
    else
    {
        enum simplified = false;
        alias It = FieldIterator!(BitpackField!(Iterator, pack));
    }
    alias Ret = Slice!(kind, packs, It);
    mixin _DefineRet_;
    foreach(i; Iota!(ret.N))
        ret._lengths[i] = slice._lengths[i];
    ret._lengths[$ - 1] *= I.sizeof * 8;
    ret._lengths[$ - 1] /= pack;
    foreach(i; Iota!(ret.S))
        ret._strides[i] = slice._strides[i];
    static if (simplified)
        ret._iterator = It(slice._iterator._index * I.sizeof * 8 / pack, BitpackField!(Field, pack)(slice._iterator._field));
    else
        ret._iterator = It(0, BitpackField!(Iterator, pack)(slice._iterator));
    return ret;
}

///
@safe pure nothrow @nogc
unittest
{
    size_t[10] data;
    // creates a packed unsigned integer slice with max allowed value equal to `2^^6 - 1 == 63`.
    auto packs = data[].sliced.bitpack!6;
    assert(packs.length == data.length * size_t.sizeof * 8 / 6);
    packs[$ - 1] = 24;
    assert(packs[$ - 1] == 24);

    packs.popFront;
    assert(packs[$ - 1] == 24);
}

/++
Implements the homonym function (also known as `transform`) present
in many languages of functional flavor. The call `map!(fun)(slice)`
returns a slice of which elements are obtained by applying `fun`
for all elements in `slice`. The original slices are
not changed. Evaluation is done lazily.

Note:
    $(SUBREF dynamic, transposed) and
    $(SUBREF topology, pack) can be used to specify dimensions.
Params:
    fun = One or more functions.
See_Also:
    $(LREF pairwise), $(LREF slide), $(LREF zip), 
    $(HTTP en.wikipedia.org/wiki/Map_(higher-order_function), Map (higher-order function))
+/
template map(fun...)
    if (fun.length)
{
    import mir.functional: adjoin, naryFun, pipe;
    static if (fun.length == 1)
    {
        static if (__traits(isSame, naryFun!"a", fun[0]))
        {
            /++
            Params:
                slice = An input slice.
            Returns:
                a slice with each fun applied to all the elements. If there is more than one
                fun, the element type will be `Tuple` containing one element for each fun.
            +/
            @fastmath auto map(SliceKind kind, size_t[] packs, Iterator)
                (Slice!(kind, packs, Iterator) slice)
            {
                static if (packs.length == 1)
                {
                    return slice;
                }
                else
                {
                    alias It = SliceIterator!(TemplateArgsOf!(slice.DeepElemType));
                    auto sl = slice.universal;
                    auto outerLengths = cast(size_t[packs[0]]) sl._lengths[0 .. packs[0]];
                    auto outerStrides = cast(ptrdiff_t[packs[0]]) sl._strides[0 .. packs[0]];
                    auto lengths = cast(size_t[It._lengths.length]) sl._lengths[packs[0] .. packs[0] + It._lengths.length];
                    auto strides = cast(ptrdiff_t[It._strides.length]) sl._strides[packs[0] .. packs[0] + It._strides.length];
                    auto it = It(lengths, strides, sl._iterator);
                    return Slice!(Universal, packs[0 .. 1], It)(outerLengths, outerStrides, it);
                }
            }
        }
        else
        static if (__traits(isSame, naryFun!(fun[0]), fun[0]))
        {
            alias f = fun[0];
            @fastmath auto map(SliceKind kind, size_t[] packs, Iterator)
                (Slice!(kind, packs, Iterator) slice)
            {
                static if (packs.length == 1)
                {
                    import mir.ndslice.iterator: mapIterator;
                    auto iterator = slice._iterator.mapIterator!f;
                    return Slice!(kind, packs, typeof(iterator))(slice._lengths, slice._strides, iterator);
                }
                // Specialization for packed tensors (tensors composed of tensors).
                else
                {
                    alias It = SliceIterator!(TemplateArgsOf!(slice.DeepElemType));
                    return .map!f(.map!(naryFun!"a")(slice));
                }
            }
        }
        else alias map = .map!(naryFun!fun);
    }
    else alias map = .map!(adjoin!fun);
}

///
@safe pure nothrow
unittest
{
    import mir.ndslice.topology : iota;
    auto s = iota(2, 3).map!(a => a * 3);
    assert(s == [[ 0,  3,  6],
                 [ 9, 12, 15]]);
}

/// String lambdas
@safe pure nothrow
unittest
{
    import mir.ndslice.topology : iota;
    assert(iota(2, 3).map!"a * 2" == [[0, 2, 4], [6, 8, 10]]);
}

/// Packed tensors.
@safe pure nothrow
unittest
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

@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota, windows;

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

/// Zipped tensors
@safe pure nothrow
unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    auto z = zip(sl1, sl2);

    auto lazySum = z.map!"a + b";

    assert(zip(sl1, sl2).map!"a + b" ==
            [[ 1,  3,  5],
             [ 7,  9, 11]]);
}

/++
Multiple functions can be passed to `map`.
In that case, the element type of `map` is a refTuple containing
one element for each function.
+/
@safe pure nothrow
unittest
{
    import mir.ndslice.topology : iota;

    auto s = iota(2, 3).map!("a + a", "a * a");

    auto sums     = [[0, 2, 4], [6,  8, 10]];
    auto products = [[0, 1, 4], [9, 16, 25]];

    foreach (i; 0..s.length!0)
    foreach (j; 0..s.length!1)
    {
        auto values = s[i, j];
        assert(values.a == sums[i][j]);
        assert(values.b == products[i][j]);
    }
}

/++
You may alias `map` with some function(s) to a symbol and use it separately:
+/
pure nothrow unittest
{
    import mir.ndslice.topology : iota;

    alias halfs = map!"double(a) / 2";
    assert(halfs(iota(2, 3)) == [[0.0, 0.5, 1], [1.5, 2, 2.5]]);
}

/++
Type normalization
+/
unittest
{
    import mir.functional : pipe;
    import mir.ndslice.topology : iota;
    auto a = iota(2, 3).map!"a + 10".map!(pipe!("a * 2", "a + 1"));
    auto b = iota(2, 3).map!(pipe!("a + 10", "a * 2", "a + 1"));
    assert(a == b);
    static assert(is(typeof(a) == typeof(b)));
}

///
pure unittest
{
    import std.algorithm.iteration : sum, reduce;
    import mir.utility : max;
    import mir.ndslice.dynamic : transposed;
    /// Returns maximal column average.
    auto maxAvg(S)(S matrix) {
        return reduce!max(matrix.universal.transposed.pack!1.map!sum)
             / double(matrix.length);
    }
    // 1 2
    // 3 4
    auto matrix = iota([2, 2], 1);
    assert(maxAvg(matrix) == 3);
}

private auto hideStride
    (SliceKind kind, Iterator)
    (Slice!(kind, [1], Iterator) slice)
{
    static if (kind == Universal)
        return Slice!(Contiguous, [1], StrideIterator!Iterator)(
            slice._lengths,
            sizediff_t[0].init,
            StrideIterator!Iterator(slice._strides[0], slice._iterator));
    else
        return slice;
}

private auto unhideStride
    (SliceKind kind, size_t[] packs, Iterator)
    (Slice!(kind, packs, Iterator) slice)
{
    static if (is(Iterator : StrideIterator!It, It))
    {
        static if (kind == Universal)
        {
            alias Ret = SliceKind!(Universal, packs, It);
            mixin _DefineRet_;
            foreach(i; Iota!(ret.N))
                ret._lengths[i] = slice._lengths[i];
            foreach(i; Iota!(ret.S))
                ret._strides[i] = slice._strides[i] * slice._iterator._stride;
        }
        else
            return slice.universal.unhideStride;
    }
    else
        return slice;
}

/++
Convenience function that creates a lazy view,
where each element of the original slice is converted to the type `T`.
It uses $(LREF  map) and $(REF_ALTTEXT $(TT to), to, mir,conv)$(NBSP)
composition under the hood.
Params:
    slice = a slice to create a view on.
Returns:
    A lazy slice with elements converted to the type `T`.
+/
template as(T)
{
    ///
    @fastmath auto as(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    {
        static if (is(slice.DeepElemType == T))
            return slice;
        else
        static if (isPointer!Iterator && is(const(Unqual!(typeof(Iterator.init[0]))) == T))
            return slice.toConst;
        else
        {
            import mir.conv: to;
            return map!(to!T)(slice);
        }
    }
}

///
@safe pure nothrow unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : diagonal, as;

    auto matrix = slice!double([2, 2], 0);
    auto stringMatrixView = matrix.as!int;
    assert(stringMatrixView ==
            [[0, 0],
             [0, 0]]);

    matrix.diagonal[] = 1;
    assert(stringMatrixView ==
            [[1, 0],
             [0, 1]]);

    /// allocate new slice composed of strings
    Slice!(Contiguous, [2], int*) stringMatrix = stringMatrixView.slice;
}

/// Special behavior for pointers to a constant data.
@safe pure nothrow unittest
{
    import mir.ndslice.allocation : slice;

    Slice!(Contiguous, [2], double*)              matrix = slice!double([2, 2], 0);
    Slice!(Contiguous, [2], const(double)*) const_matrix = matrix.as!(const double);
}

/++
Takes a field `source` and a slice `indexes`, and creates a view of source as if its elements were reordered according to indexes.
`indexes` may include only a subset of the elements of `source` and may also repeat elements.

Params:
    source = a filed, source of data. `source` must be an array or a pointer, or have `opIndex` primitive. Full random access range API is not required.
    indexes = a slice, source of indexes.
Returns:
    n-dimensional slice with the same kind, shape and strides.

See_also: `indexed` is similar to $(LREF, map), but a field is used instead of a function.
+/
Slice!(kind, packs, IndexIterator!(Iterator, Field))
    indexed(Field, SliceKind kind, size_t[] packs, Iterator)
    (Field source, Slice!(kind, packs, Iterator) indexes)
{
    return typeof(return)(
            indexes._lengths,
            indexes._strides,
            IndexIterator!(Iterator, Field)(
                indexes._iterator,
                source));
}

///
@safe pure nothrow unittest
{
    auto source = [1, 2, 3, 4, 5];
    auto indexes = [4, 3, 1, 2, 0, 4].sliced;
    auto ind = source.indexed(indexes);
    assert(ind == [5, 4, 2, 3, 1, 5]);
    
    assert(ind.retro == source.indexed(indexes.retro));

    ind[3] += 10; // for index 2
    //                0  1   2  3  4
    assert(source == [1, 2, 13, 4, 5]);
}

/++
Groups slices into a slice of refTuples. The slices must have identical strides or be 1-dimensional.
Params:
    sameStrides = if `true` assumes that all slices has the same strides.
    slices = list of slices
Returns:
    n-dimensional slice of elements refTuple
See_also: $(SUBREF slice, Slice.strides).
+/
auto zip
    (bool sameStrides = false, Slices...)(Slices slices)
    if (Slices.length > 1 && allSatisfy!(isSlice, Slices))
{
    enum packs = packsOf!(Slices[0]);
    foreach(i, S; Slices[1 .. $])
    {
        static assert(packsOf!S == packs, "zip: all Slices must have the same shape packs");
        assert(slices[i + 1]._lengths == slices[0]._lengths, "zip: all slices must have the same lengths");
        static if (sameStrides)
            assert(slices[i + 1].unpack.strides == slices[0].unpack.strides, "zip: all slices must have the same strides when unpacked");
    }
    static if (!sameStrides && minElem(staticMap!(kindOf, Slices)) != Contiguous)
    {
        static assert(packs == [1], "zip: cannot zip canonical and universal multidimensional slices if `sameStrides` is false");
        mixin(`return .zip(` ~ _iotaArgs!(Slices.length, "slices[", "].hideStride, ") ~`);`);
    }
    else
    {
        enum kind = maxElem(staticMap!(kindOf, Slices));
        alias Iterator = ZipIterator!(staticMap!(_IteratorOf, Slices));
        alias Ret = Slice!(kind, packs, Iterator);
        mixin _DefineRet_;
        foreach (i; Iota!(Ret.N))
            ret._lengths[i] = slices[0]._lengths[i];
        foreach (i; Iota!(Ret.S))
            ret._strides[i] = slices[0]._strides[i];
        ret._iterator = mixin("Iterator(" ~ _iotaArgs!(Slices.length, "slices[", "]._iterator, ") ~ ")");
        return ret;
    }
}

///
@safe pure nothrow unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : flattened, iota;

    auto alpha = iota!int(4, 3);
    auto beta = slice!int(4, 3).universal;

    auto m = zip!true(alpha, beta);
    foreach (r; m)
        foreach (e; r)
            e.b = e.a;
    assert(alpha == beta);

    beta[] = 0;
    foreach (e; m.flattened)
        e.b = cast(int)e.a;
    assert(alpha == beta);
}

@safe pure nothrow unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : flattened, iota;

    auto alpha = iota!int(4).universal;
    auto beta = slice!int(4);

    auto m = zip(alpha, beta);
    foreach (e; m)
        e.b = e.a;
    assert(alpha == beta);
}

/++
Selects a slice from a zipped slice.
Params:
    name = name of a slice to unzip.
    slice = zipped slice
Returns:
    unzipped slice
+/
auto unzip
    (char name, SliceKind kind, size_t[] packs, Iterator : ZipIterator!Iterators, Iterators...)
    (Slice!(kind, packs, Iterator) slice)
{
    enum size_t i = name - 'a';
    static assert(i < Iterators.length, `unzip: constraint: size_t(name - 'a') < Iterators.length`);
    return Slice!(kind, packs, Iterators[i])(slice._lengths, slice._strides, slice._iterator._iterators[i]).unhideStride;
}

///
pure nothrow unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : iota;

    auto alpha = iota!int(4, 3);
    auto beta = iota!int([4, 3], 1).slice;

    auto m = zip(alpha, beta);

    static assert(is(typeof(unzip!'a'(m)) == typeof(alpha)));
    static assert(is(typeof(unzip!'b'(m)) == typeof(beta)));

    assert(m.unzip!'a' == alpha);
    assert(m.unzip!'b' == beta);
}

private enum TotalDim(NdFields...) = [staticMap!(DimensionCount, NdFields)].sum;

/++
Sliding map for vectors.

Suitable for simple convolution algorithms.

Params:
    params = windows length.
    fun = map functions with `params` arity.
See_also: $(LREF pairwise), $(LREF diff).
+/
template slide(size_t params, alias fun)
    if (params <= 'z' - 'a' + 1)
{
    import mir.functional: naryFun;
    static if (params == 1)
    {
        alias slide = .map!(naryFun!fun);
    }
    else
    static if (__traits(isSame, naryFun!fun, fun))
    {
        /++
        Params:
            slice = An 1-dimensional input slice.
        Returns:
            1d-slice composed of `fun(slice[i], ..., slice[i + params - 1])`.
        +/
        @fastmath auto slide(SliceKind kind, Iterator)
            (Slice!(kind, [1], Iterator) slice)
        {
            auto s = slice.flattened;
            s._lengths[0] -= params - 1;
            if (cast(sizediff_t)s._lengths[0] < 0)
                s._lengths[0] = 0;
            alias I = SlideIterator!(_IteratorOf!(typeof(s)), params, fun);
            return Slice!(Contiguous, [1], I)(
                s._lengths,
                s._strides,
                I(s._iterator));
        }
    }
    else alias slide = .slide!(params, naryFun!fun);
}

///
unittest
{
    auto data = 10.iota;
    auto sw = data.slide!(3, "a + 2 * b + c");
    
    import mir.utility: max;
    assert(sw.length == max(0, cast(ptrdiff_t)data.length - 3 + 1));
    assert(sw == sw.length.iota.map!"(a + 1) * 4");
    assert(sw == [4, 8, 12, 16, 20, 24, 28, 32]);
}

/++
Pairwise map for vectors.

Params:
    fun = function to accomulate
    lag = an integer indicating which lag to use
Returns: lazy ndslice composed of `fun(a_n, a_n+1)` values.

See_also: $(LREF slide).
+/
alias pairwise(alias fun, size_t lag = 1) = slide!(lag + 1, fun);

///
unittest
{
    assert([2, 4, 3, -1].sliced.pairwise!"a + b" == [6, 7, 2]);
}

/++
Differences between vector elements.

Params:
    lag = an integer indicating which lag to use
Returns: lazy differences.

See_also: $(LREF slide).
+/
alias diff(size_t lag = 1) = pairwise!(('a' + lag) ~ " - a", lag);

///
unittest
{
    assert([2, 4, 3, -1].sliced.diff == [2, -1, -4]);
}

/++
Cartesian product.

Constructs lazy cartesian product $(SUBREF slice, Slice) without memory allocation.

Params:
    fields = list of fields with lengths or ndFields with shapes
Returns: $(SUBREF ndfield, Cartesian)`!NdFields(fields).`$(SUBREF slice, slicedNdField)`;`
+/
auto cartesian(NdFields...)(NdFields fields)
    if (NdFields.length > 1 && allSatisfy!(templateOr!(hasShape, hasLength), NdFields))
{
    return Cartesian!NdFields(fields).slicedNdField;
}

/// 1D x 1D
unittest
{
    auto a = [10, 20, 30];
    auto b = [ 1,  2,  3];

    auto c = cartesian(a, b)
        .map!"a + b";

    assert(c == [
        [11, 12, 13],
        [21, 22, 23],
        [31, 32, 33]]);
}

/// 1D x 2D
unittest
{
    auto a = [10, 20, 30];
    auto b = iota([2, 3], 1);

    auto c = cartesian(a, b)
        .map!"a + b";

    assert(c.shape == [3, 2, 3]);

    assert(c == [
        [
            [11, 12, 13],
            [14, 15, 16],
        ],
        [
            [21, 22, 23],
            [24, 25, 26],
        ],
        [
            [31, 32, 33],
            [34, 35, 36],
        ]]);
}

/// 1D x 1D x 1D
unittest
{
    auto u = [100, 200];
    auto v = [10, 20, 30];
    auto w = [1, 2];

    auto c = cartesian(u, v, w)
        .map!"a + b + c";

    assert(c.shape == [2, 3, 2]);

    assert(c == [
        [
            [111, 112],
            [121, 122],
            [131, 132],
        ],
        [
            [211, 212],
            [221, 222],
            [231, 232],
        ]]);
}



/++
$(LINK2 https://en.wikipedia.org/wiki/Kronecker_product,  Kronecker product).

Constructs lazy kronecker product $(SUBREF slice, Slice) without memory allocation.
+/
template kronecker(alias fun = product)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))

    /++
    Params:
        fields = list of either fields with lengths or ndFields with shapes.
            All ndFields must have the same dimension count.
    Returns:
        $(SUBREF ndfield, Kronecker)`!(fun, NdFields)(fields).`$(SUBREF slice, slicedNdField)
    +/
    @fastmath auto kronecker(NdFields...)(NdFields fields)
        if (allSatisfy!(hasShape, NdFields) || allSatisfy!(hasLength, NdFields))
    {
        return Kronecker!(fun, NdFields)(fields).slicedNdField;
    }
    else
        alias kronecker = .kronecker!(naryFun!fun);
}

/// 2D
unittest
{
    import mir.ndslice.allocation: slice;

    // eye
    auto a = slice!double([4, 4], 0);
    a.diagonal[] = 1;

    auto b = [ 1, -1,
              -1,  1].sliced(2, 2);

    auto c = kronecker(a, b);

    assert(c == [
        [ 1, -1,  0,  0,  0,  0,  0,  0],
        [-1,  1,  0,  0,  0,  0,  0,  0],
        [ 0,  0,  1, -1,  0,  0,  0,  0],
        [ 0,  0, -1,  1,  0,  0,  0,  0],
        [ 0,  0,  0,  0,  1, -1,  0,  0],
        [ 0,  0,  0,  0, -1,  1,  0,  0],
        [ 0,  0,  0,  0,  0,  0,  1, -1],
        [ 0,  0,  0,  0,  0,  0, -1,  1]]);
}

/// 1D
unittest
{
    auto a = iota([3], 1);

    auto b = [ 1, -1];

    auto c = kronecker(a, b);

    assert(c == [1, -1, 2, -2, 3, -3]);
}

/// 2D with 3 arguments
unittest
{
    import mir.ndslice.allocation: slice;

    auto a = [ 1,  2,
               3,  4].sliced(2, 2);

    auto b = [ 1,  0,
               0,  1].sliced(2, 2);

    auto c = [ 1, -1,
              -1,  1].sliced(2, 2);

    auto d = kronecker(a, b, c);

    assert(d == [
        [ 1, -1,  0,  0,  2, -2,  0,  0],
        [-1,  1,  0,  0, -2,  2,  0,  0],
        [ 0,  0,  1, -1,  0,  0,  2, -2],
        [ 0,  0, -1,  1,  0,  0, -2,  2],
        [ 3, -3,  0,  0,  4, -4,  0,  0],
        [-3,  3,  0,  0, -4,  4,  0,  0],
        [ 0,  0,  3, -3,  0,  0,  4, -4],
        [ 0,  0, -3,  3,  0,  0, -4,  4]]);
}

/++
$(HTTPS en.wikipedia.org/wiki/Magic_square, Magic square).
Params:
    length = square matrix length.
Returns:
    Lazy magic matrix.
+/
auto magic(size_t length)
{
    assert(length > 0);
    static if (is(size_t == ulong))
        assert(length <= uint.max);
    else
        assert(length <= ushort.max);
    import mir.ndslice.field: MagicField;
    return MagicField!()(length).slicedField(length, length);
}

///
@safe pure nothrow
unittest
{
    auto isMagic(S)(S matrix)
    {
        import mir.math.sum;
        import mir.ndslice.algorithm: all;
        import mir.ndslice.allocation: slice;
        import mir.ndslice.dynamic: transposed, reversed;
        import mir.ndslice.topology: flattened, universal, diagonal;

        // check shape
        if (matrix.length == 0)
            return false;
        if (matrix.length!0 != matrix.length!1)
            return false;

        // checks that matrix is composed of consequent elements from interval 1:N^2.
        auto n2 = matrix.elementsCount;
        enum bc = size_t.sizeof * 8;
        auto flags = slice!size_t(n2 / bc + (n2 % bc != 0))
            .bitwise[0 .. n2];
        foreach(elem; matrix.flattened)
        {
            assert(elem > 0);
            assert(elem <= n2);
            flags[elem - 1] = true;
        }
        if (!flags.all)
            return false;

        // calculate magic number
        auto n = matrix.length;
        auto c = n * (n * n + 1) / 2;

        // each row sum should equal magic number
        foreach(row; matrix)
            if (row.sum != c)
                return false;
        // each columns sum should equal magic number
        foreach(col; matrix.universal.transposed)
            if (col.sum != c)
                return false;
        // each diagonal sum should equal magic number
        if (matrix.diagonal.sum != c)
            return false;
        if (matrix.universal.reversed!0.diagonal.sum != c)
            return false;

        return true;
    }

    assert(isMagic(magic(1)));
    assert(!isMagic(magic(2))); // 2x2 magic square does not exist
    foreach(n; 3 .. 24)
        assert(isMagic(magic(n)));
}

/++
Chops 1D input slice into n chunks with ascending or descending lengths.

`stairs` can be used to pack and unpack symmetric and triangular matrix storage.

Note: `stairs` is defined for 1D (packet) input and 2D (general) input.
    This part of documentation is for 1D input.

Params:
    type = $(UL
        $(LI `"-"` for stairs with lengths `n, n-1, ..., 1`.)
        $(LI `"+"` for stairs with lengths `1, 2, ..., n`;)
        )
    slice = input slice with length equal to `n * (n + 1) / 2`
    n = stairs count
Returns:
    1D contiguous slice composed of 1D contiguous slices.

See_also: $(LREF ._stairs.2)
+/
auto stairs(string type, Iterator)(Slice!(Contiguous, [1], Iterator) slice, size_t n)
    if (type == "+" || type == "-")
{
    assert(slice.length == (n + 1) * n / 2, "stairs: slice length must be equal to n * (n + 1) / 2, where n is stairs count.");
    static if (type == "+")
    {
        return StairsIterator!Iterator(1, slice._iterator)
            .sliced(n);
    }
    else
    {
        auto it = slice.retro._iterator;
        return StairsIterator!(typeof(it))(1, it)
            .sliced(n)
            .map!retro
            .retro;
    }
}

///
unittest
{
    import mir.ndslice.topology: iota, stairs;

    auto pck = 15.iota;
    auto inc = pck.stairs!"+"(5);
    auto dec = pck.stairs!"-"(5);

    assert(inc == [
        [0],
        [1, 2],
        [3, 4, 5],
        [6, 7, 8, 9],
        [10, 11, 12, 13, 14]]);

    assert(dec == [
        [0, 1, 2, 3, 4],
           [5, 6, 7, 8],
            [9, 10, 11],
               [12, 13],
                   [14]]);

    static assert(is(typeof(inc.front) == typeof(pck)));
    static assert(is(typeof(dec.front) == typeof(pck)));
}

/++
Slice composed of rows of lower or upper triangular matrix.

`stairs` can be used to pack and unpack symmetric and triangular matrix storage.

Note: `stairs` is defined for 1D (packet) input and 2D (general) input.
    This part of documentation is for 2D input.

Params:
    type = $(UL
        $(LI `"+"` for stairs with lengths `1, 2, ..., n`, lower matrix;)
        $(LI `"-"` for stairs with lengths `n, n-1, ..., 1`, upper matrix.)
        )
    slice = input slice with length equal to `n * (n + 1) / 2`
Returns:
    1D slice composed of 1D contiguous slices.

See_also: $(LREF _stairs) $(SUBREF dynamic, transposed), $(LREF universal)
+/
auto stairs(string type, SliceKind kind, Iterator)(Slice!(kind, [2], Iterator) slice)
    if (type == "+" || type == "-")
{
    assert(slice.length!0 == slice.length!1, "stairs: input slice must be a square matrix.");
    static if (type == "+")
    {
        return slice
            .pack!1
            .map!"a"
            .zip([slice.length].iota!size_t(1))
            .map!"a[0 .. b]";
    }
    else
    {
        return slice
            .pack!1
            .map!"a"
            .zip([slice.length].iota!size_t)
            .map!"a[b .. $]";
    }
}

///
unittest
{
    import mir.ndslice.topology: iota, as, stairs;

    auto gen = [3, 3].iota.as!double;
    auto inc = gen.stairs!"+";
    auto dec = gen.stairs!"-";

    assert(inc == [
        [0],
        [3, 4],
        [6, 7, 8]]);

    assert(dec == [
        [0, 1, 2],
           [4, 5],
              [8]]);

    static assert(is(typeof(inc.front) == typeof(gen.front)));
    static assert(is(typeof(dec.front) == typeof(gen.front)));

    /////////////////////////////////////////
    // Pack lower and upper matrix parts
    auto n = gen.length;
    auto m = n * (n + 1) / 2;
    // allocate memory
    import mir.ndslice.allocation: uninitSlice;
    auto lowerData = m.uninitSlice!double;
    auto upperData = m.uninitSlice!double;
    // construct packed stairs
    auto lower = lowerData.stairs!"+"(n);
    auto upper = upperData.stairs!"-"(n);
    // copy data
    import mir.ndslice.algorithm: each;
    each!"a[] = b"(lower, inc);
    each!"a[] = b"(upper, dec);

    assert(&lower[0][0] is &lowerData[0]);
    assert(&upper[0][0] is &upperData[0]);

    assert(lowerData == [0, 3, 4, 6, 7, 8]);
    assert(upperData == [0, 1, 2, 4, 5, 8]);
}

/// Transposed adjusted to ignore dim=0 and include universal
private template adjTransposed(Dimensions...)
    if (Dimensions.length)
{
    import mir.ndslice.slice : Slice, SliceKind;
    import mir.ndslice.internal : isSize_t, toSize_t;
    import std.meta : allSatisfy, staticMap;
   
    static if (!allSatisfy!(isSize_t, Dimensions))
        alias adjTransposed = .adjTransposed!(staticMap!(toSize_t, Dimensions));
    else
    ///
    @fastmath auto adjTransposed(SliceKind kind, size_t[] packs, Iterator)
                                           (Slice!(kind, packs, Iterator) slice)
    {
        import mir.ndslice.topology : ipack;
        import mir.ndslice.internal : DimensionsCountCTError, DimensionCTError;
        import mir.internal.utility : Iota;

        mixin DimensionsCountCTError;

        static if (Dimensions == Iota!(Dimensions.length))
        {
            return slice;
        }
        else static if (Dimensions[0] + 1 < packs[0] || packs.length > 1)
        {
            import mir.ndslice.topology : canonical;
            import mir.ndslice.dynamic : transposed;
            
            return slice.canonical.transposed!Dimensions;
        } 
        else
        {
            import mir.ndslice.topology : universal;
            import mir.ndslice.dynamic : transposed;

            return slice.universal.transposed!Dimensions;
        }
    }
}

///
private auto adjTransposed(SliceKind kind, size_t[] packs, Iterator)
                                        (Slice!(kind, packs, Iterator) slice)
{
    return slice.adjTransposed!0;
}

// 1-dimensional slice support
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota;
    import mir.ndslice.traits : isContiguousSlice;
    //  -------
    // | 0 1 2 |
    //  -------
    auto slice = iota(3);
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isContiguousSlice!(typeof(x)));
}

// 2-dimensional slice support
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota;
    import mir.ndslice.traits : isContiguousSlice, isUniversalSlice;
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto slice = iota(3, 4);
    //->
    // | 3 4 |
    //->
    // | 4 3 |
    size_t[2] shape34 = [3, 4];
    size_t[2] shape43 = [4, 3];
    
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isContiguousSlice!(typeof(x)));
    assert(x.shape == shape34);
    assert(x.front == iota(4));
    x.popFront;
    assert(x.front == iota([4], 4));
    
    //  ---------
    // | 0  4  8 |
    // | 1  5  9 |
    // | 2  6 10 |
    // | 3  7 11 |
    //  ---------
    auto y = slice.adjTransposed!1;
    assert(isUniversalSlice!(typeof(y)));
    assert(y.shape == shape43);
    assert(y.front == iota([3], 0, 4));
    y.popFront;
    assert(y.front == iota([3], 1, 4));
}

// 3-dimensional slice support, N-dimensional also supported
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, universal, flattened, reshape;
    import mir.ndslice.dynamic : strided, transposed;
    import mir.ndslice.traits : isContiguousSlice, isUniversalSlice, 
                                isCanonicalSlice;
    //  ----------------
    // |  0  1  2  3  4 |
    // |  5  6  7  8  9 |
    // | 10 11 12 13 14 |
    // | 15 16 17 18 19 |
    //  - - - - - - - -
    // | 20 21 22 23 24 |
    // | 25 26 27 28 29 |
    // | 30 31 32 33 34 |
    // | 35 36 37 38 39 |
    //  - - - - - - - -
    // | 40 41 42 43 44 |
    // | 45 46 47 48 49 |
    // | 50 51 52 53 54 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto slice = iota(3, 4, 5);
    //->
    // | 3 4 5 |
    //->
    // | 4 3 5 |
    //->
    // | 5 3 4 |
    //->
    // | 5 4 3 |
    //->
    // | 4 5 |
    //->
    // | 3 5 |
    //->
    // | 3 4 |
    //->
    // | 4 3 |
    size_t[3] shape345 = [3, 4, 5];
    size_t[3] shape435 = [4, 3, 5];
    size_t[3] shape534 = [5, 3, 4];
    size_t[3] shape543 = [5, 4, 3];
    size_t[2] shape45 = [4, 5];
    size_t[2] shape35 = [3, 5];
    size_t[2] shape34 = [3, 4];
    size_t[2] shape43 = [4, 3];

    //  ----------------
    // |  0  1  2  3  4 |
    // |  5  6  7  8  9 |
    // | 10 11 12 13 14 |
    // | 15 16 17 18 19 |
    //  - - - - - - - -
    // | 20 21 22 23 24 |
    // | 25 26 27 28 29 |
    // | 30 31 32 33 34 |
    // | 35 36 37 38 39 |
    //  - - - - - - - -
    // | 40 41 42 43 44 |
    // | 45 46 47 48 49 |
    // | 50 51 52 53 54 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isContiguousSlice!(typeof(x)));
    assert(x.shape == shape345);
    assert(x.front.shape == shape45);
    assert(x.front == iota([4, 5]));
    x.popFront;
    assert(x.front == iota([4, 5], (4 * 5)));
    
    //  ----------------
    // |  0  1  2  3  4 |
    // | 20 21 22 23 24 |
    // | 40 41 42 43 44 |
    //  - - - - - - - -
    // |  5  6  7  8  9 |
    // | 25 26 27 28 29 |
    // | 45 46 47 48 49 |
    //  - - - - - - - -
    // | 10 11 12 13 14 |
    // | 30 31 32 33 34 |
    // | 50 51 52 53 54 |
    //  - - - - - - - -
    // | 15 16 17 18 19 |
    // | 35 36 37 38 39 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto y = slice.adjTransposed!1;
    assert(isCanonicalSlice!(typeof(y)));
    assert(y.shape == shape435);
    assert(y.front.shape == shape35);
    int err;
    assert(y.front == slice.universal.strided!1(4).reshape([3, -1], err));
    y.popFront;
    assert(y.front.front == iota([5], 5));
    
    //  -------------
    // |  0  5 10 15 |
    // | 20 25 30 35 |
    // | 40 45 50 55 |
    //  - - - - - - -
    // |  1  6 11 16 |
    // | 21 26 31 36 |
    // | 41 46 51 56 |
    //  - - - - - - -
    // |  2  7 12 17 |
    // | 22 27 32 37 |
    // | 42 47 52 57 |
    //  - - - - - - -
    // |  3  8 13 18 |
    // | 23 28 33 38 |
    // | 43 48 53 58 |
    //  - - - - - - -
    // |  4  9 14 19 |
    // | 24 29 34 39 |
    // | 44 49 54 59 |
    //  -------------
    auto z = slice.adjTransposed!2;
    assert(isUniversalSlice!(typeof(z)));
    assert(z.shape == shape534);
    assert(z.front.shape == shape34);
    assert(z.front == iota([3, 4], 0, 5));
    z.popFront;
    assert(z.front.front == iota([4], 1, 5));

    //  ----------
    // |  0 20 40 |
    // |  5 25 45 |
    // | 10 30 50 |
    // | 15 35 55 |
    //  - - - - -
    // |  1 21 41 |
    // |  6 26 46 |
    // | 11 31 51 |
    // | 16 36 56 |
    //  - - - - -
    // |  2 22 42 |
    // |  7 27 47 |
    // | 12 32 52 |
    // | 17 37 57 |
    //  - - - - -
    // |  3 23 43 |
    // |  8 28 48 |
    // | 13 33 53 |
    // | 18 38 58 |
    //  - - - - -
    // |  4 24 44 |
    // |  9 29 49 |
    // | 14 34 54 |
    // | 19 39 59 |
    //  ----------
    auto a = slice.adjTransposed!(2, 1);
    assert(isUniversalSlice!(typeof(a)));
    assert(a.shape == shape543);
    assert(a.front.shape == shape43);
    assert(a.front == iota([3, 4], 0, 5).universal.transposed!1);
    a.popFront;
    assert(a.front.front == iota([3], 1, 20));
}

// Ensure works on canonical
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, canonical;
    import mir.ndslice.traits : isUniversalSlice, isCanonicalSlice;
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto slice = iota(3, 4).canonical;
    //->
    // | 3 4 |
    //->
    // | 4 3 |
    size_t[2] shape34 = [3, 4];
    size_t[2] shape43 = [4, 3];
    
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isCanonicalSlice!(typeof(x)));
    assert(x.shape == shape34);
    assert(x.front == iota(4));
    x.popFront;
    assert(x.front == iota([4], 4));
    
    //  ---------
    // | 0  4  8 |
    // | 1  5  9 |
    // | 2  6 10 |
    // | 3  7 11 |
    //  ---------
    auto y = slice.adjTransposed!1;
    assert(isUniversalSlice!(typeof(y)));
    assert(y.shape == shape43);
    assert(y.front == iota([3], 0, 4));
    y.popFront;
    assert(y.front == iota([3], 1, 4));
}

// Ensure works on universal
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, universal;
    import mir.ndslice.traits : isUniversalSlice;
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto slice = iota(3, 4).universal;
    //->
    // | 3 4 |
    //->
    // | 4 3 |
    size_t[2] shape34 = [3, 4];
    size_t[2] shape43 = [4, 3];
    
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isUniversalSlice!(typeof(x)));
    assert(x.shape == shape34);
    assert(x.front == iota(4));
    x.popFront;
    assert(x.front == iota([4], 4));
    
    //  ---------
    // | 0  4  8 |
    // | 1  5  9 |
    // | 2  6 10 |
    // | 3  7 11 |
    //  ---------
    auto y = slice.adjTransposed!1;
    assert(isUniversalSlice!(typeof(y)));
    assert(y.shape == shape43);
    assert(y.front == iota([3], 0, 4));
    y.popFront;
    assert(y.front == iota([3], 1, 4));
}

// Ensure works on canonical packed slice
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, universal, flattened, reshape;
    import mir.ndslice.dynamic : strided;
    import mir.ndslice.traits : isCanonicalSlice;
    //  ----------------
    // |  0  1  2  3  4 |
    // |  5  6  7  8  9 |
    // | 10 11 12 13 14 |
    // | 15 16 17 18 19 |
    //  - - - - - - - -
    // | 20 21 22 23 24 |
    // | 25 26 27 28 29 |
    // | 30 31 32 33 34 |
    // | 35 36 37 38 39 |
    //  - - - - - - - -
    // | 40 41 42 43 44 |
    // | 45 46 47 48 49 |
    // | 50 51 52 53 54 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto slice = iota(3, 4, 5).canonical.pack!1;
    //->
    // | 3 4 |
    //->
    // | 4 3 |
    //->
    // | 2 1 |
    //->
    // | 4 |
    //->
    // | 3 |
    size_t[2] shape34 = [3, 4];
    size_t[2] shape43 = [4, 3];
    size_t[2] shape21 = [2, 1];
    size_t[1] shape4 = [4];
    size_t[1] shape3 = [3];

    assert(packsOf!(typeof(slice)) == shape21);

    //  ----------------
    // |  0  1  2  3  4 |
    // |  5  6  7  8  9 |
    // | 10 11 12 13 14 |
    // | 15 16 17 18 19 |
    //  - - - - - - - -
    // | 20 21 22 23 24 |
    // | 25 26 27 28 29 |
    // | 30 31 32 33 34 |
    // | 35 36 37 38 39 |
    //  - - - - - - - -
    // | 40 41 42 43 44 |
    // | 45 46 47 48 49 |
    // | 50 51 52 53 54 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isCanonicalSlice!(typeof(x)));
    assert(x.shape == shape34);
    assert(x.front.shape == shape4);
    assert(x.front == iota([4, 5]));
    x.popFront;
    assert(x.front == iota([4, 5], (4 * 5)));
    
    //  ----------------
    // |  0  1  2  3  4 |
    // | 20 21 22 23 24 |
    // | 40 41 42 43 44 |
    //  - - - - - - - -
    // |  5  6  7  8  9 |
    // | 25 26 27 28 29 |
    // | 45 46 47 48 49 |
    //  - - - - - - - -
    // | 10 11 12 13 14 |
    // | 30 31 32 33 34 |
    // | 50 51 52 53 54 |
    //  - - - - - - - -
    // | 15 16 17 18 19 |
    // | 35 36 37 38 39 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto y = slice.adjTransposed!1;
    assert(isCanonicalSlice!(typeof(y)));
    assert(y.shape == shape43);
    assert(y.front.shape == shape3);
    int err;
    assert(y.front == slice.universal.strided!1(4).unpack.reshape([3, -1], err));
    y.popFront;
    assert(y.front.front == iota([5], 5));
}

// Ensure works on contiguous pack!1 slice
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, packsOf;
    import mir.ndslice.dynamic : strided;
    import mir.ndslice.traits : isContiguousSlice, isCanonicalSlice;
    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto slice = iota(2, 3, 4, 5).pack!1;
    //->
    // | 2 3 4 |
    //->
    // | 3 2 4 |
    //->
    // | 4 2 3 |
    //->
    // | 4 3 2 |
    //->
    // | 3 4 2 |
    //->
    // | 2 4 3 |
    //->
    // | 3 4 |
    //->
    // | 2 4 |
    //->
    // | 3 1 |
    //->
    // | 2 3 |
    //->
    // | 4 2 |
    //->
    // | 4 3 |
    size_t[3] shape234 = [2, 3, 4];
    size_t[3] shape324 = [3, 2, 4];
    size_t[3] shape423 = [4, 2, 3];
    size_t[3] shape432 = [4, 3, 2];
    size_t[3] shape342 = [3, 4, 2];
    size_t[3] shape243 = [2, 4, 3];
    size_t[2] shape34 = [3, 4];
    size_t[2] shape24 = [2, 4];
    size_t[2] shape31 = [3, 1];
    size_t[2] shape23 = [2, 3];
    size_t[2] shape32 = [3, 2];
    size_t[2] shape42 = [4, 2];
    size_t[2] shape43 = [4, 3];

    assert(packsOf!(typeof(slice)) == shape31);
    
    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isContiguousSlice!(typeof(x)));
    assert(x.shape == shape234);
    assert(x.front.shape == shape34);
    assert(x.front == iota(3, 4, 5));
    x.popFront;
    assert(x.front == iota([3, 4, 5], (3 * 4 * 5)));
    
    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto y = slice.adjTransposed!1;
    assert(isCanonicalSlice!(typeof(y)));
    assert(y.shape == shape324);
    assert(y.front.shape == shape24);
    assert(y.front.front == iota([4, 5]));
    y.popFront;
    assert(y.front.front == iota([4, 5], (4 * 5)));
    
    //  ---------------------
    // |   0   1   2   3   4 |
    // |  20  21  22  23  24 |
    // |  40  41  42  43  44 |
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  80  81  82  83  84 |
    // | 100 101 102 103 104 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |   5   6   7   8   9 |
    // |  25  26  27  28  29 |
    // |  45  46  47  48  49 |
    //  - - - - - - - - - - -
    // |  65  66  67  68  69 |
    // |  85  86  87  88  89 |
    // | 105 106 107 108 109 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  10  11  12  13  14 |
    // |  30  31  32  33  34 |
    // |  70  71  72  73  74 |
    //  - - - - - - - - - - -
    // |  70  71  72  73  74 |
    // |  90  91  92  93  94 |
    // | 110 111 112 113 114 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  15  16  17  18  19 |
    // |  35  36  37  38  39 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    // |  75  76  77  78  79 |
    // |  95  96  97  98  99 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto z = slice.adjTransposed!2;
    assert(isCanonicalSlice!(typeof(z)));
    assert(z.shape == shape423);
    assert(z.front.shape == shape23);
    int err;
    assert(z.front.front == 
             slice.front.universal.strided!1(4).unpack.reshape([3, -1], err));
    z.popFront;
    assert(z.front.front == slice
                                .front
                                .universal
                                .strided!1(4)
                                .unpack.
                                reshape([3, -1], err)
                                .map!(a => a + 5));
                                
    auto a = slice.adjTransposed!(0, 1);
    assert(a == slice);
    
    //see y
    auto b = slice.adjTransposed!(1, 0);
    auto yAlt = slice.adjTransposed!1; //y, but y has been popFronted
    assert(isCanonicalSlice!(typeof(b)));
    assert(b.shape == yAlt.shape);
    assert(b.front.shape == yAlt.front.shape);
    assert(b.front == yAlt.front);
    b.popFront;
    yAlt.popFront;
    assert(b.front == yAlt.front);
    
    //see z
    auto c = slice.adjTransposed!(2, 0);
    auto zAlt = slice.adjTransposed!2; //z, but z has been popFronted
    assert(isCanonicalSlice!(typeof(c)));
    assert(c.shape == zAlt.shape);
    assert(c.front.shape == zAlt.front.shape);
    assert(c.front == zAlt.front);
    c.popFront;
    zAlt.popFront;
    assert(c.front == zAlt.front);
    
    //  ---------------------
    // |   0   1   2   3   4 |
    // |  60  61  62  63  64 |
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  80  81  82  83  84 |
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // | 100 101 102 103 104 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |   5   6   7   8   9 |
    // |  65  66  67  68  69 |
    //  - - - - - - - - - - -
    // |  25  26  27  28  29 |
    // |  85  86  87  88  89 |
    //  - - - - - - - - - - -
    // |  45  46  47  48  49 |
    // | 105 106 107 108 109 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  10  11  12  13  14 |
    // |  70  71  72  73  74 |
    //  - - - - - - - - - - -
    // |  30  31  32  33  34 |
    // |  90  91  92  93  94 |
    //  - - - - - - - - - - -
    // |  50  51  52  53  54 |
    // | 110 111 112 113 114 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  15  16  17  18  19 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    // |  35  36  37  38  39 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    // |  55  56  57  58  59 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto d = slice.adjTransposed!(2, 1);
    assert(isCanonicalSlice!(typeof(d)));
    assert(d.shape == shape432);
    assert(d.front.shape == shape32);
    assert(d.front.front[0] == iota(5));
    assert(d.front.front[1] == iota([5], 60));
    d.popFront;
    assert(d.front.front[0] == iota([5], 5));
    assert(d.front.front[1] == iota([5], 65));
    
    //  ---------------------
    // |   0   1   2   3   4 |
    // |  60  61  62  63  64 |
    //  - - - - - - - - - - -
    // |   5   6   7   8   9 |
    // |  65  66  67  68  69 |
    //  - - - - - - - - - - -
    // |  10  11  12  13  14 |
    // |  70  71  72  73  74 |
    //  - - - - - - - - - - -
    // |  15  16  17  18  19 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  80  81  82  83  84 |
    //  - - - - - - - - - - -
    // |  25  26  27  28  29 |
    // |  85  86  87  88  89 |
    //  - - - - - - - - - - -
    // |  30  31  32  33  34 |
    // |  90  91  92  93  94 |
    //  - - - - - - - - - - -
    // |  35  36  37  38  39 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // | 100 101 102 103 104 |
    //  - - - - - - - - - - -
    // |  45  46  47  48  49 |
    // | 105 106 107 108 109 |
    //  - - - - - - - - - - -
    // |  50  51  52  53  54 |
    // | 110 111 112 113 114 |
    //  - - - - - - - - - - -
    // |  55  56  57  58  59 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto e = slice.adjTransposed!(1, 2);
    assert(isCanonicalSlice!(typeof(e)));
    assert(e.shape == shape342);
    assert(e.front.shape == shape42);
    assert(e.front.front[0] == iota(5));
    assert(e.front.front[1] == iota([5], 60));
    e.popFront;
    assert(e.front.front[0] == iota([5], 20));
    assert(e.front.front[1] == iota([5], 80));
    
    //  ---------------------
    // |   0   1   2   3   4 |
    // |  20  21  22  23  24 |
    // |  40  41  42  43  44 |
    //  - - - - - - - - - - -
    // |   5   6   7   8   9 |
    // |  25  26  27  28  29 |
    // |  45  46  47  48  49 |
    //  - - - - - - - - - - -
    // |  10  11  12  13  14 |
    // |  30  31  32  33  34 |
    // |  70  71  72  73  74 |
    //  - - - - - - - - - - -
    // |  15  16  17  18  19 |
    // |  35  36  37  38  39 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  80  81  82  83  84 |
    // | 100 101 102 103 104 |
    //  - - - - - - - - - - -
    // |  65  66  67  68  69 |
    // |  85  86  87  88  89 |
    // | 105 106 107 108 109 |
    //  - - - - - - - - - - -
    // |  70  71  72  73  74 |
    // |  90  91  92  93  94 |
    // | 110 111 112 113 114 |
    //  - - - - - - - - - - -
    // |  75  76  77  78  79 |
    // |  95  96  97  98  99 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto f = slice.adjTransposed!(0, 2);
    assert(isCanonicalSlice!(typeof(f)));
    assert(f.shape == shape243);
    assert(f.front.shape == shape43);
    assert(f.front.front[0] == iota(5));
    assert(f.front.front[1] == iota([5], 20));
    assert(f.front.front[2] == iota([5], 40));
    f.popFront;
    assert(f.front.front[0] == iota([5], 60));
    assert(f.front.front[1] == iota([5], 80));
    assert(f.front.front[2] == iota([5], 100));
}


// Ensure works on contiguous pack!2 slice
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, packsOf;
    import mir.ndslice.traits : isContiguousSlice, isUniversalSlice, 
                                isCanonicalSlice;
    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto slice = iota(2, 3, 4, 5).pack!2;
    //->
    // | 2 3 |
    //->
    // | 3 2 |
    //->
    // | 2 2 |
    //->
    // | 3 |
    //->
    // | 2 |
    size_t[2] shape23 = [2, 3];
    size_t[2] shape32 = [3, 2];
    size_t[2] shape22 = [2, 2];
    size_t[1] shape3 = [3];
    size_t[1] shape2 = [2];
    
    assert(packsOf!(typeof(slice)) == shape22);

    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto x = slice.adjTransposed;
    assert(x == slice);
    assert(isContiguousSlice!(typeof(x)));
    assert(x.shape == shape23);
    assert(x.front.shape == shape3);
    assert(x.front == iota(3, 4, 5));
    x.popFront;
    assert(x.front == iota([3, 4, 5], (3 * 4 * 5)));
    
    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto y = slice.adjTransposed!1;
    assert(isCanonicalSlice!(typeof(y)));
    assert(y.shape == shape32);
    assert(y.front.shape == shape2);
    assert(y.front.front == iota([4, 5]));
    y.popFront;
    assert(y.front.front == iota([4, 5], (4 * 5)));
    
    auto z = slice.adjTransposed!(0, 1);
    assert(z == slice);
    
    auto a = slice.adjTransposed!(1, 0);
    auto yAlt = slice.adjTransposed!1; //y, but y has been popFronted
    assert(isCanonicalSlice!(typeof(a)));
    assert(a.shape == yAlt.shape);
    assert(a.front.shape == yAlt.front.shape);
    assert(a.front == yAlt.front);
    a.popFront;
    yAlt.popFront;
    assert(a.front == yAlt.front);
}

// Ensure works on contiguous pack!3 slice
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, packsOf;
    import mir.ndslice.traits : isContiguousSlice, isUniversalSlice, 
                                isCanonicalSlice;
    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto slice = iota(2, 3, 4, 5).pack!3;
    //->
    // | 3 4 5 |
    //->
    // | 1 3 |
    //->
    // | 2 |
    size_t[3] shape345 = [3, 4, 5];
    size_t[2] shape13 = [1, 3];
    size_t[1] shape2 = [2];
    
    assert(packsOf!(typeof(slice)) == shape13);

    //  ---------------------
    // |   0   1   2   3   4 |
    // |   5   6   7   8   9 |
    // |  10  11  12  13  14 |
    // |  15  16  17  18  19 |
    //  - - - - - - - - - - -
    // |  20  21  22  23  24 |
    // |  25  26  27  28  29 |
    // |  30  31  32  33  34 |
    // |  35  36  37  38  39 |
    //  - - - - - - - - - - -
    // |  40  41  42  43  44 |
    // |  45  46  47  48  49 |
    // |  50  51  52  53  54 |
    // |  55  56  57  58  59 |
    //  - - - - - - - - - - -
    //  - - - - - - - - - - -
    // |  60  61  62  63  64 |
    // |  65  66  67  68  69 |
    // |  70  71  72  73  74 |
    // |  75  76  77  78  79 |
    //  - - - - - - - - - - -
    // |  80  81  82  83  84 |
    // |  85  86  87  88  89 |
    // |  90  91  92  93  94 |
    // |  95  96  97  98  99 |
    //  - - - - - - - - - - -
    // | 100 101 102 103 104 |
    // | 105 106 107 108 109 |
    // | 110 111 112 113 114 |
    // | 115 116 117 118 119 |
    //  ---------------------
    auto x = slice.adjTransposed;

    assert(x == slice);
    assert(isContiguousSlice!(typeof(x)));
    assert(x.shape == shape2);
    assert(x.front.shape == shape345);
    assert(x.front == iota(3, 4, 5));
    x.popFront;
    assert(x.front == iota([3, 4, 5], (3 * 4 * 5)));
}

/++
Returns a slice that can be iterated by dimension. Transposes dimensions on top and then packs them.

Combines $(LREF transposed) and $(LREF ipack).

Params:
    dim = dimension to perform iteration on
    slice = input slice (may not be 1-dimensional slice)
Returns:
    n-dimensional slice ipacked to allow iteration by dimension
See_also:
    $(LREF slice),
    $(LREF ipack),
    $(LREF transposed).
+/
template byDim(Dimensions...)
    if (Dimensions.length)
{
    import mir.ndslice.slice : Slice, SliceKind;
    import mir.ndslice.internal : isSize_t, toSize_t;
    import std.meta : allSatisfy, staticMap;
   
    static if (!allSatisfy!(isSize_t, Dimensions))
        alias byDim = .byDim!(staticMap!(toSize_t, Dimensions));
    else
    ///
    @fastmath auto byDim(SliceKind kind, size_t[] packs, Iterator)
                                        (Slice!(kind, packs, Iterator) slice)
    {
        import mir.ndslice.topology : ipack;
        import mir.ndslice.internal : DimensionsCountCTError, DimensionCTError;
       
        mixin DimensionsCountCTError;

        static if (packs == [1])
        {
            return slice;
        }
        else
        {
            import mir.ndslice.topology : ipack;
            return slice.adjTransposed!Dimensions.ipack!1;
        }
    }
}

///
auto byDim(SliceKind kind, size_t[] packs, Iterator)
                                        (Slice!(kind, packs, Iterator) slice)
{
    return slice.byDim!0;
}

/// 2-dimensional slice support
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota;
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto slice = iota(3, 4);
    //->
    // | 3 |
    //->
    // | 4 |
    size_t[1] shape3 = [3];
    size_t[1] shape4 = [4];
    
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto x = slice.byDim;
    assert(x.shape == shape3);
    assert(x.front.shape == shape4);
    assert(x.front == iota(4));
    x.popFront;
    assert(x.front == iota([4], 4));
    
    //  ---------
    // | 0  4  8 |
    // | 1  5  9 |
    // | 2  6 10 |
    // | 3  7 11 |
    //  ---------
    auto y = slice.byDim!1;
    assert(y.shape == shape4);
    assert(y.front.shape == shape3);
    assert(y.front == iota([3], 0, 4));
    y.popFront;
    assert(y.front == iota([3], 1, 4));
}

/// 3-dimensional slice support, N-dimensional also supported
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, universal, flattened, reshape;
    import mir.ndslice.dynamic : strided, transposed;
    //  ----------------
    // | 0   1  2  3  4 |
    // | 5   6  7  8  9 |
    // | 10 11 12 13 14 |
    // | 15 16 17 18 19 |
    //  - - - - - - - -
    // | 20 21 22 23 24 |
    // | 25 26 27 28 29 |
    // | 30 31 32 33 34 |
    // | 35 36 37 38 39 |
    //  - - - - - - - -
    // | 40 41 42 43 44 |
    // | 45 46 47 48 49 |
    // | 50 51 52 53 54 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto slice = iota(3, 4, 5);
    //->
    // | 4 5 |
    //->
    // | 3 5 |
    //->
    // | 3 4 |
    //->
    // | 4 3 |
    //->
    // | 3 |
    //->
    // | 4 |
    //->
    // | 5 |
    size_t[2] shape45 = [4, 5];
    size_t[2] shape35 = [3, 5];
    size_t[2] shape34 = [3, 4];
    size_t[2] shape43 = [4, 3];
    size_t[1] shape3 = [3];
    size_t[1] shape4 = [4];
    size_t[1] shape5 = [5];
    
    //  ----------------
    // |  0  1  2  3  4 |
    // |  5  6  7  8  9 |
    // | 10 11 12 13 14 |
    // | 15 16 17 18 19 |
    //  - - - - - - - -
    // | 20 21 22 23 24 |
    // | 25 26 27 28 29 |
    // | 30 31 32 33 34 |
    // | 35 36 37 38 39 |
    //  - - - - - - - -
    // | 40 41 42 43 44 |
    // | 45 46 47 48 49 |
    // | 50 51 52 53 54 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto x = slice.byDim;
    assert(x.shape == shape3);
    assert(x.front.shape == shape45);
    assert(x.front == iota([4, 5]));
    x.popFront;
    assert(x.front == iota([4, 5], (4 * 5)));
    
    //  ----------------
    // |  0  1  2  3  4 |
    // | 20 21 22 23 24 |
    // | 40 41 42 43 44 |
    //  - - - - - - - -
    // |  5  6  7  8  9 |
    // | 25 26 27 28 29 |
    // | 45 46 47 48 49 |
    //  - - - - - - - -
    // | 10 11 12 13 14 |
    // | 30 31 32 33 34 |
    // | 50 51 52 53 54 |
    //  - - - - - - - -
    // | 15 16 17 18 19 |
    // | 35 36 37 38 39 |
    // | 55 56 57 58 59 |
    //  ----------------
    auto y = slice.byDim!1;
    assert(y.shape == shape4);
    assert(y.front.shape == shape35);
    int err;
    assert(y.front == slice.universal.strided!1(4).reshape([3, -1], err));
    y.popFront;
    assert(y.front.front == iota([5], 5));
    
    //  -------------
    // |  0  5 10 15 |
    // | 20 25 30 35 |
    // | 40 45 50 55 |
    //  - - - - - - -
    // |  1  6 11 16 |
    // | 21 26 31 36 |
    // | 41 46 51 56 |
    //  - - - - - - -
    // |  2  7 12 17 |
    // | 22 27 32 37 |
    // | 42 47 52 57 |
    //  - - - - - - -
    // |  3  8 13 18 |
    // | 23 28 33 38 |
    // | 43 48 53 58 |
    //  - - - - - - -
    // |  4  9 14 19 |
    // | 24 29 34 39 |
    // | 44 49 54 59 |
    //  -------------
    auto z = slice.byDim!2;
    assert(z.shape == shape5);
    assert(z.front.shape == shape34);
    assert(z.front == iota([3, 4], 0, 5));
    z.popFront;
    assert(z.front.front == iota([4], 1, 5));

    //  ----------
    // |  0 20 40 |
    // |  5 25 45 |
    // | 10 30 50 |
    // | 15 35 55 |
    //  - - - - -
    // |  1 21 41 |
    // |  6 26 46 |
    // | 11 31 51 |
    // | 16 36 56 |
    //  - - - - -
    // |  2 22 42 |
    // |  7 27 47 |
    // | 12 32 52 |
    // | 17 37 57 |
    //  - - - - -
    // |  3 23 43 |
    // |  8 28 48 |
    // | 13 33 53 |
    // | 18 38 58 |
    //  - - - - -
    // |  4 24 44 |
    // |  9 29 49 |
    // | 14 34 54 |
    // | 19 39 59 |
    //  ----------
    auto a = slice.byDim!(2, 1);
    assert(a.shape == shape5);
    assert(a.front.shape == shape43);
    assert(a.front == iota([3, 4], 0, 5).universal.transposed!1);
    a.popFront;
    assert(a.front.front == iota([3], 1, 20));
}

// Ensure works on canonical
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, canonical;
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto slice = iota(3, 4).canonical;
    //->
    // | 3 |
    //->
    // | 4 |
    size_t[1] shape3 = [3];
    size_t[1] shape4 = [4];
    
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto x = slice.byDim;
    assert(x.shape == shape3);
    assert(x.front.shape == shape4);
    assert(x.front == iota(4));
    x.popFront;
    assert(x.front == iota([4], 4));
    
    //  ---------
    // | 0  4  8 |
    // | 1  5  9 |
    // | 2  6 10 |
    // | 3  7 11 |
    //  ---------
    auto y = slice.byDim!1;
    assert(y.shape == shape4);
    assert(y.front.shape == shape3);
    assert(y.front == iota([3], 0, 4));
    y.popFront;
    assert(y.front == iota([3], 1, 4));
}

// Ensure works on universal
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota, universal;
    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto slice = iota(3, 4).universal;
    //->
    // | 3 |
    //->
    // | 4 |
    size_t[1] shape3 = [3];
    size_t[1] shape4 = [4];

    //  ------------
    // | 0  1  2  3 |
    // | 4  5  6  7 |
    // | 8  9 10 11 |
    //  ------------
    auto x = slice.byDim;
    assert(x.shape == shape3);
    assert(x.front.shape == shape4);
    assert(x.front == iota(4));
    x.popFront;
    assert(x.front == iota([4], 4));
    
    //  ---------
    // | 0  4  8 |
    // | 1  5  9 |
    // | 2  6 10 |
    // | 3  7 11 |
    //  ---------
    auto y = slice.byDim!1;
    assert(y.shape == shape4);
    assert(y.front.shape == shape3);
    assert(y.front == iota([3], 0, 4));
    y.popFront;
    assert(y.front == iota([3], 1, 4));
}

// 1-dimensional slice support
@safe @nogc pure nothrow
unittest
{
    import mir.ndslice.topology : iota;
    //  -------
    // | 0 1 2 |
    //  -------
    auto slice = iota(3);
    auto x = slice.byDim;
    assert(x == slice);
}
