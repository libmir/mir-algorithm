/++
This is a submodule of $(MREF mir,ndslice).

Selectors create new views and iteration patterns over the same data, without copying.

$(BOOKTABLE $(H2 SliceKind Selectors),
$(TR $(TH Function Name) $(TH Description))

$(T2 universal, Converts a slice to universal $(SUBREF slice, SliceKind).)
$(T2 canonical, Converts a slice to canonical $(SUBREF slice, SliceKind).)
$(T2 assumeCanonical, Converts a slice to canonical $(SUBREF slice, SliceKind) (unsafe).)
$(T2 assumeContiguous, Converts a slice to contiguous $(SUBREF slice, SliceKind) (unsafe).)

)

$(BOOKTABLE $(H2 Sequence Selectors),
$(TR $(TH Function Name) $(TH Description))

$(T2 cycle, Cycle repeates 1-dimensional field/range/array/slice in a fixed length 1-dimensional slice)
$(T2 iota, Contiguous Slice with initial flattened (contiguous) index.)
$(T2 linspace, Evenly spaced numbers over a specified interval.)
$(T2 magic, Magic square.)
$(T2 ndiota, Contiguous Slice with initial multidimensional index.)
$(T2 repeat, Slice with identical values)
)

.

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
$(T2 bytegroup, Groups existing slice into fixed length chunks and uses them as data store for destination type.)
$(T2 cached, Random access cache. It is usefull in combiation with $(LREF map) and $(LREF vmap).)
$(T2 cachedGC, Random access cache auto-allocated in GC heap. It is usefull in combiation with $(LREF map) and $(LREF vmap).)
$(T2 diff, Differences between vector elements.)
$(T2 flattened, Contiguous 1-dimensional slice of all elements of a slice.)
$(T2 map, Multidimensional functional map.)
$(T2 member, Field (element's member) projection.)
$(T2 orthogonalReduceField, Functional deep-element wise reduce of a slice composed of fields or iterators.)
$(T2 pairwise, Pairwise map for vectors.)
$(T2 pairwiseMapSubSlices, Maps pairwise indexes pairs to subslices.)
$(T2 retro, Reverses order of iteration for all dimensions.)
$(T2 slide, Sliding map for vectors.)
$(T2 stairs, Two functions to pack, unpack, and iterate triangular and symmetric matrix storage.)
$(T2 stride, Strides 1-dimensional slice.)
$(T2 subSlices, Maps indexes pairs to subslices.)
$(T2 triplets, Constructs a lazy view of triplets with `left`, `center`, and `right` members. The topology is usefull for Math and Physics.)
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
$(T2 unpack   , Merges two hight dimension packs. See also $(SUBREF fuse, fuse).)
$(T2 evertPack, Reverses dimension packs.)
$(T2 byDim    , Returns a slice that can be iterated by dimension. Transposes dimensions on top and then packs them.)

)

Subspace selectors serve to generalize and combine other selectors easily.
For a slice of `Slice!(Iterator, N, kind)` type `slice.pack!K` creates a slice of
slices of `Slice!(kind, [N - K, K], Iterator)` type by packing
the last `K` dimensions of the top dimension pack,
and the type of element of $(LREF flattened) is `Slice!(Iterator, K)`.
Another way to use $(LREF pack) is transposition of dimension packs using
$(LREF evertPack).
Examples of use of subspace selectors are available for selectors,
$(SUBREF slice, Slice.shape), and $(SUBREF slice, Slice.elementCount).


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

import std.meta;

import mir.internal.utility;
import mir.math.common: optmath;
import mir.ndslice.field;
import mir.ndslice.internal;
import mir.ndslice.iterator;
import mir.ndslice.ndfield;
import mir.ndslice.slice;
import mir.primitives;
import mir.qualifier;
import mir.utility: min;

private immutable choppedExceptionMsg = "bounds passed to chopped are out of sliceable bounds.";
version (D_Exceptions) private immutable choppedException = new Exception(choppedExceptionMsg);

@optmath:

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
auto universal(Iterator, size_t N, SliceKind kind, Labels...)(Slice!(Iterator, N, kind, Labels) slice)
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
        alias Ret = Slice!(Iterator, N, Universal, Labels);
        size_t[Ret.N] lengths;
        auto strides = sizediff_t[Ret.S].init;
        foreach (i; Iota!(slice.N))
            lengths[i] = slice._lengths[i];
        static if (kind == Canonical)
        {
            foreach (i; Iota!(slice.S))
                strides[i] = slice._strides[i];
            strides[$-1] = 1;
        }
        else
        {
            ptrdiff_t ball = 1;
            foreach_reverse (i; Iota!(Ret.S))
            {
                strides[i] = ball;
                static if (i)
                    ball *= slice._lengths[i];
            }
        }
        return Ret(lengths, strides, slice._iterator, slice._labels);
    }
}

///
@safe pure nothrow
version(mir_test) unittest
{
    auto slice = iota(2, 3).universal;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3, 1]);
}

@safe pure nothrow
version(mir_test) unittest
{
    auto slice = iota(2, 3).canonical.universal;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3, 1]);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation: slice;

    auto dataframe = slice!(double, int, string)(2, 3);
    dataframe.label[] = [1, 2];
    dataframe.label!1[] = ["Label1", "Label2", "Label3"];

    auto universaldf = dataframe.universal;
    assert(universaldf._lengths == [2, 3]);
    assert(universaldf._strides == [3, 1]);

    assert(is(typeof(universaldf) ==
        Slice!(double*, 2, Universal, int*, string*)));
    assert(universaldf.label!0[0] == 1);
    assert(universaldf.label!1[1] == "Label2");
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
Slice!(Iterator, N, N == 1 ? Contiguous : Canonical, Labels)
    canonical
    (Iterator, size_t N, SliceKind kind, Labels...)
    (Slice!(Iterator, N, kind, Labels) slice)
    if (kind == Contiguous || kind == Canonical)
{
    static if (kind == Canonical || N == 1)
        return slice;
    else
    {
        alias Ret = typeof(return);
        size_t[Ret.N] lengths;
        auto strides = sizediff_t[Ret.S].init;
        foreach (i; Iota!(slice.N))
            lengths[i] = slice._lengths[i];
        ptrdiff_t ball = 1;
        foreach_reverse (i; Iota!(Ret.S))
        {
            ball *= slice._lengths[i + 1];
            strides[i] = ball;
        }
        return Ret(lengths, strides, slice._iterator, slice._labels);
    }
}

///
@safe pure nothrow
version(mir_test) unittest
{
    auto slice = iota(2, 3).canonical;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3]);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation: slice;

    auto dataframe = slice!(double, int, string)(2, 3);
    dataframe.label[] = [1, 2];
    dataframe.label!1[] = ["Label1", "Label2", "Label3"];

    auto canonicaldf = dataframe.canonical;
    assert(canonicaldf._lengths == [2, 3]);
    assert(canonicaldf._strides == [3]);

    assert(is(typeof(canonicaldf) ==
        Slice!(double*, 2, Canonical, int*, string*)));
    assert(canonicaldf.label!0[0] == 1);
    assert(canonicaldf.label!1[1] == "Label2");
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
Slice!(Iterator, N, Canonical, Labels)
    assumeCanonical
    (Iterator, size_t N, SliceKind kind, Labels...)
    (Slice!(Iterator, N, kind, Labels) slice)
{
    static if (kind == Contiguous)
        return slice.canonical;
    else
    static if (kind == Canonical)
        return slice;
    else
    {
        alias Ret = typeof(return);
        size_t[Ret.N] lengths;
        auto strides = sizediff_t[Ret.S].init;
        foreach (i; Iota!(slice.N))
            lengths[i] = slice._lengths[i];
        foreach (i; Iota!(Ret.S))
            strides[i] = slice._strides[i];
        return Ret(lengths, strides, slice._iterator, slice._labels);
    }
}

///
@safe pure nothrow
version(mir_test) unittest
{
    auto slice = iota(2, 3).universal.assumeCanonical;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    assert(slice._strides == [3]);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation: slice;

    auto dataframe = slice!(double, int, string)(2, 3);
    dataframe.label[] = [1, 2];
    dataframe.label!1[] = ["Label1", "Label2", "Label3"];

    auto assmcanonicaldf = dataframe.assumeCanonical;
    assert(assmcanonicaldf._lengths == [2, 3]);
    assert(assmcanonicaldf._strides == [3]);

    assert(is(typeof(assmcanonicaldf) ==
        Slice!(double*, 2, Canonical, int*, string*)));
    assert(assmcanonicaldf.label!0[0] == 1);
    assert(assmcanonicaldf.label!1[1] == "Label2");
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
Slice!(Iterator, N, Contiguous, Labels)
    assumeContiguous
    (Iterator, size_t N, SliceKind kind, Labels...)
    (Slice!(Iterator, N, kind, Labels) slice)
{
    static if (kind == Contiguous)
        return slice;
    else
    {
        return typeof(return)(slice._lengths, slice._iterator, slice._labels);
    }
}

///
@safe pure nothrow
version(mir_test) unittest
{
    auto slice = iota(2, 3).universal.assumeContiguous;
    assert(slice == [[0, 1, 2], [3, 4, 5]]);
    assert(slice._lengths == [2, 3]);
    static assert(slice._strides.length == 0);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation: slice;

    auto dataframe = slice!(double, int, string)(2, 3);
    dataframe.label[] = [1, 2];
    dataframe.label!1[] = ["Label1", "Label2", "Label3"];

    auto assmcontdf = dataframe.canonical.assumeContiguous;
    assert(assmcontdf._lengths == [2, 3]);
    static assert(assmcontdf._strides.length == 0);

    assert(is(typeof(assmcontdf) ==
        Slice!(double*, 2, Contiguous, int*, string*)));
    assert(assmcontdf.label!0[0] == 1);
    assert(assmcontdf.label!1[1] == "Label2");
}

/++
+/
auto assumeFieldsHaveZeroShift(Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice)
    if (__traits(hasMember, Iterator, "assumeFieldsHaveZeroShift"))
{
    return slice._iterator.assumeFieldsHaveZeroShift.slicedField(slice._lengths);
}

/++
Creates a packed slice, i.e. slice of slices.
Packs the last `P` dimensions.
The function does not allocate any data.

Params:
    P = size of dimension pack
    slice = a slice to pack
Returns:
    `slice.pack!p` returns `Slice!(kind, [N - p, p], Iterator)`
See_also: $(LREF ipack)
+/
Slice!(SliceIterator!(Iterator, P, P == 1 && kind == Canonical ? Contiguous : kind), N - P, Universal)
pack(size_t P, Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    if (P && P < N)
{
    return slice.ipack!(N - P);
}

///
@safe @nogc pure nothrow version(mir_test) unittest
{
    import mir.ndslice.slice : sliced, Slice;

    auto a = iota(3, 4, 5, 6);
    auto b = a.pack!2;

    static immutable res1 = [3, 4];
    static immutable res2 = [5, 6];
    assert(b.shape == res1);
    assert(b[0, 0].shape == res2);
    assert(a == b.unpack);
    assert(a.pack!2 == b);
    static assert(is(typeof(b) == typeof(a.pack!2)));
}

/++
Creates a packed slice, i.e. slice of slices.
Packs the last `N - P` dimensions.
The function does not allocate any data.

Params:
    + = size of dimension pack
    slice = a slice to pack
See_also: $(LREF pack)
+/
Slice!(SliceIterator!(Iterator, N - P, N - P == 1 && kind == Canonical ? Contiguous : kind), P, Universal)
ipack(size_t P, Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    if (P && P < N)
{
    alias Ret = typeof(return);
    alias It = Ret.Iterator;
    alias EN = It.Element.N;
    alias ES = It.Element.S;
    auto sl = slice.universal;
    static if (It.Element.kind == Contiguous)
        return Ret(
            cast(   size_t[P]) sl._lengths[0 .. P],
            cast(ptrdiff_t[P]) sl._strides[0 .. P],
            It(
                cast(size_t[EN]) sl._lengths[P .. $],
                sl._iterator));
    else
        return Ret(
            cast(   size_t[P]) sl._lengths[0 .. P],
            cast(ptrdiff_t[P]) sl._strides[0 .. P],
            It(
                cast(   size_t[EN]) sl._lengths[P .. $],
                cast(ptrdiff_t[ES]) sl._strides[P .. $ - (It.Element.kind == Canonical)],
                sl._iterator));
}

///
@safe @nogc pure nothrow version(mir_test) unittest
{
    import mir.ndslice.slice : sliced, Slice;

    auto a = iota(3, 4, 5, 6);
    auto b = a.ipack!2;

    static immutable res1 = [3, 4];
    static immutable res2 = [5, 6];
    assert(b.shape == res1);
    assert(b[0, 0].shape == res2);
    assert(a.ipack!2 == b);
    static assert(is(typeof(b) == typeof(a.ipack!2)));
}

/++
Unpacks a packed slice.

The functions does not allocate any data.

Params:
    slice = packed slice
Returns:
    unpacked slice, that is a view on the same data.

See_also: $(LREF pack), $(LREF evertPack)
+/
Slice!(Iterator, N + M, min(innerKind, Canonical))
    unpack(Iterator, size_t M, SliceKind innerKind, size_t N, SliceKind outerKind)
    (Slice!(SliceIterator!(Iterator, M, innerKind), N, outerKind) slice)
{
    alias Ret = typeof(return);
    size_t[N + M] lengths;
    auto strides = sizediff_t[Ret.S].init;
    auto outerStrides = slice.strides;
    auto innerStrides = Slice!(Iterator, M, innerKind)(
        slice._iterator._structure,
        slice._iterator._iterator,
        ).strides;
    foreach(i; Iota!N)
        lengths[i] = slice._lengths[i];
    foreach(i; Iota!N)
        strides[i] = outerStrides[i];
    foreach(i; Iota!M)
        lengths[N + i] = slice._iterator._structure[0][i];
    foreach(i; Iota!(Ret.S - N))
        strides[N + i] = innerStrides[i];
    return Ret(lengths, strides, slice._iterator._iterator);
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
Slice!(SliceIterator!(Iterator, N, outerKind), M, innerKind)
evertPack(Iterator, size_t M, SliceKind innerKind, size_t N, SliceKind outerKind)
    (Slice!(SliceIterator!(Iterator, M, innerKind), N, outerKind) slice)
{
    return typeof(return)(
        slice._iterator._structure,
        typeof(return).Iterator(
            slice._structure,
            slice._iterator._iterator));
}

///
@safe @nogc pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: slice;
    static assert(is(typeof(
        slice!int(6)
            .sliced(1,2,3)
            .pack!1
            .evertPack()
        )
         == Slice!(SliceIterator!(int*, 2, Universal), 1)));
}


///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    auto a = iota(3, 4, 5, 6, 7, 8, 9, 10, 11);
    auto b = a.pack!2.unpack;
    static assert(is(typeof(a.canonical) == typeof(b)));
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
Slice!(IotaIterator!I, N)
iota
    (I = sizediff_t, size_t N)(size_t[N] lengths...)
    if (__traits(isIntegral, I))
{
    import mir.ndslice.slice : sliced;
    return IotaIterator!I(I.init).sliced(lengths);
}

///ditto
Slice!(IotaIterator!sizediff_t, N)
iota
    (size_t N)(size_t[N] lengths, sizediff_t start)
{
    import mir.ndslice.slice : sliced;
    return IotaIterator!sizediff_t(start).sliced(lengths);
}

///ditto
Slice!(StrideIterator!(IotaIterator!sizediff_t), N)
iota
    (size_t N)(size_t[N] lengths, sizediff_t start, size_t stride)
{
    import mir.ndslice.slice : sliced;
    return StrideIterator!(IotaIterator!sizediff_t)(stride, IotaIterator!sizediff_t(start)).sliced(lengths);
}

///ditto
template iota(I)
    if (__traits(isIntegral, I))
{
    ///
    Slice!(IotaIterator!I, N)
    iota
        (size_t N)(size_t[N] lengths, I start)
        if (__traits(isIntegral, I))
    {
        import mir.ndslice.slice : sliced;
        return IotaIterator!I(start).sliced(lengths);
    }

    ///ditto
    Slice!(StrideIterator!(IotaIterator!I), N)
    iota
        (size_t N)(size_t[N] lengths, I start, size_t stride)
        if (__traits(isIntegral, I))
    {
        import mir.ndslice.slice : sliced;
        return StrideIterator!(IotaIterator!I)(stride, IotaIterator!I(start)).sliced(lengths);
    }
}

///ditto
Slice!(IotaIterator!I, N)
iota
    (I, size_t N)(size_t[N] lengths, I start)
    if (is(I P : P*))
{
    import mir.ndslice.slice : sliced;
    return IotaIterator!I(start).sliced(lengths);
}

///ditto
Slice!(StrideIterator!(IotaIterator!I), N)
iota
    (I, size_t N)(size_t[N] lengths, I start, size_t stride)
    if (is(I P : P*))
{
    import mir.ndslice.slice : sliced;
    return StrideIterator!(IotaIterator!I)(stride, IotaIterator!I(start)).sliced(lengths);
}

///
@safe pure nothrow @nogc version(mir_test) unittest
{
    auto slice = iota(2, 3);
    static immutable array =
        [[0, 1, 2],
         [3, 4, 5]];

    assert(slice == array);

    static assert(is(DeepElementType!(typeof(slice)) == sizediff_t));
}

///
pure nothrow @nogc
version(mir_test) unittest
{
    int[6] data;
    auto slice = iota([2, 3], data.ptr);
    assert(slice[0, 0] == data.ptr);
    assert(slice[0, 1] == data.ptr + 1);
    assert(slice[1, 0] == data.ptr + 3);
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    auto im = iota([10, 5], 100);
    assert(im[2, 1] == 111); // 100 + 2 * 5 + 1

    //slicing works correctly
    auto cm = im[1 .. $, 3 .. $];
    assert(cm[2, 1] == 119); // 119 = 100 + (1 + 2) * 5 + (3 + 1)
}

/// `iota` with step
@safe pure nothrow version(mir_test) unittest
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
See_also: $(LREF antidiagonal)
+/
Slice!(Iterator, 1, N == 1 ? kind : Universal)
    diagonal
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice)
{
    static if (N == 1)
    {
        return slice;
    }
    else
    {
        alias Ret = typeof(return);
        size_t[Ret.N] lengths;
        auto strides = sizediff_t[Ret.S].init;
        lengths[0] = slice._lengths[0];
        foreach (i; Iota!(1, N))
            if (lengths[0] > slice._lengths[i])
                lengths[0] = slice._lengths[i];
        foreach (i; Iota!(1, Ret.N))
            lengths[i] = slice._lengths[i + N - 1];
        auto rstrides = slice.strides;
        strides[0] = rstrides[0];
        foreach (i; Iota!(1, N))
            strides[0] += rstrides[i];
        foreach (i; Iota!(1, Ret.S))
            strides[i] = rstrides[i + N - 1];
        return Ret(lengths, strides, slice._iterator);
    }
}

/// Matrix, main diagonal
@safe @nogc pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
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
version(mir_test) unittest
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

/// 3D, main diagonal
@safe @nogc pure nothrow version(mir_test) unittest
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
@safe @nogc pure nothrow version(mir_test) unittest
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
version(mir_test) unittest
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
Returns a 1-dimensional slice over the main antidiagonal of an 2D-dimensional slice.
`antidiagonal` can be generalized with other selectors such as
$(LREF blocks) (diagonal blocks) and $(LREF windows) (multi-diagonal slice).

It runs from the top right corner to the bottom left corner.

Pseudo_code:
------
auto antidiagonal = slice.dropToHypercube.reversed!1.diagonal;
------

Params:
    slice = input slice
Returns:
    1-dimensional slice composed of antidiagonal elements.
See_also: $(LREF diagonal)
+/
Slice!(Iterator, 1, Universal)
    antidiagonal
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice)
    if (N == 2)
{
    import mir.ndslice.dynamic : dropToHypercube, reversed;
    return slice.dropToHypercube.reversed!1.diagonal;
}

///
@safe @nogc pure nothrow version(mir_test) unittest
{
    //  -----
    // | 0 1 |
    // | 2 3 |
    //  -----
    //->
    // | 1 2 |
    static immutable c = [1, 2];
    import std.stdio;
    assert(iota(2, 2).antidiagonal == c);
}

///
@safe @nogc pure nothrow version(mir_test) unittest
{
    //  -------
    // | 0 1 2 |
    // | 3 4 5 |
    //  -------
    //->
    // | 1 3 |
    static immutable d = [1, 3];
    assert(iota(2, 3).antidiagonal == d);
}

/++
Returns an n-dimensional slice of n-dimensional non-overlapping blocks.
`blocks` can be generalized with other selectors.
For example, `blocks` in combination with $(LREF diagonal) can be used to get a slice of diagonal blocks.
For overlapped blocks, combine $(LREF windows) with $(SUBREF dynamic, strided).

Params:
    N = dimension count
    slice = slice to be split into blocks
    rlengths_ = dimensions of block, residual blocks are ignored
Returns:
    packed `N`-dimensional slice composed of `N`-dimensional slices

See_also: $(SUBREF chunks, ._chunks)
+/
Slice!(SliceIterator!(Iterator, N, N == 1 ? Universal : min(kind, Canonical)), N, Universal)
    blocks
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice, size_t[N] rlengths_...)
in
{
    foreach (i, length; rlengths_)
        assert(length > 0, "length of dimension = " ~ i.stringof ~ " must be positive"
            ~ tailErrorMessage!());
}
do
{
    size_t[N] lengths;
    size_t[N] rlengths = rlengths_;
    sizediff_t[N] strides;
    foreach (dimension; Iota!N)
        lengths[dimension] = slice._lengths[dimension] / rlengths[dimension];
    auto rstrides = slice.strides;
    foreach (i; Iota!N)
    {
        strides[i] = rstrides[i];
        if (lengths[i]) //do not remove `if (...)`
            strides[i] *= rlengths[i];
    }
    return typeof(return)(
        lengths,
        strides,
        typeof(return).Iterator(
            rlengths,
            rstrides[0 .. typeof(return).DeepElement.S],
            slice._iterator));
}

///
pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
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
@safe pure version(mir_test) unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto slice = slice!int(5, 13);
    auto blocks = slice
        .pack!1
        .evertPack
        .blocks(3)
        .unpack;

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
    rlengths = dimensions of windows
Returns:
    packed `N`-dimensional slice composed of `N`-dimensional slices
+/
Slice!(SliceIterator!(Iterator, N, N == 1 ? kind : min(kind, Canonical)), N, Universal)
    windows
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice, size_t[N] rlengths...)
in
{
    foreach (i, length; rlengths)
        assert(length > 0, "length of dimension = " ~ i.stringof ~ " must be positive"
            ~ tailErrorMessage!());
}
do
{
    size_t[N] rls = rlengths;
    size_t[N] lengths;
    foreach (dimension; Iota!N)
        lengths[dimension] = slice._lengths[dimension] >= rls[dimension] ?
            slice._lengths[dimension] - rls[dimension] + 1 : 0;
    auto rstrides = slice.strides;
    static if (typeof(return).DeepElement.S)
        return typeof(return)(
            lengths,
            rstrides,
            typeof(return).Iterator(
                rls,
                rstrides[0 .. typeof(return).DeepElement.S],
                slice._iterator));
    else
        return typeof(return)(
            lengths,
            rstrides,
            typeof(return).Iterator(
                rls,
                slice._iterator));
}

///
@safe pure nothrow
version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto slice = slice!int(5, 8);
    auto windows = slice
        .pack!1
        .evertPack
        .windows(3)
        .unpack;

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
@safe pure nothrow version(mir_test) unittest
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

version(mir_test) unittest
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
    rlengths = list of new dimensions. One of the lengths can be set to `-1`.
        In this case, the corresponding dimension is inferable.
    err = $(LREF ReshapeError) code
Returns:
    reshaped slice
+/
Slice!(Iterator, M, kind) reshape
        (Iterator, size_t N, SliceKind kind, size_t M)
        (Slice!(Iterator, N, kind) slice, ptrdiff_t[M] rlengths, ref int err)
{
    static if (kind == Canonical)
    {
        auto r = slice.universal.reshape(rlengths, err);
        assert(err || r._strides[$-1] == 1);
        r._strides[$-1] = 1;
        return r.assumeCanonical;
    }
    else
    {
        alias Ret = typeof(return);
        auto structure = Ret._Structure.init;
        alias lengths = structure[0];
        foreach (i; Iota!M)
            lengths[i] = rlengths[i];

        /// Code size optimization
        immutable size_t eco = slice.elementCount;
        size_t ecn = lengths[0 .. rlengths.length].iota.elementCount;
        if (eco == 0)
        {
            err = ReshapeError.empty;
            goto R;
        }
        foreach (i; Iota!M)
            if (lengths[i] == -1)
            {
                ecn = -ecn;
                lengths[i] = eco / ecn;
                ecn *= lengths[i];
                break;
            }
        if (eco != ecn)
        {
            err = ReshapeError.total;
            goto R;
        }
        static if (kind == Universal)
        {
            for (size_t oi, ni, oj, nj; oi < N && ni < M; oi = oj, ni = nj)
            {
                size_t op = slice._lengths[oj++];
                size_t np =        lengths[nj++];

                for (;;)
                {
                    if (op < np)
                        op *= slice._lengths[oj++];
                    if (op > np)
                        np *=        lengths[nj++];
                    if (op == np)
                        break;
                }
                while (oj < N && slice._lengths[oj] == 1) oj++;
                while (nj < M        &&        lengths[nj] == 1) nj++;

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
                assert((oi == N) == (ni == M));

                structure[1][nj - 1] = slice._strides[oj - 1];
                foreach_reverse (i; ni .. nj - 1)
                    structure[1][i] = lengths[i + 1] * structure[1][i + 1];
            }
        }
        foreach (i; Iota!(M, Ret.N))
            lengths[i] = slice._lengths[i + N - M];
        static if (M < Ret.S)
        foreach (i; Iota!(M, Ret.S))
            structure[1][i] = slice._strides[i + N - M];
        err = 0;
        return Ret(structure, slice._iterator);
    R:
        return Ret(structure, slice._iterator.init);
    }
}

///
@safe nothrow pure
version(mir_test) unittest
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
@safe pure version(mir_test) unittest
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

    auto sl = iota!int(3, 4)
        .slice
        .universal
        .reversed!0;

    assert(reshape2(sl, [4, 3]) ==
        [[ 8, 9, 10],
         [11, 4,  5],
         [ 6, 7,  0],
         [ 1, 2,  3]]);
}

nothrow @safe pure version(mir_test) unittest
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
version(mir_test) unittest
{
    int err;
    assert(iota(3, 4, 5, 6, 7).pack!2.reshape([4, 3, 5], err)[0, 0, 0].shape == cast(size_t[2])[6, 7]);
    assert(err == 0);
}

nothrow @nogc @safe pure version(mir_test) unittest
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
version(mir_test) unittest
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
Slice!(FlattenedIterator!(Iterator, N, kind))
    flattened
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice)
    if (N != 1 && kind != Contiguous)
{
    size_t[typeof(return).N] lengths;
    sizediff_t[typeof(return)._iterator._indexes.length] indexes;
    lengths[0] = slice.elementCount;
    return typeof(return)(lengths, FlattenedIterator!(Iterator, N, kind)(indexes, slice));
}

/// ditto
Slice!Iterator
    flattened
    (Iterator, size_t N)
    (Slice!(Iterator, N) slice)
{
    static if (N == 1)
    {
        return slice;
    }
    else
    {
        import core.lifetime: move;
        size_t[typeof(return).N] lengths;
        lengths[0] = slice.elementCount;
        return typeof(return)(lengths, slice._iterator.move);
    }
}

/// ditto
Slice!(StrideIterator!Iterator)
    flattened
    (Iterator)
    (Slice!(Iterator,  1, Universal) slice)
{
    return slice.hideStride;
}

version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    auto sl1 = iota(2, 3).slice.universal.pack!1.flattened;
    auto sl2 = iota(2, 3).slice.canonical.pack!1.flattened;
    auto sl3 = iota(2, 3).slice.pack!1.flattened;
}

/// Regular slice
@safe @nogc pure nothrow version(mir_test) unittest
{
    assert(iota(4, 5).flattened == iota(20));
    assert(iota(4, 5).canonical.flattened == iota(20));
    assert(iota(4, 5).universal.flattened == iota(20));
}

@safe @nogc pure nothrow version(mir_test) unittest
{
    assert(iota(4).flattened == iota(4));
    assert(iota(4).canonical.flattened == iota(4));
    assert(iota(4).universal.flattened == iota(4));
}

/// Packed slice
@safe @nogc pure nothrow version(mir_test) unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.dynamic;
    assert(iota(3, 4, 5, 6, 7).pack!2.flattened[1] == iota([6, 7], 6 * 7));
}

/// Properties
@safe pure nothrow version(mir_test) unittest
{
    auto elems = iota(3, 4).universal.flattened;

    elems.popFrontExactly(2);
    assert(elems.front == 2);
    /// `_index` is available only for canonical and universal ndslices.
    assert(elems._iterator._indexes == [0, 2]);

    elems.popBackExactly(2);
    assert(elems.back == 9);
    assert(elems.length == 8);
}

/// Index property
@safe pure nothrow version(mir_test) unittest
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

@safe pure nothrow version(mir_test) unittest
{
    auto elems = iota(3, 4).universal.flattened;
    assert(elems.front == 0);
    assert(elems.save[1] == 1);
}

/++
Random access and slicing
+/
nothrow version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice : sliced;

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

@safe @nogc pure nothrow version(mir_test) unittest
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

@safe @nogc pure nothrow version(mir_test) unittest
{
    import std.range.primitives : isRandomAccessRange, hasSlicing;
    auto elems = iota(4, 5).flattened;
    static assert(isRandomAccessRange!(typeof(elems)));
    static assert(hasSlicing!(typeof(elems)));
}

// Checks strides
@safe @nogc pure nothrow version(mir_test) unittest
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

@safe @nogc pure nothrow version(mir_test) unittest
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

    assert(elems0.length == slice0.elementCount);
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
    elems0.popFrontExactly(slice0.elementCount - 14);
    assert(elems0.length == 13);
    assert(elems0 == range[slice0.elementCount - 13 .. slice0.elementCount]);

    foreach (elem; elems0) {}
}

// Issue 15549
version(mir_test) unittest
{
    import std.range.primitives;
    import mir.ndslice.allocation;
    alias A = typeof(iota(1, 2, 3, 4).pack!1);
    static assert(isRandomAccessRange!A);
    static assert(hasLength!A);
    static assert(hasSlicing!A);
    alias B = typeof(slice!int(1, 2, 3, 4).pack!3);
    static assert(isRandomAccessRange!B);
    static assert(hasLength!B);
    static assert(hasSlicing!B);
}

// Issue 16010
version(mir_test) unittest
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
Slice!(FieldIterator!(ndIotaField!N), N)
    ndiota
    (size_t N)
    (size_t[N] lengths...)
    if (N)
{
    return FieldIterator!(ndIotaField!N)(0, ndIotaField!N(lengths[1 .. $])).sliced(lengths);
}

///
@safe pure nothrow @nogc version(mir_test) unittest
{
    auto slice = ndiota(2, 3);
    static immutable array =
        [[[0, 0], [0, 1], [0, 2]],
         [[1, 0], [1, 1], [1, 2]]];

    assert(slice == array);
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto im = ndiota(7, 9);

    assert(im[2, 1] == [2, 1]);

    //slicing works correctly
    auto cm = im[1 .. $, 4 .. $];
    assert(cm[2, 1] == [3, 5]);
}

version(mir_test) unittest
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

// example from readme
version(mir_test) unittest
{
    import mir.ndslice;
    // import std.stdio: writefln;

    enum fmt = "%(%(%.2f %)\n%)\n";

    auto a = magic(5).as!float;
    // writefln(fmt, a);

    auto b = linspace!float([5, 5], [1f, 2f], [0f, 1f]).map!"a * a + b";
    // writefln(fmt, b);

    auto c = slice!float(5, 5);
    c[] = transposed(a + b / 2);
}

/// 1D
@safe pure nothrow
version(mir_test) unittest
{
    auto s = linspace!double([5], [1.0, 2.0]);
    assert(s == [1.0, 1.25, 1.5, 1.75, 2.0]);

    // reverse order
    assert(linspace!double([5], [2.0, 1.0]) == s.retro);

    // remove endpoint
    s.popBack;
    assert(s == [1.0, 1.25, 1.5, 1.75]);
}

/// 2D
@safe pure nothrow
version(mir_test) unittest
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
version(mir_test) unittest
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
Slice!(FieldIterator!(RepeatField!T), M, Universal)
    repeat(T, size_t M)(T value, size_t[M] lengths...) @trusted
    if (M && !isSlice!T)
{
    size_t[M] ls = lengths;
    return typeof(return)(
        ls,
        sizediff_t[M].init,
        typeof(return).Iterator(0, RepeatField!T(cast(RepeatField!T.UT) value)));
}

/// ditto
Slice!(SliceIterator!(Iterator, N, kind), M, Universal)
    repeat
    (SliceKind kind, size_t N, Iterator, size_t M)
    (Slice!(Iterator, N, kind) slice, size_t[M] lengths...)
    if (M)
{
    size_t[M] ls = lengths;
    return typeof(return)(
        ls,
        sizediff_t[M].init,
        typeof(return).Iterator(
            slice._structure,
            slice._iterator));
}

///
@safe pure nothrow
version(mir_test) unittest
{
    auto sl = iota(3).repeat(4);
    assert(sl == [[0, 1, 2],
                  [0, 1, 2],
                  [0, 1, 2],
                  [0, 1, 2]]);
}

///
@safe pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
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
@safe pure nothrow version(mir_test) unittest
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
Cycle repeates 1-dimensional field/range/array/slice in a fixed length 1-dimensional slice.
+/
auto cycle(Field)(Field field, size_t loopLength, size_t length)
    if (!isSlice!Field && !is(Field : T[], T))
{
    return CycleField!Field(loopLength, field).slicedField(length);
}

/// ditto
auto cycle(size_t loopLength, Field)(Field field, size_t length)
    if (!isSlice!Field && !is(Field : T[], T))
{
    static assert(loopLength);
    return CycleField!(Field, loopLength)(field).slicedField(length);
}

/// ditto
auto cycle(Iterator, SliceKind kind)(Slice!(Iterator, 1, kind) slice, size_t length)
{
    assert(slice.length);
    static if (kind == Universal)
        return slice.hideStride.cycle(length);
    else
        return CycleField!Iterator(slice._lengths[0], slice._iterator).slicedField(length);
}

/// ditto
auto cycle(size_t loopLength, Iterator, SliceKind kind)(Slice!(Iterator, 1, kind) slice, size_t length)
{
    static assert(loopLength);
    assert(loopLength <= slice.length);
    static if (kind == Universal)
        return slice.hideStride.cycle!loopLength(length);
    else
        return CycleField!(Iterator, loopLength)(slice._iterator).slicedField(length);
}

/// ditto
auto cycle(T)(T[] array, size_t length)
{
    return cycle(array.sliced, length);
}

/// ditto
auto cycle(size_t loopLength, T)(T[] array, size_t length)
{
    return cycle!loopLength(array.sliced, length);
}


/// ditto
auto cycle(size_t loopLength, T)(T withAsSlice, size_t length)
    if (hasAsSlice!T)
{
    return cycle!loopLength(withAsSlice.asSlice, length);
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto slice = iota(3);
    assert(slice.cycle(7) == [0, 1, 2, 0, 1, 2, 0]);
    assert(slice.cycle!2(7) == [0, 1, 0, 1, 0, 1, 0]);
    assert([0, 1, 2].cycle(7) == [0, 1, 2, 0, 1, 2, 0]);
    assert([4, 3, 2, 1].cycle!4(7) == [4, 3, 2, 1, 4, 3, 2]);
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
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice, ptrdiff_t factor)
    if (N == 1)
in
{
    assert (factor > 0, "factor must be positive.");
}
do
{
    static if (kind == Contiguous)
        return slice.universal.stride(factor);
    else
    {
        import mir.ndslice.dynamic: strided;
        return slice.strided!0(factor).hideStride;
    }
}

/// ditto
auto stride(T)(T[] array, ptrdiff_t factor)
{
    return stride(array.sliced, factor);
}

/// ditto
auto stride(T)(T withAsSlice, ptrdiff_t factor)
    if (hasAsSlice!T)
{
    return stride(withAsSlice.asSlice, factor);
}

///
@safe pure nothrow @nogc version(mir_test) unittest
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
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice)
    @trusted
{
    static if (kind == Contiguous || kind == Canonical)
    {
        size_t[slice.N] lengths;
        foreach (i; Iota!(slice.N))
            lengths[i] = slice._lengths[i];
        static if (slice.S)
        {
            sizediff_t[slice.S] strides;
            foreach (i; Iota!(slice.S))
                strides[i] = slice._strides[i];
            alias structure = AliasSeq!(lengths, strides);
        }
        else
        {
            alias structure = lengths;
        }
        static if (is(Iterator : RetroIterator!It, It))
        {
            alias Ret = Slice!(It, N, kind);
            return Ret(structure, slice._iterator._iterator - slice.lastIndex);
        }
        else
        {
            alias Ret = Slice!(RetroIterator!Iterator, N, kind);
            return Ret(structure, RetroIterator!Iterator(slice._iterator + slice.lastIndex));
        }
    }
    else
    {
        import mir.ndslice.dynamic: allReversed;
        return slice.allReversed;
    }
}

/// ditto
auto retro(T)(T[] array)
{
    return retro(array.sliced);
}

/// ditto
auto retro(T)(T withAsSlice)
    if (hasAsSlice!T)
{
    return retro(withAsSlice.asSlice);
}

///
@safe pure nothrow @nogc version(mir_test) unittest
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
    (Iterator, size_t N, SliceKind kind, I = typeof(Iterator.init[size_t.init]))
    (Slice!(Iterator, N, kind) slice)
    if (__traits(isIntegral, I) && (kind == Contiguous || kind == Canonical))
{
    static if (is(Iterator : FieldIterator!Field, Field))
    {
        enum simplified = true;
        alias It = FieldIterator!(BitField!Field);
    }
    else
    {
        enum simplified = false;
        alias It = FieldIterator!(BitField!Iterator);
    }
    alias Ret = Slice!(It, N, kind);
    auto structure_ = Ret._Structure.init;
    foreach(i; Iota!(Ret.N))
        structure_[0][i] = slice._lengths[i];
    structure_[0][$ - 1] *= I.sizeof * 8;
    foreach(i; Iota!(Ret.S))
        structure_[1][i] = slice._strides[i];
    static if (simplified)
        return Ret(structure_, It(slice._iterator._index * I.sizeof * 8, BitField!Field(slice._iterator._field)));
    else
        return Ret(structure_, It(0, BitField!Iterator(slice._iterator)));
}

/// ditto
auto bitwise(T)(T[] array)
{
    return bitwise(array.sliced);
}

/// ditto
auto bitwise(T)(T withAsSlice)
    if (hasAsSlice!T)
{
    return bitwise(withAsSlice.asSlice);
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    size_t[10] data;
    auto bits = data[].bitwise;
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
version(mir_test) unittest
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
Bitwise field over an integral field.
Params:
    field = an integral field.
Returns: A bitwise field.
+/
auto bitwiseField(Field, I = typeof(Field.init[size_t.init]))(Field field)
    if (__traits(isUnsigned, I))
{
    return BitField!(Field, I)(field);
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
    (size_t pack, Iterator, size_t N, SliceKind kind, I = typeof(Iterator.init[size_t.init]))
    (Slice!(Iterator, N, kind) slice)
    if (__traits(isIntegral, I) && (kind == Contiguous || kind == Canonical) && pack > 1)
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
    alias Ret = Slice!(It, N, kind);
    auto structure = Ret._Structure.init;
    foreach(i; Iota!(Ret.N))
        structure[0][i] = slice._lengths[i];
    structure[0][$ - 1] *= I.sizeof * 8;
    structure[0][$ - 1] /= pack;
    foreach(i; Iota!(Ret.S))
        structure[1][i] = slice._strides[i];
    static if (simplified)
        return Ret(structure, It(slice._iterator._index * I.sizeof * 8 / pack, BitpackField!(Field, pack)(slice._iterator._field)));
    else
        return Ret(structure, It(0, BitpackField!(Iterator, pack)(slice._iterator)));
}

/// ditto
auto bitpack(size_t pack, T)(T[] array)
{
    return bitpack!pack(array.sliced);
}

/// ditto
auto bitpack(size_t pack, T)(T withAsSlice)
    if (hasAsSlice!T)
{
    return bitpack!pack(withAsSlice.asSlice);
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    size_t[10] data;
    // creates a packed unsigned integer slice with max allowed value equal to `2^^6 - 1 == 63`.
    auto packs = data[].bitpack!6;
    assert(packs.length == data.length * size_t.sizeof * 8 / 6);
    packs[$ - 1] = 24;
    assert(packs[$ - 1] == 24);

    packs.popFront;
    assert(packs[$ - 1] == 24);
}

/++
Bytegroup slice over an integral slice.

Groups existing slice into fixed length chunks and uses them as data store for destination type.

Correctly handles scalar types on both little-endian and big-endian platforms.

Params:
    group = count of iterator items used to store the destination type.
    DestinationType = deep element type of the result slice.
    slice = a contiguous or canonical slice.
Returns: A bytegroup slice.
+/
Slice!(BytegroupIterator!(Iterator, group, DestinationType), N, kind)
bytegroup
    (size_t group, DestinationType, Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice)
    if ((kind == Contiguous || kind == Canonical) && group)
{
    auto structure = slice._structure;
    structure[0][$ - 1] /= group;
    return typeof(return)(structure, BytegroupIterator!(Iterator, group, DestinationType)(slice._iterator));
}


/// ditto
auto bytegroup(size_t pack, DestinationType, T)(T[] array)
{
    return bytegroup!(pack, DestinationType)(array.sliced);
}

/// ditto
auto bytegroup(size_t pack, DestinationType, T)(T withAsSlice)
    if (hasAsSlice!T)
{
    return bytegroup!(pack, DestinationType)(withAsSlice.asSlice);
}

/// 24 bit integers
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.slice : DeepElementType, sliced;

    ubyte[20] data;
    // creates a packed unsigned integer slice with max allowed value equal to `2^^6 - 1 == 63`.
    auto int24ar = data[].bytegroup!(3, int); // 24 bit integers
    assert(int24ar.length == data.length / 3);

    enum checkInt = ((1 << 20) - 1);

    int24ar[3] = checkInt;
    assert(int24ar[3] == checkInt);

    int24ar.popFront;
    assert(int24ar[2] == checkInt);

    static assert(is(DeepElementType!(typeof(int24ar)) == int));
}

/// 48 bit integers
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.slice : DeepElementType, sliced;
    ushort[20] data;
    // creates a packed unsigned integer slice with max allowed value equal to `2^^6 - 1 == 63`.
    auto int48ar = data[].sliced.bytegroup!(3, long); // 48 bit integers
    assert(int48ar.length == data.length / 3);

    enum checkInt = ((1L << 44) - 1);

    int48ar[3] = checkInt;
    assert(int48ar[3] == checkInt);

    int48ar.popFront;
    assert(int48ar[2] == checkInt);

    static assert(is(DeepElementType!(typeof(int48ar)) == long));
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
    $(LREF cached), $(LREF vmap), $(LREF indexed),
    $(LREF pairwise), $(LREF subSlices), $(LREF slide), $(LREF zip),
    $(HTTP en.wikipedia.org/wiki/Map_(higher-order_function), Map (higher-order function))
+/
template map(fun...)
    if (fun.length)
{
    import mir.functional: adjoin, naryFun, pipe;
    static if (fun.length == 1)
    {
        static if (__traits(isSame, naryFun!(fun[0]), fun[0]) && !__traits(isSame, naryFun!"a", fun[0]))
        {
            alias f = fun[0];
        @optmath:
            /++
            Params:
                slice = An input slice.
            Returns:
                a slice with each fun applied to all the elements. If there is more than one
                fun, the element type will be `Tuple` containing one element for each fun.
            +/
            auto map(Iterator, size_t N, SliceKind kind)
                (Slice!(Iterator, N, kind) slice)
            {
                alias Iterator = typeof(_mapIterator!f(slice._iterator));
                import mir.ndslice.traits: isIterator;
                static assert(isIterator!Iterator, "mir.ndslice.map: probably the lambda function contains a compile time bug.");
                return Slice!(Iterator, N, kind)(slice._structure, _mapIterator!f(slice._iterator));
            }

            /// ditto
            auto map(T)(T[] array)
            {
                return map(array.sliced);
            }

            /// ditto
            auto map(T)(T withAsSlice)
                if (hasAsSlice!T)
            {
                return map(withAsSlice.asSlice);
            }
        }
        else
        static if (__traits(isSame, naryFun!"a", fun[0]))
        {
            ///
            @optmath auto map(Iterator, size_t N, SliceKind kind)
                (Slice!(Iterator, N, kind) slice)
            {
                return slice;
            }

            /// ditto
            auto map(T)(T[] array)
            {
                return array.sliced;
            }

            /// ditto
            auto map(T)(T withAsSlice)
                if (hasAsSlice!T)
            {
                return withAsSlice.asSlice;
            }
        }
        else alias map = .map!(naryFun!fun);
    }
    else alias map = .map!(adjoin!fun);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    auto s = iota(2, 3).map!(a => a * 3);
    assert(s == [[ 0,  3,  6],
                 [ 9, 12, 15]]);
}

/// String lambdas
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    assert(iota(2, 3).map!"a * 2" == [[0, 2, 4], [6, 8, 10]]);
}

/// Packed tensors.
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota, windows;
    import mir.math.sum: sum;

    //  iota        windows     map  sums ( reduce!"a + b" )
    //                --------------
    //  -------      |  ---    ---  |      ------
    // | 0 1 2 |  => || 0 1 || 1 2 ||  => | 8 12 |
    // | 3 4 5 |     || 3 4 || 4 5 ||      ------
    //  -------      |  ---    ---  |
    //                --------------
    auto s = iota(2, 3)
        .windows(2, 2)
        .map!sum;

    assert(s == [[8, 12]]);
}

/// Zipped tensors
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    auto z = zip(sl1, sl2);

    assert(zip(sl1, sl2).map!"a + b" == sl1 + sl2);
}

/++
Multiple functions can be passed to `map`.
In that case, the element type of `map` is a refTuple containing
one element for each function.
+/
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    auto sl = iota(2, 3);
    auto s = sl.map!("a + a", "a * a");

    auto sums     = [[0, 2, 4], [6,  8, 10]];
    auto products = [[0, 1, 4], [9, 16, 25]];

    assert(s.map!"a[0]" == sl + sl);
    assert(s.map!"a[1]" == sl * sl);
}

/++
`map` can be aliased to a symbol and be used separately:
+/
pure nothrow version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    alias halfs = map!"double(a) / 2";
    assert(halfs(iota(2, 3)) == [[0.0, 0.5, 1], [1.5, 2, 2.5]]);
}

/++
Type normalization
+/
version(mir_test) unittest
{
    import mir.functional : pipe;
    import mir.ndslice.topology : iota;
    auto a = iota(2, 3).map!"a + 10".map!(pipe!("a * 2", "a + 1"));
    auto b = iota(2, 3).map!(pipe!("a + 10", "a * 2", "a + 1"));
    assert(a == b);
    static assert(is(typeof(a) == typeof(b)));
}

///
pure version(mir_test) unittest
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


/++
Implements the homonym function (also known as `transform`) present
in many languages of functional flavor. The call `slice.vmap(fun)`
returns a slice of which elements are obtained by applying `fun`
for all elements in `slice`. The original slices are
not changed. Evaluation is done lazily.

Note:
    $(SUBREF dynamic, transposed) and
    $(SUBREF topology, pack) can be used to specify dimensions.
Params:
    slice = ndslice
    callable = callable object, structure, delegate, or function pointer.
See_Also:
    $(LREF cached), $(LREF map), $(LREF indexed),
    $(LREF pairwise), $(LREF subSlices), $(LREF slide), $(LREF zip),
    $(HTTP en.wikipedia.org/wiki/Map_(higher-order_function), Map (higher-order function))
+/
@optmath auto vmap(Iterator, size_t N, SliceKind kind, Callable)
    (
        Slice!(Iterator, N, kind) slice,
        Callable callable,
    )
{
    alias It = VmapIterator!(Iterator, Callable);
    return Slice!(It, N, kind)(slice._structure, It(slice._iterator, callable));
}

/// ditto
auto vmap(T, Callable)(T[] array, Callable callable)
{
    return vmap(array.sliced, callable);
}

/// ditto
auto vmap(T, Callable)(T withAsSlice, Callable callable)
    if (hasAsSlice!T)
{
    return vmap(withAsSlice.asSlice, callable);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    static struct Mul {
        double factor; this(double f) { factor = f; }
        auto opCall(long x) const {return x * factor; }
        auto lightConst()() const @property { return Mul(factor); }
    }

    auto callable = Mul(3);
    auto s = iota(2, 3).vmap(callable);

    assert(s == [[ 0,  3,  6],
                 [ 9, 12, 15]]);
}

/// Packed tensors.
@safe pure nothrow
version(mir_test) unittest
{
    import mir.math.sum: sum;
    import mir.ndslice.topology : iota, windows;

    //  iota        windows     vmap  scaled sums
    //                --------------
    //  -------      |  ---    ---  |      -----
    // | 0 1 2 |  => || 0 1 || 1 2 ||  => | 4 6 |
    // | 3 4 5 |     || 3 4 || 4 5 ||      -----
    //  -------      |  ---    ---  |
    //                --------------

    struct Callable
    {
        double factor;
        this(double f) {factor = f;}
        auto opCall(S)(S x) { return x.sum * factor; }

        auto lightConst()() const @property { return Callable(factor); }
        auto lightImmutable()() immutable @property { return Callable(factor); }
    }

    auto callable = Callable(0.5);

    auto s = iota(2, 3)
        .windows(2, 2)
        .vmap(callable);

    assert(s == [[4, 6]]);
}

/// Zipped tensors
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota, zip;

    struct Callable
    {
        double factor;
        this(double f) {factor = f;}
        auto opCall(S, T)(S x, T y) { return x + y * factor; }

        auto lightConst()() const { return Callable(factor); }
        auto lightImmutable()() immutable { return Callable(factor); }
    }

    auto callable = Callable(10);

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    auto z = zip(sl1, sl2);

    assert(zip(sl1, sl2).vmap(callable) ==
            [[10,  21,  32],
             [43,  54,  65]]);
}

// TODO
/+
Multiple functions can be passed to `vmap`.
In that case, the element type of `vmap` is a refTuple containing
one element for each function.
+/
@safe pure nothrow
version(none) version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    auto s = iota(2, 3).vmap!("a + a", "a * a");

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

private auto hideStride
    (Iterator, SliceKind kind)
    (Slice!(Iterator, 1, kind) slice)
{
    static if (kind == Universal)
        return Slice!(StrideIterator!Iterator)(
            slice._lengths,
            StrideIterator!Iterator(slice._strides[0], slice._iterator));
    else
        return slice;
}

private auto unhideStride
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, N, kind) slice)
{
    static if (is(Iterator : StrideIterator!It, It))
    {
        static if (kind == Universal)
        {
            alias Ret = SliceKind!(It, N, Universal);
            auto strides = slice._strides;
            foreach(i; Iota!(Ret.S))
                strides[i] = slice._strides[i] * slice._iterator._stride;
            return Slice!(It, N, Universal)(slice._lengths, strides, slice._iterator._iterator);
        }
        else
            return slice.universal.unhideStride;
    }
    else
        return slice;
}

/++
Creates a random access cache for lazyly computed elements.
Params:
    original = original ndslice
    caches = cached values
    flags = array composed of flags that indicates if values are already computed
Returns:
    ndslice, which is internally composed of three ndslices: `original`, allocated cache and allocated bit-ndslice.
See_also: $(LREF cachedGC), $(LREF map), $(LREF vmap), $(LREF indexed)
+/
Slice!(CachedIterator!(Iterator, CacheIterator, FlagIterator), N, kind)
    cached(Iterator, SliceKind kind, size_t N, CacheIterator, FlagIterator)(
        Slice!(Iterator, N, kind) original,
        Slice!(CacheIterator, N, kind) caches,
        Slice!(FlagIterator, N, kind) flags,
    )
{
    assert(original.shape == caches.shape, "caches.shape should be equal to original.shape");
    assert(original.shape == flags.shape, "flags.shape should be equal to original.shape");
    return typeof(return)(
        original._structure,
        IteratorOf!(typeof(return))(
            original._iterator,
            caches._iterator,
            flags._iterator,
        ));
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology: cached, iota, map;
    import mir.ndslice.allocation: bitSlice, uninitSlice;

    int[] funCalls;

    auto v = 5.iota!int
        .map!((i) {
            funCalls ~= i;
            return 2 ^^ i;
        });
    auto flags = v.length.bitSlice;
    auto cache = v.length.uninitSlice!int;
    // cached lazy slice: 1 2 4 8 16
    auto sl = v.cached(cache, flags);

    assert(funCalls == []);
    assert(sl[1] == 2); // remember result
    assert(funCalls == [1]);
    assert(sl[1] == 2); // reuse result
    assert(funCalls == [1]);

    assert(sl[0] == 1);
    assert(funCalls == [1, 0]);
    funCalls = [];

    // set values directly
    sl[1 .. 3] = 5;
    assert(sl[1] == 5);
    assert(sl[2] == 5);
    // no function calls
    assert(funCalls == []);
}

/// Cache of immutable elements
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.slice: DeepElementType;
    import mir.ndslice.topology: cached, iota, map, as;
    import mir.ndslice.allocation: bitSlice, uninitSlice;

    int[] funCalls;

    auto v = 5.iota!int
        .map!((i) {
            funCalls ~= i;
            return 2 ^^ i;
        })
        .as!(immutable int);
    auto flags = v.length.bitSlice;
    auto cache = v.length.uninitSlice!(immutable int);

    // cached lazy slice: 1 2 4 8 16
    auto sl = v.cached(cache, flags);

    static assert(is(DeepElementType!(typeof(sl)) == immutable int));

    assert(funCalls == []);
    assert(sl[1] == 2); // remember result
    assert(funCalls == [1]);
    assert(sl[1] == 2); // reuse result
    assert(funCalls == [1]);

    assert(sl[0] == 1);
    assert(funCalls == [1, 0]);
}

/++
Creates a random access cache for lazyly computed elements.
Params:
    original = ND Contiguous or 1D Universal ndslice.
Returns:
    ndslice, which is internally composed of three ndslices: `original`, allocated cache and allocated bit-ndslice.
See_also: $(LREF cached), $(LREF map), $(LREF vmap), $(LREF indexed)
+/
Slice!(CachedIterator!(Iterator, typeof(Iterator.init[0])*, FieldIterator!(BitField!(size_t*))), N)
    cachedGC(Iterator, size_t N)(Slice!(Iterator, N) original) @trusted
{
    import std.traits: hasElaborateAssign, Unqual;
    import mir.ndslice.allocation: bitSlice, slice, uninitSlice;
    alias C = typeof(Iterator.init[0]);
    alias UC = Unqual!C;
    static if (hasElaborateAssign!UC)
        alias newSlice = slice;
    else
        alias newSlice = uninitSlice;
    return typeof(return)(
        original._structure,
        IteratorOf!(typeof(return))(
            original._iterator,
            newSlice!C(original._lengths)._iterator,
            original._lengths.bitSlice._iterator,
            ));
}

/// ditto
auto cachedGC(Iterator)(Slice!(Iterator,  1, Universal) from)
{
    return from.flattened.cachedGC;
}

/// ditto
auto cachedGC(T)(T withAsSlice)
    if (hasAsSlice!T)
{
    return cachedGC(withAsSlice.asSlice);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology: cachedGC, iota, map;

    int[] funCalls;

    // cached lazy slice: 1 2 4 8 16
    auto sl = 5.iota!int
        .map!((i) {
            funCalls ~= i;
            return 2 ^^ i;
        })
        .cachedGC;

    assert(funCalls == []);
    assert(sl[1] == 2); // remember result
    assert(funCalls == [1]);
    assert(sl[1] == 2); // reuse result
    assert(funCalls == [1]);

    assert(sl[0] == 1);
    assert(funCalls == [1, 0]);
    funCalls = [];

    // set values directly
    sl[1 .. 3] = 5;
    assert(sl[1] == 5);
    assert(sl[2] == 5);
    // no function calls
    assert(funCalls == []);
}

/// Cache of immutable elements
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.slice: DeepElementType;
    import mir.ndslice.topology: cachedGC, iota, map, as;

    int[] funCalls;

    // cached lazy slice: 1 2 4 8 16
    auto sl = 5.iota!int
        .map!((i) {
            funCalls ~= i;
            return 2 ^^ i;
        })
        .as!(immutable int)
        .cachedGC;

    static assert(is(DeepElementType!(typeof(sl)) == immutable int));

    assert(funCalls == []);
    assert(sl[1] == 2); // remember result
    assert(funCalls == [1]);
    assert(sl[1] == 2); // reuse result
    assert(funCalls == [1]);

    assert(sl[0] == 1);
    assert(funCalls == [1, 0]);
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
See_also: $(LREF map), $(LREF vmap)
+/
template as(T)
{
    ///
    @optmath auto as(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        static if (is(slice.DeepElement == T))
            return slice;
        else
        static if (is(Iterator : T*))
            return slice.toConst;
        else
        {
            import mir.conv: to;
            return map!(to!T)(slice);
        }
    }

    /// ditto
    auto as(S)(S[] array)
    {
        return as(array.sliced);
    }

    /// ditto
    auto as(S)(S withAsSlice)
        if (hasAsSlice!S)
    {
        return as(withAsSlice.asSlice);
    }
}

///
@safe pure nothrow version(mir_test) unittest
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
    Slice!(int*, 2) stringMatrix = stringMatrixView.slice;
}

/// Special behavior for pointers to a constant data.
@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.slice : Contiguous, Slice;

    Slice!(double*, 2)              matrix = slice!double([2, 2], 0);
    Slice!(const(double)*, 2) const_matrix = matrix.as!(const double);
}

/++
Takes a field `source` and a slice `indexes`, and creates a view of source as if its elements were reordered according to indexes.
`indexes` may include only a subset of the elements of `source` and may also repeat elements.

Params:
    source = a filed, source of data. `source` must be an array or a pointer, or have `opIndex` primitive. Full random access range API is not required.
    indexes = a slice, source of indexes.
Returns:
    n-dimensional slice with the same kind, shape and strides.

See_also: `indexed` is similar to $(LREF, vmap), but a field (`[]`) is used instead of a function (`()`), and order of arguments is reversed.
+/
Slice!(IndexIterator!(Iterator, Field), N, kind)
    indexed(Field, Iterator, size_t N, SliceKind kind)
    (Field source, Slice!(Iterator, N, kind) indexes)
{
    return typeof(return)(
            indexes._structure,
            IndexIterator!(Iterator, Field)(
                indexes._iterator,
                source));
}

/// ditto
auto indexed(Field, S)(Field source, S[] indexes)
{
    return indexed(source, indexes.sliced);
}

/// ditto
auto indexed(Field, S)(Field source, S indexes)
    if (hasAsSlice!S)
{
    return indexed(source, indexes.asSlice);
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto source = [1, 2, 3, 4, 5];
    auto indexes = [4, 3, 1, 2, 0, 4];
    auto ind = source.indexed(indexes);
    assert(ind == [5, 4, 2, 3, 1, 5]);

    assert(ind.retro == source.indexed(indexes.retro));

    ind[3] += 10; // for index 2
    //                0  1   2  3  4
    assert(source == [1, 2, 13, 4, 5]);
}

/++
Maps indexes pairs to subslices.
Params:
    sliceable = pointer, array, ndslice, series, or something sliceable with `[a .. b]`.
    slices = ndslice composed of indexes pairs.
Returns:
    ndslice composed of subslices.
See_also: $(LREF chopped), $(LREF pairwise).
+/
Slice!(SubSliceIterator!(Iterator, Sliceable), N, kind)
    subSlices(Iterator, size_t N, SliceKind kind, Sliceable)(
        Sliceable sliceable,
        Slice!(Iterator, N, kind) slices,
    )
{
    return typeof(return)(
        slices._structure,
        SubSliceIterator!(Iterator, Sliceable)(slices._iterator, sliceable)
    );
}

/// ditto
auto subSlices(S, Sliceable)(Sliceable sliceable, S[] slices)
{
    return subSlices(sliceable, slices.sliced);
}

/// ditto
auto subSlices(S, Sliceable)(Sliceable sliceable, S slices)
    if (hasAsSlice!S)
{
    return subSlices(sliceable, slices.asSlice);
}

///
@safe pure version(mir_test) unittest
{
    import mir.functional: staticArray;
    auto subs =[
            staticArray(2, 4),
            staticArray(2, 10),
        ];
    auto sliceable = 10.iota;

    auto r = sliceable.subSlices(subs);
    assert(r == [
        iota([4 - 2], 2),
        iota([10 - 2], 2),
        ]);
}

/++
Maps indexes pairs to subslices.
Params:
    bounds = ndslice composed of consequent (`a_i <= a_(i+1)`) pairwise index bounds.
    sliceable = pointer, array, ndslice, series, or something sliceable with `[a_i .. a_(i+1)]`.
Returns:
    ndslice composed of subslices.
See_also: $(LREF pairwise), $(LREF subSlices).
+/
Slice!(ChopIterator!(Iterator, Sliceable)) chopped(Iterator, Sliceable)(
        Sliceable sliceable,
        Slice!Iterator bounds,
    )
in
{
    debug(mir)
        foreach(b; bounds.pairwise!"a <= b")
            assert(b);
}
do {
    import core.lifetime: move;
    sizediff_t length = bounds._lengths[0] <= 1 ? 0 : bounds._lengths[0] - 1;
    static if (hasLength!Sliceable)
    {
        if (length && bounds[length - 1] > sliceable.length)
        {
            version (D_Exceptions)
                throw choppedException;
            else
               assert(0, choppedExceptionMsg);
        }
    }

    return typeof(return)([size_t(length)], ChopIterator!(Iterator, Sliceable)(bounds._iterator.move, sliceable.move));
}

/// ditto
auto chopped(S, Sliceable)(Sliceable sliceable, S[] bounds)
{
    return chopped(sliceable, bounds.sliced);
}

/// ditto
auto chopped(S, Sliceable)(Sliceable sliceable, S bounds)
    if (hasAsSlice!S)
{
    return chopped(sliceable, bounds.asSlice);
}

///
@safe pure version(mir_test) unittest
{
    import mir.functional: staticArray;
    import mir.ndslice.slice : sliced;
    auto pairwiseIndexes = [2, 4, 10].sliced;
    auto sliceable = 10.iota;

    auto r = sliceable.chopped(pairwiseIndexes);
    assert(r == [
        iota([4 - 2], 2),
        iota([10 - 4], 4),
        ]);
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
    if (Slices.length > 1 && allSatisfy!(isConvertibleToSlice, Slices))
{
    static if (allSatisfy!(isSlice, Slices))
    {
        enum N = Slices[0].N;
        foreach(i, S; Slices[1 .. $])
        {
            static assert(S.N == N, "zip: all Slices must have the same dimension count");
            assert(slices[i + 1]._lengths == slices[0]._lengths, "zip: all slices must have the same lengths");
            static if (sameStrides)
                assert(slices[i + 1].strides == slices[0].strides, "zip: all slices must have the same strides when unpacked");
        }
        static if (!sameStrides && minElem(staticMap!(kindOf, Slices)) != Contiguous)
        {
            static assert(N == 1, "zip: cannot zip canonical and universal multidimensional slices if `sameStrides` is false");
            mixin(`return .zip(` ~ _iotaArgs!(Slices.length, "slices[", "].hideStride, ") ~`);`);
        }
        else
        {
            enum kind = maxElem(staticMap!(kindOf, Slices));
            alias Iterator = ZipIterator!(staticMap!(_IteratorOf, Slices));
            alias Ret = Slice!(Iterator, N, kind);
            auto structure = Ret._Structure.init;
            structure[0] = slices[0]._lengths;
            foreach (i; Iota!(Ret.S))
                structure[1][i] = slices[0]._strides[i];
            return Ret(structure, mixin("Iterator(" ~ _iotaArgs!(Slices.length, "slices[", "]._iterator, ") ~ ")"));
        }
    }
    else
    {
        return .zip(toSlices!slices);
    }
}

///
@safe pure nothrow version(mir_test) unittest
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

@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : flattened, iota;

    auto alpha = iota!int(4).universal;
    auto beta = new int[4];

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
    (char name, size_t N, SliceKind kind, Iterators...)
    (Slice!(ZipIterator!Iterators, N, kind) slice)
{
    enum size_t i = name - 'a';
    static assert(i < Iterators.length, `unzip: constraint: size_t(name - 'a') < Iterators.length`);
    return Slice!(Iterators[i], N, kind)(slice._structure, slice._iterator._iterators[i]).unhideStride;
}

///
pure nothrow version(mir_test) unittest
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
Works with packed slices.

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

    static if (params > 1 && __traits(isSame, naryFun!fun, fun))
    {
    @optmath:
        /++
        Params:
            slice = An input slice with first dimension pack equals to one (e.g. 1-dimensional for not packed slices).
        Returns:
            1d-slice composed of `fun(slice[i], ..., slice[i + params - 1])`.
        +/
        auto slide(Iterator, size_t N, SliceKind kind)
            (Slice!(Iterator, N, kind) slice)
            if (N == 1)
        {
            auto s = slice.map!"a".flattened;
            if (cast(sizediff_t)s._lengths[0] < sizediff_t(params - 1))
                s._lengths[0] = 0;
            else
                s._lengths[0] -= params - 1;

            alias I = SlideIterator!(_IteratorOf!(typeof(s)), params, fun);
            return Slice!(I)(
                s._structure,
                I(s._iterator));
        }

        /// ditto
        auto slide(S)(S[] slice)
        {
            return slide(slice.sliced);
        }

        /// ditto
        auto slide(S)(S slice)
            if (hasAsSlice!S)
        {
            return slide(slice.asSlice);
        }
    }
    else
    static if (params == 1)
        alias slide = .map!(naryFun!fun);
    else alias slide = .slide!(params, naryFun!fun);
}

///
version(mir_test) unittest
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
Works with packed slices.

Params:
    fun = function to accumulate
    lag = an integer indicating which lag to use
Returns: lazy ndslice composed of `fun(a_n, a_n+1)` values.

See_also: $(LREF slide), $(LREF subSlices).
+/
alias pairwise(alias fun, size_t lag = 1) = slide!(lag + 1, fun);

///
version(mir_test) unittest
{
    assert([2, 4, 3, -1].sliced.pairwise!"a + b" == [6, 7, 2]);
}

/++
Differences between vector elements.
Works with packed slices.

Params:
    lag = an integer indicating which lag to use
Returns: lazy differences.

See_also: $(LREF slide), $(LREF slide).
+/
alias diff(size_t lag = 1) = pairwise!(('a' + lag) ~ " - a", lag);

///
version(mir_test) unittest
{
    assert([2, 4, 3, -1].sliced.diff == [2, -1, -4]);
}

/// packed slices
version(mir_test) unittest
{
    // 0 1  2  3
    // 4 5  6  7
    // 8 9 10 11
    auto s = iota(3, 4);
    import std.stdio;
    assert(iota(3, 4).byDim!0.diff == [
        [4, 4, 4, 4],
        [4, 4, 4, 4]]);
    assert(iota(3, 4).byDim!1.diff == [
        [1, 1, 1],
        [1, 1, 1],
        [1, 1, 1]]);
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
version(mir_test) unittest
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
version(mir_test) unittest
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
version(mir_test) unittest
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
    @optmath auto kronecker(NdFields...)(NdFields fields)
        if (allSatisfy!(hasShape, NdFields) || allSatisfy!(hasLength, NdFields))
    {
        return Kronecker!(fun, NdFields)(fields).slicedNdField;
    }
    else
        alias kronecker = .kronecker!(naryFun!fun);
}

/// 2D
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice : sliced;

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
version(mir_test) unittest
{
    auto a = iota([3], 1);

    auto b = [ 1, -1];

    auto c = kronecker(a, b);

    assert(c == [1, -1, 2, -2, 3, -3]);
}

/// 2D with 3 arguments
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice : sliced;

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
    return MagicField(length).slicedField(length, length);
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.math.sum;
    import mir.ndslice: slice, magic, byDim, map, as, repeat, diagonal, antidiagonal;

    bool isMagic(S)(S matrix)
    {
        auto n = matrix.length;
        auto c = n * (n * n + 1) / 2; // magic number
        return // check shape
            matrix.length!0 > 0 && matrix.length!0 == matrix.length!1
            && // each row sum should equal magic number
            matrix.byDim!0.map!sum == c.repeat(n)
            && // each columns sum should equal magic number
            matrix.byDim!1.map!sum == c.repeat(n)
            && // diagonal sum should equal magic number
            matrix.diagonal.sum == c
            && // antidiagonal sum should equal magic number
            matrix.antidiagonal.sum == c;
    }

    assert(isMagic(magic(1)));
    assert(!isMagic(magic(2))); // 2x2 magic square does not exist
    foreach(n; 3 .. 24)
        assert(isMagic(magic(n)));
    assert(isMagic(magic(3).as!double.slice));
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

See_also: $(LREF triplets) $(LREF ._stairs.2)
+/
Slice!(StairsIterator!(Iterator, type)) stairs(string type, Iterator)(Slice!Iterator slice, size_t n)
    if (type == "+" || type == "-")
{
    assert(slice.length == (n + 1) * n / 2, "stairs: slice length must be equal to n * (n + 1) / 2, where n is stairs count.");
    static if (type == "+")
        size_t length = 1;
    else
        size_t length = n;
    return StairsIterator!(Iterator, type)(length, slice._iterator).sliced(n);
}

/// ditto
Slice!(StairsIterator!(S*, type))  stairs(string type, S)(S[] slice, size_t n)
    if (type == "+" || type == "-")
{
    return stairs!type(slice.sliced, n);
}

/// ditto
auto stairs(string type, S)(S slice, size_t n)
    if (hasAsSlice!S && (type == "+" || type == "-"))
{
    return stairs!type(slice.asSlice, n);
}

///
version(mir_test) unittest
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
    assert(inc[1 .. $][2] == [6, 7, 8, 9]);

    assert(dec == [
        [0, 1, 2, 3, 4],
           [5, 6, 7, 8],
            [9, 10, 11],
               [12, 13],
                   [14]]);
    assert(dec[1 .. $][2] == [12, 13]);

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
auto stairs(string type, Iterator, SliceKind kind)(Slice!(Iterator, 2, kind) slice)
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
version(mir_test) unittest
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
    import mir.algorithm.iteration: each;
    each!"a[] = b"(lower, inc);
    each!"a[] = b"(upper, dec);

    assert(&lower[0][0] is &lowerData[0]);
    assert(&upper[0][0] is &upperData[0]);

    assert(lowerData == [0, 3, 4, 6, 7, 8]);
    assert(upperData == [0, 1, 2, 4, 5, 8]);
}

/++
Returns a slice that can be iterated by dimension. Transposes dimensions on top and then packs them.

Combines $(LREF transposed) and $(LREF ipack).

Params:
    Dimensions = dimensions to perform iteration on
Returns:
    n-dimensional slice ipacked to allow iteration by dimension
See_also:
    $(LREF slice),
    $(LREF ipack),
    $(LREF transposed).
+/
template byDim(Dimensions...)
    if (Dimensions.length > 0)
{
    import mir.ndslice.internal : isSize_t;
    import std.meta : allSatisfy;

    static if (!allSatisfy!(isSize_t, Dimensions))
    {
        import std.meta : staticMap;
        import mir.ndslice.internal : toSize_t;

        alias byDim = .byDim!(staticMap!(toSize_t, Dimensions));
    }
    else
    {
        import mir.ndslice.slice : Slice, SliceKind;
        /++
        Params:
            slice = input slice (may not be 1-dimensional slice)
        Returns:
            n-dimensional slice ipacked to allow iteration by dimension
        +/
        @optmath auto byDim(Iterator, size_t N, SliceKind kind)
                                       (Slice!(Iterator, N, kind) slice)
        {
            import mir.ndslice.topology : ipack;
            import mir.ndslice.internal : DimensionsCountCTError;

            mixin DimensionsCountCTError;

            static if (N == 1)
            {
                return slice;
            }
            else
            {
                import mir.ndslice.dynamic: transposed;
                return slice
                            .transposed!Dimensions
                            .ipack!(Dimensions.length);
            }
        }
    }
}

/// 2-dimensional slice support
@safe @nogc pure nothrow
version(mir_test) unittest
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
    auto x = slice.byDim!0;
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
version(mir_test) unittest
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
    // | 5 4 |
    //->
    // | 3 |
    //->
    // | 4 |
    //->
    // | 5 |
    size_t[2] shape45 = [4, 5];
    size_t[2] shape35 = [3, 5];
    size_t[2] shape34 = [3, 4];
    size_t[2] shape54 = [5, 4];
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
    auto x = slice.byDim!0;
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
    assert(a.shape == shape54);
    assert(a.front.shape == shape4);
    assert(a.front.unpack == iota([3, 4], 0, 5).universal.transposed!1);
    a.popFront;
    assert(a.front.front == iota([3], 1, 20));
}

// Ensure works on canonical
@safe @nogc pure nothrow
version(mir_test) unittest
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
    auto x = slice.byDim!0;
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
version(mir_test) unittest
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
    auto x = slice.byDim!0;
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
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    //  -------
    // | 0 1 2 |
    //  -------
    auto slice = iota(3);
    auto x = slice.byDim!0;
    assert(x == slice);
}

/++
Field (element's member) projection.

Params:
    name = element's member name
Returns:
    lazy n-dimensional slice of the same shape
See_also:
    $(LREF map)
+/

template member(string name)
    if (name.length)
{
    /++
    Params:
        slice = n-dimensional slice composed of structs, classes or unions
    Returns:
        lazy n-dimensional slice of the same shape
    +/
    Slice!(MemberIterator!(Iterator, name), N, kind) member(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        return typeof(return)(slice._structure, MemberIterator!(Iterator, name)(slice._iterator));
    }

    /// ditto
    Slice!(MemberIterator!(T*, name)) member(T)(T[] array)
    {
        return member(array.sliced);
    }

    /// ditto
    auto member(T)(T withAsSlice)
        if (hasAsSlice!T)
    {
        return member(withAsSlice.asSlice);
    }
}

///
version(mir_test)
@safe pure unittest
{
    // struct, union or class
    struct S
    {
        // Property support
        // Getter always must be defined.
        double _x;
        double x() @property
        {
            return x;
        }
        void x(double x) @property
        {
            _x = x;
        }

        /// Field support
        double y;

        /// Zero argument function support
        double f()
        {
            return _x * 2;
        }
    }

    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto matrix = slice!S(2, 3);
    matrix.member!"x"[] = [2, 3].iota;
    matrix.member!"y"[] = matrix.member!"f";
    assert(matrix.member!"y" == [2, 3].iota * 2);
}

/++
Functional deep-element wise reduce of a slice composed of fields or iterators.
+/
template orthogonalReduceField(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    {
    @optmath:
        /++
        Params:
            slice = Non empty input slice composed of fields or iterators.
        Returns:
            a lazy field with each element of which is reduced value of element of the same index of all iterators.
        +/
        OrthogonalReduceField!(Iterator, fun, I) orthogonalReduceField(I, Iterator)(I initialValue, Slice!Iterator slice)
        {
            return typeof(return)(slice, initialValue);
        }

        /// ditto
        OrthogonalReduceField!(T*, fun, I) orthogonalReduceField(I, T)(I initialValue, T[] array)
        {
            return orthogonalReduceField(initialValue, array.sliced);
        }

        /// ditto
        auto orthogonalReduceField(I, T)(I initialValue, T withAsSlice)
            if (hasAsSlice!T)
        {
            return orthogonalReduceField(initialValue, withAsSlice.asSlice);
        }
    }
    else alias orthogonalReduceField = .orthogonalReduceField!(naryFun!fun);
}

/// bit array operations
version(mir_test)
unittest
{
    import mir.ndslice.slice: slicedField;
    import mir.ndslice.allocation: bitSlice;
    import mir.ndslice.dynamic: strided;
    import mir.ndslice.topology: iota, orthogonalReduceField;
    auto len = 100;
    auto a = len.bitSlice;
    auto b = len.bitSlice;
    auto c = len.bitSlice;
    a[len.iota.strided!0(7)][] = true;
    b[len.iota.strided!0(11)][] = true;
    c[len.iota.strided!0(13)][] = true;

    // this is valid since bitslices above are oroginal slices of allocated memory.
    auto and =
        orthogonalReduceField!"a & b"(size_t.max, [
            a.iterator._field._field, // get raw data pointers
            b.iterator._field._field,
            c.iterator._field._field,
        ]) // operation on size_t
        .bitwiseField
        .slicedField(len);

    assert(and == (a & b & c));
}

/++
Constructs a lazy view of triplets with `left`, `center`, and `right` members.

Returns: Slice of the same length composed of $(SUBREF iterator, Triplet) triplets.
The `center` member is type of a slice element.
The `left` and `right` members has the same type as slice.

The module contains special function $(LREF collapse) to handle
left and right side of triplets in one expression.

Params:
    slice = a slice or an array to iterate over

Example:
------
triplets(eeeeee) =>

||c|lllll|
|r|c|llll|
|rr|c|lll|
|rrr|c|ll|
|rrrr|c|l|
|rrrrr|c||
------

See_also: $(LREF stairs).
+/
Slice!(TripletIterator!(Iterator, kind)) triplets(Iterator, SliceKind kind)(Slice!(Iterator, 1, kind) slice)
{
    return typeof(return)(slice.length, typeof(return).Iterator(0, slice));
}

/// ditto
Slice!(TripletIterator!(T*)) triplets(T)(scope return T[] slice)
{
    return .triplets(slice.sliced);
}

/// ditto
auto triplets(string type, S)(S slice, size_t n)
    if (hasAsSlice!S)
{
    return .triplets(slice.asSlice);
}

///
version(mir_test) unittest
{
    import mir.ndslice.topology: triplets, member, iota;

    auto a = [4, 5, 2, 8];
    auto h = a.triplets;

    assert(h[1].center == 5);
    assert(h[1].left == [4]);
    assert(h[1].right == [2, 8]);

    h[1].center = 9;
    assert(a[1] == 9);

    assert(h.member!"center" == a);

    // `triplets` topology can be used with iota to index a slice
    auto s = a.sliced;
    auto w = s.length.iota.triplets[1];

    assert(&s[w.center] == &a[1]);
    assert(s[w.left].field is a[0 .. 1]);
    assert(s[w.right].field is a[2 .. $]);
}
