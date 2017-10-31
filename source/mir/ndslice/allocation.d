/++
This is a submodule of $(MREF mir,ndslice).

It contains allocation utilities.

$(BOOKTABLE $(H2 Transpose operators),
$(TR $(TH Function Name) $(TH Description))
$(T2 makeNdarray, Allocates a common n-dimensional array from a slice using an allocator. )
$(T2 makeSlice, Allocates a slice using an allocator. )
$(T2 makeUninitSlice, Allocates an uninitialized slice using an allocator. )
$(T2 ndarray, Allocates a common n-dimensional array from a slice. )
$(T2 shape, Returns a shape of a common n-dimensional array. )
$(T2 slice, Allocates a slice using GC.)
$(T2 uninitSlice, Allocates an uninitialized slice using GC. )
$(T2 stdcSlice, Allocates a slice copy using `core.stdc.stdlib.malloc`)
$(T2 stdcFreeSlice, Frees memory using `core.stdc.stdlib.free`)
$(T2 stdcUninitSlice, Allocates an uninitialized slice using `core.stdc.stdlib.malloc`.)
)


License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.allocation;

import std.traits;
import mir.ndslice.slice;
import mir.ndslice.internal;
import mir.ndslice.concatenation;
import mir.math.common: optmath;


deprecated("use uninitSlice instead")
alias uninitializedSlice = uninitSlice;
deprecated("use makeUninitSlice instead")
alias makeUninitializedSlice = makeUninitSlice;

@optmath:

/++
Allocates an array and an n-dimensional slice over it.
Params:
    lengths = List of lengths for each dimension.
    init = Value to initialize with.
    slice = Slice to copy shape and data from.
Returns:
    n-dimensional slice
+/
ContiguousSlice!(N, T)
    slice(T, size_t N)(size_t[N] lengths...)
{
    immutable len = lengthsProduct(lengths);
    return new T[len].sliced(lengths);
}

/// ditto
ContiguousSlice!(N, T)
    slice(T, size_t N)(size_t[N] lengths, T init)
{
    immutable len = lengthsProduct(lengths);
    static if (!hasElaborateAssign!T)
    {
        import std.array : uninitializedArray;
        auto arr = uninitializedArray!(Unqual!T[])(len);
    }
    else
    {
        auto arr = new Unqual!T[len];
    }
    arr[] = init;
    auto ret = .sliced(cast(T[])arr, lengths);
    return ret;
}

/// ditto
auto slice(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
{
    alias T = Unqual!(slice.DeepElemType);
    static if (hasElaborateAssign!T)
        alias fun = .slice;
    else
        alias fun = .uninitSlice;
    auto ret = (shape)@trusted{ return fun!T(shape);}(slice.shape);
    ret[] = slice;
    auto retq = ()@trusted{ return (cast(slice.DeepElemType*)ret._iterator).sliced(ret.shape); }();
    return retq;
}

///
version(mir_test)
@safe pure nothrow unittest
{
    auto tensor = slice!int(5, 6, 7);
    assert(tensor.length == 5);
    assert(tensor.elementsCount == 5 * 6 * 7);
    static assert(is(typeof(tensor) == Slice!(Contiguous, [3], int*)));

    // creates duplicate using `slice`
    auto dup = tensor.slice;
    assert(dup == tensor);
}

///
version(mir_test)
@safe pure nothrow unittest
{
    auto tensor = slice([2, 3], 5);
    assert(tensor.elementsCount == 2 * 3);
    assert(tensor[1, 1] == 5);
}

/// ditto
auto slice(size_t dim, Slices...)(Concatenation!(dim, Slices) concatenation)
{
    alias T = Unqual!(concatenation.DeepElemType);
    static if (hasElaborateAssign!T)
        alias fun = .slice;
    else
        alias fun = .uninitSlice;
    auto ret = (shape)@trusted{ return fun!T(shape);}(concatenation.shape);
    ret[] = concatenation;
    return ret;
}

version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    auto tensor = iota(2, 3).slice;
    assert(tensor == [[0, 1, 2], [3, 4, 5]]);
}

/++
Allocates an uninitialized array and an n-dimensional slice over it.
Params:
    lengths = list of lengths for each dimension
Returns:
    contiguous uninitialized n-dimensional slice
+/
auto uninitSlice(T, size_t N)(size_t[N] lengths...)
{
    immutable len = lengthsProduct(lengths);
    import std.array : uninitializedArray;
    auto arr = uninitializedArray!(T[])(len);
    return arr.sliced(lengths);
}

///
version(mir_test)
@safe pure nothrow unittest
{
    auto tensor = uninitSlice!int(5, 6, 7);
    assert(tensor.length == 5);
    assert(tensor.elementsCount == 5 * 6 * 7);
    static assert(is(typeof(tensor) == Slice!(Contiguous, [3], int*)));
}

/++
Allocates an array through a specified allocator and creates an n-dimensional slice over it.
See also $(MREF std, experimental, allocator).
Params:
    alloc = allocator
    lengths = list of lengths for each dimension
    init = default value for array initialization
    slice = slice to copy shape and data from
Returns:
    a structure with fields `array` and `slice`
Note:
    `makeSlice` always returns slice with mutable elements
+/
auto makeSlice(Allocator, size_t N, Iterator)(auto ref Allocator alloc, Slice!(N, Iterator) slice)
{
    alias T = Unqual!(slice.DeepElemType);
    return makeSlice!(T)(alloc, slice);
}

/// ditto
ContiguousSlice!(N, T)
makeSlice(T, Allocator, size_t N)(auto ref Allocator alloc, size_t[N] lengths...)
{
    import std.experimental.allocator : makeArray;
    return alloc.makeArray!T(lengthsProduct(lengths)).sliced(lengths);
}

/// ditto
ContiguousSlice!(N, T)
makeSlice(T, Allocator, size_t N)(auto ref Allocator alloc, size_t[N] lengths, T init)
{
    import std.experimental.allocator : makeArray;
    immutable len = lengthsProduct(lengths);
    auto array = alloc.makeArray!T(len, init);
    return array.sliced(lengths);
}

///// ditto
//ContiguousSlice!(N, T)
//makeSlice(T,
//    Flag!`replaceArrayWithPointer` ra = Yes.replaceArrayWithPointer,
//    Allocator,
//    SliceKind kind, size_t[] packs, Iterator)(auto ref Allocator alloc, Slice!(kind, packs, Iterator) slice)
//{
//    import std.experimental.allocator : makeArray;
//    import mir.ndslice.topology : flattened;
//    auto array = alloc.makeArray!T(slice.flattened);
//    auto _slice = array.sliced!ra(slice.shape);
//    return typeof(return)(array, _slice);
//}

/////
version(mir_test)
//@nogc unittest
//{
//    import std.experimental.allocator;
//    import std.experimental.allocator.mallocator;

//    auto tup = makeSlice!int(Mallocator.instance, 2, 3, 4);

//    assert(tup.array.length           == 24);
//    assert(tup.slice.elementsCount    == 24);
//    assert(tup.array.ptr == &tup.slice[0, 0, 0]);

//     //makes duplicate using `makeSlice`
//    tup.slice[0, 0, 0] = 3;
//    auto dup = makeSlice(Mallocator.instance, tup.slice);
//    assert(dup.slice == tup.slice);

//    Mallocator.instance.dispose(tup.array);
//    Mallocator.instance.dispose(dup.array);
//}

/// Initialization with default value
version(mir_test)
@nogc unittest
{
    import std.experimental.allocator;
    import std.experimental.allocator.mallocator;

    auto sl = makeSlice(Mallocator.instance, [2, 3, 4], 10);
    auto ar = sl.field;
    assert(sl[1, 1, 1] == 10);
    Mallocator.instance.dispose(ar);
}

version(mir_test)
@nogc unittest
{
    import std.experimental.allocator;
    import std.experimental.allocator.mallocator;

    // cast to your own type
    auto sl = makeSlice!double(Mallocator.instance, [2, 3, 4], 10);
    auto ar = sl.field;
    assert(sl[1, 1, 1] == 10.0);
    Mallocator.instance.dispose(ar);
}

/++
Allocates an uninitialized array through a specified allocator and creates an n-dimensional slice over it.
See also $(MREF std, experimental, allocator).
Params:
    alloc = allocator
    lengths = list of lengths for each dimension
Returns:
    a structure with fields `array` and `slice`
+/
ContiguousSlice!(N, T)
makeUninitSlice(T, Allocator, size_t N)(auto ref Allocator alloc, size_t[N] lengths...)
{
    immutable len = lengthsProduct(lengths);
    auto array = cast(T[]) alloc.allocate(len * T.sizeof);
    return array.sliced(lengths);
}

///
version(mir_test)
@system @nogc unittest
{
    import std.experimental.allocator;
    import std.experimental.allocator.mallocator;

    auto sl = makeUninitSlice!int(Mallocator.instance, 2, 3, 4);
    auto ar = sl.field;
    assert(ar.ptr is sl.iterator);
    assert(ar.length           == 24);
    assert(sl.elementsCount    == 24);

    Mallocator.instance.dispose(ar);
}

/++
Allocates a common n-dimensional array from a slice.
Params:
    slice = slice
Returns:
    multidimensional D array
+/
auto ndarray(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
{
    import std.array : array;
    static if (slice.N == 1)
    {
        return array(slice);
    }
    else
    {
        import std.algorithm.iteration : map;
        return array(slice.map!(a => .ndarray(a)));
    }
}

///
version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    auto slice = iota(3, 4);
    auto m = slice.ndarray;
    static assert(is(typeof(m) == sizediff_t[][])); // sizediff_t is long for 64 bit platforms
    assert(m == [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]]);
}

/++
Allocates a common n-dimensional array using data from a slice.
Params:
    alloc = allocator (optional)
    slice = slice
Returns:
    multidimensional D array
+/
auto makeNdarray(T, Allocator, SliceKind kind, size_t[] packs, Iterator)(auto ref Allocator alloc, Slice!(kind, packs, Iterator) slice)
{
    import std.experimental.allocator : makeArray;
    static if (slice.N == 1)
    {
        return makeArray!T(alloc, slice);
    }
    else
    {
        alias E = typeof(makeNdarray!T(alloc, slice[0]));
        auto ret = makeArray!E(alloc, slice.length);
        foreach (i, ref e; ret)
            e = .makeNdarray!T(alloc, slice[i]);
        return ret;
    }
}

///
version(mir_test)
@nogc unittest
{
    import std.experimental.allocator;
    import std.experimental.allocator.mallocator;
    import mir.ndslice.topology : iota;

    auto slice = iota(3, 4);
    auto m = Mallocator.instance.makeNdarray!long(slice);

    static assert(is(typeof(m) == long[][]));

    static immutable ar = [[0L, 1, 2, 3], [4L, 5, 6, 7], [8L, 9, 10, 11]];
    assert(m == ar);

    foreach (ref row; m)
        Mallocator.instance.dispose(row);
    Mallocator.instance.dispose(m);
}

/++
Shape of a common n-dimensional array.
Params:
    array = common n-dimensional array
    err = error flag passed by reference
Returns:
    static array of dimensions type of `size_t[n]`
+/
auto shape(T)(T[] array, ref int err)
{
    static if (isDynamicArray!T)
    {
        size_t[1 + typeof(shape(T.init, err)).length] ret;

        if (array.length)
        {
            ret[0] = array.length;
            ret[1..$] = shape(array[0], err);
            if (err)
                goto L;
            foreach (ar; array)
            {
                if (shape(ar, err) != ret[1..$])
                    err = 1;
                if (err)
                    goto L;
            }
        }
    }
    else
    {
        size_t[1] ret;
        ret[0] = array.length;
    }
    err = 0;
L:
    return ret;
}

///
version(mir_test)
@safe pure unittest
{
    int err;
    size_t[2] shape = [[1, 2, 3], [4, 5, 6]].shape(err);
    assert(err == 0);
    assert(shape == [2, 3]);

    [[1, 2], [4, 5, 6]].shape(err);
    assert(err == 1);
}

/// Slice from ndarray
version(mir_test)
unittest
{
    import mir.ndslice.allocation: slice, shape;
    int err;
    auto array = [[1, 2, 3], [4, 5, 6]];
    auto s = array.shape(err).slice!int;
    s[] = [[1, 2, 3], [4, 5, 6]];
    assert(s == array);
}

version(mir_test)
@safe pure unittest
{
    int err;
    size_t[2] shape = (int[][]).init.shape(err);
    assert(shape[0] == 0);
    assert(shape[1] == 0);
}

version(mir_test)
nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.topology : iota;

    auto sl = iota([0, 0], 1);

    assert(sl.empty!0);
    assert(sl.empty!1);

    auto gcsl1 = sl.slice;
    auto gcsl2 = slice!double(0, 0);

    import std.experimental.allocator;
    import std.experimental.allocator.mallocator;

    auto sl2 = makeSlice!double(Mallocator.instance, 0, 0);

    Mallocator.instance.dispose(sl2.field);
}

/++
Allocates an uninitialized array using `core.stdc.stdlib.malloc` and an n-dimensional slice over it.
Params:
    lengths = list of lengths for each dimension
Returns:
    contiguous uninitialized n-dimensional slice
See_also:
    $(MREF stdcSlice), $(MREF stdcFreeSlice)
+/
Slice!(Contiguous, [N], T*) stdcUninitSlice(T, size_t N)(size_t[N] lengths...)
{
    import core.stdc.stdlib: malloc;
    immutable len = lengthsProduct(lengths);
    auto ptr = len ? cast(T*) malloc(len * T.sizeof) : null;
    return ptr.sliced(lengths);
}

/++
Allocates a copy of a slice using `core.stdc.stdlib.malloc`.
Params:
    slice = n-dimensional slice
Returns:
    contiguous n-dimensional slice
See_also:
    $(MREF stdcUninitSlice), $(MREF stdcFreeSlice)
+/
auto stdcSlice(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
{
    alias T = Unqual!(slice.DeepElemType);
    static assert (!hasElaborateAssign!T, "stdcSlice is not miplemented for slices that have elaborate assign");
    auto ret = stdcUninitSlice!T(slice.shape);
    ret[] = slice;
    return ret;
}

/++
Frees memory using `core.stdc.stdlib.free`.
Params:
    slice = n-dimensional slice
See_also:
    $(MREF stdcSlice), $(MREF stdcUninitSlice)
+/
void stdcFreeSlice(size_t[] packs, T)(Slice!(Contiguous, packs, T*) slice)
{
    import core.stdc.stdlib: free;
    slice._iterator.free;
}

///
version(mir_test)
unittest
{
    import mir.ndslice.topology: iota;
    
    auto i = iota(3, 4);
    auto s = i.stdcSlice;
    auto t = s.shape.stdcUninitSlice!size_t;
    
    t[] = s;

    assert(t == i);
    
    s.stdcFreeSlice;
    t.stdcFreeSlice;
}
