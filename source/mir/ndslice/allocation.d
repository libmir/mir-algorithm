/++
This is a submodule of $(MREF mir,ndslice).

It contains allocation utilities.


$(BOOKTABLE $(H2 Common utilities),
$(T2 shape, Returns a shape of a common n-dimensional array. )
)

$(BOOKTABLE $(H2 GC Allocation utilities),
$(TR $(TH Function Name) $(TH Description))
$(T2 slice, Allocates a slice using GC.)
$(T2 bitSlice, GC-Allocates a bitwise packed n-dimensional boolean slice.)
$(T2 ndarray, Allocates a common n-dimensional array from a slice. )
$(T2 uninitSlice, Allocates an uninitialized slice using GC. )
)

$(BOOKTABLE $(H2 Ref counted allocation utilities),
$(T2 rcslice, Allocates an n-dimensional reference-counted (thread-safe) slice.)
$(T2 bitRcslice, Allocates a bitwise packed n-dimensional reference-counted (thread-safe) boolean slice.)
$(T2 mininitRcslice, Allocates a minimally initialized n-dimensional reference-counted (thread-safe) slice.)
)

$(BOOKTABLE $(H2 Custom allocation utilities),
$(TR $(TH Function Name) $(TH Description))
$(T2 makeNdarray, Allocates a common n-dimensional array from a slice using an allocator. )
$(T2 makeSlice, Allocates a slice using an allocator. )
$(T2 makeUninitSlice, Allocates an uninitialized slice using an allocator. )
)

$(BOOKTABLE $(H2 CRuntime allocation utilities),
$(TR $(TH Function Name) $(TH Description))
$(T2 stdcSlice, Allocates a slice copy using `core.stdc.stdlib.malloc`)
$(T2 stdcUninitSlice, Allocates an uninitialized slice using `core.stdc.stdlib.malloc`.)
$(T2 stdcFreeSlice, Frees memory using `core.stdc.stdlib.free`)
)

$(BOOKTABLE $(H2 Aligned allocation utilities),
$(TR $(TH Function Name) $(TH Description))
$(T2 uninitAlignedSlice, Allocates an uninitialized aligned slice using GC. )
$(T2 stdcUninitAlignedSlice, Allocates an uninitialized aligned slice using CRuntime.)
$(T2 stdcFreeAlignedSlice, Frees memory using CRuntime)
)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.allocation;

import mir.math.common: optmath;
import mir.ndslice.concatenation;
import mir.ndslice.field: BitField;
import mir.ndslice.internal;
import mir.ndslice.iterator: FieldIterator;
import mir.ndslice.slice;
import mir.rc.array;
import std.traits;
import std.meta: staticMap;

@optmath:

/++
Allocates an n-dimensional reference-counted (thread-safe) slice.
Params:
    lengths = List of lengths for each dimension.
    init = Value to initialize with (optional).
    slice = Slice to copy shape and data from (optional).
Returns:
    n-dimensional slice
+/
Slice!(RCI!T, N)
    rcslice(T, size_t N)(size_t[N] lengths...)
{
    immutable len = lengths.lengthsProduct;
    auto _lengths = lengths;
    return typeof(return)(_lengths, RCI!T(RCArray!T(len)));
}

/// ditto
Slice!(RCI!T, N)
    rcslice(T, size_t N)(size_t[N] lengths, T init)
{
    auto ret = (()@trusted => mininitRcslice!T(lengths))();
    ret.lightScope.field[] = init;
    static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
    return move(ret);
}

/// ditto
auto rcslice(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
{
    import mir.conv: emplaceRef;
    alias E = slice.DeepElement;

    auto result = (() @trusted => slice.shape.mininitRcslice!(Unqual!E))();

    import mir.algorithm.iteration: each;
    each!(emplaceRef!E)(result.lightScope, slice.lightScope);

    static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
    return move(*(() @trusted => cast(Slice!(RCI!E, N)*) &result)());
}

///
version(mir_test)
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.slice: Slice;
    import mir.rc.array: RCI;
    auto tensor = rcslice!int(5, 6, 7);
    assert(tensor.length == 5);
    assert(tensor.elementCount == 5 * 6 * 7);
    static assert(is(typeof(tensor) == Slice!(RCI!int, 3)));

    // creates duplicate using `rcslice`
    auto dup = tensor.rcslice;
    assert(dup == tensor);
}

///
version(mir_test)
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.slice: Slice;
    import mir.rc.array: RCI;
    auto tensor = rcslice([2, 3], 5);
    assert(tensor.elementCount == 2 * 3);
    assert(tensor[1, 1] == 5);

    import mir.rc.array;
    static assert(is(typeof(tensor) == Slice!(RCI!int, 2)));
}

/// ditto
auto rcslice(size_t dim, Slices...)(Concatenation!(dim, Slices) concatenation)
{
    alias T = Unqual!(concatenation.DeepElement);
    auto ret = (()@trusted => mininitRcslice!T(concatenation.shape))();
    static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
    ret.lightScope.opIndexAssign(concatenation);
    return ret;
}

///
version(mir_test)
@safe pure nothrow @nogc unittest
{
    import mir.ndslice.slice: Slice;
    import mir.ndslice.topology : iota;
    import mir.ndslice.concatenation;
    auto tensor = concatenation([2, 3].iota, [3].iota(6)).rcslice;
    assert(tensor == [3, 3].iota);

    static assert(is(typeof(tensor) == Slice!(RCI!ptrdiff_t, 2)));
}

/++
Allocates a bitwise packed n-dimensional reference-counted (thread-safe) boolean slice.
Params:
    lengths = List of lengths for each dimension.
Returns:
    n-dimensional bitwise rcslice
See_also: $(SUBREF topology, bitwise).
+/
Slice!(FieldIterator!(BitField!(RCI!size_t)), N) bitRcslice(size_t N)(size_t[N] lengths...)
{
    import mir.ndslice.topology: bitwise;
    enum elen = size_t.sizeof * 8;
    immutable len = lengths.lengthsProduct;
    immutable dlen = (len / elen + (len % elen != 0));
    return RCArray!size_t(dlen).asSlice.bitwise[0 .. len].sliced(lengths);
}

/// 1D
@safe pure nothrow @nogc
version(mir_test) unittest
{
    auto bitarray = 100.bitRcslice; // allocates 16 bytes total (plus RC context)
    assert(bitarray.shape == cast(size_t[1])[100]);
    assert(bitarray[72] == false);
    bitarray[72] = true;
    assert(bitarray[72] == true);
}

/// 2D
@safe pure nothrow @nogc
version(mir_test) unittest
{
    auto bitmatrix = bitRcslice(20, 6); // allocates 16 bytes total (plus RC context)
    assert(bitmatrix.shape == cast(size_t[2])[20, 6]);
    assert(bitmatrix[3, 4] == false);
    bitmatrix[3, 4] = true;
    assert(bitmatrix[3, 4] == true);
}

/++
Allocates a minimally initialized n-dimensional reference-counted (thread-safe) slice.
Params:
    lengths = list of lengths for each dimension
Returns:
    contiguous minimally initialized n-dimensional reference-counted (thread-safe) slice
+/
Slice!(RCI!T, N) mininitRcslice(T, size_t N)(size_t[N] lengths...)
{
    immutable len = lengths.lengthsProduct;
    auto _lengths = lengths;
    return Slice!(RCI!T, N)(_lengths, RCI!T(mininitRcarray!T(len)));
}

///
version(mir_test)
pure nothrow @nogc unittest
{
    import mir.ndslice.slice: Slice;
    import mir.rc.array: RCI;
    auto tensor = mininitRcslice!int(5, 6, 7);
    assert(tensor.length == 5);
    assert(tensor.elementCount == 5 * 6 * 7);
    static assert(is(typeof(tensor) == Slice!(RCI!int, 3)));
}

private alias Pointer(T) = T*;
private alias Pointers(Args...) = staticMap!(Pointer, Args);

/++
GC-Allocates an n-dimensional slice.
+/
template slice(Args...)
    if (Args.length)
{
    ///
    alias LabelTypes = Args[1 .. $];
    ///
    alias T = Args[0];

    /++
    Params:
        lengths = List of lengths for each dimension.
        init = Value to initialize with (optional).
    Returns:
        initialzed n-dimensional slice
    +/
    Slice!(T*, N, Contiguous, Pointers!LabelTypes)
        slice(size_t N)(size_t[N] lengths...)
        if (N >= LabelTypes.length)
    {
        auto shape = lengths; // DMD variadic bug workaround
        immutable len = shape.lengthsProduct;
        auto ret = typeof(return)(shape, len == 0 ? null : (()@trusted=>new T[len].ptr)());
        foreach (i, L; LabelTypes) // static
            ret._labels[i] = (()@trusted=>new L[shape[i]].ptr)();
        return ret;
    }

    /// ditto
    Slice!(T*, N, Contiguous, Pointers!LabelTypes)
        slice(size_t N)(size_t[N] lengths, T init)
        if (N >= LabelTypes.length)
    {
        import mir.conv: emplaceRef;
        import std.array : uninitializedArray;
        immutable len = lengths.lengthsProduct;
        auto arr = uninitializedArray!(Unqual!T[])(len);
        foreach (ref e; arr)
            emplaceRef(e, init);
        auto ret = typeof(return)(lengths, len == 0 ? null : (()@trusted=>cast(T*)arr.ptr)());
        foreach (i, L; LabelTypes) // static
            ret._labels[i] = (()@trusted=>new L[shape[i]].ptr)();
        return ret;
    }
}

///
version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.slice: Slice;
    auto tensor = slice!int(5, 6, 7);
    assert(tensor.length == 5);
    assert(tensor.length!1 == 6);
    assert(tensor.elementCount == 5 * 6 * 7);
    static assert(is(typeof(tensor) == Slice!(int*, 3)));
}

/// 2D DataFrame example
version(mir_test)
@safe pure unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.allocation: slice;

    import std.datetime.date;

    auto dataframe = slice!(double, Date, string)(4, 3);
    assert(dataframe.length == 4);
    assert(dataframe.length!1 == 3);
    assert(dataframe.elementCount == 4 * 3);

    static assert(is(typeof(dataframe) ==
        Slice!(double*, 2, Contiguous, Date*, string*)));

    // Dataframe labels are contiguous 1-dimensional slices.

    // Fill row labels
    dataframe.label[] = [
        Date(2019, 1, 24),
        Date(2019, 2, 2),
        Date(2019, 2, 4),
        Date(2019, 2, 5),
    ];

    assert(dataframe.label!0[2] == Date(2019, 2, 4));

    // Fill column labels
    dataframe.label!1[] = ["income", "outcome", "balance"];

    assert(dataframe.label!1[2] == "balance");

    // Change label element
    dataframe.label!1[2] = "total";
    assert(dataframe.label!1[2] == "total");

    // Attach a newly allocated label
    dataframe.label!1 = ["Income", "Outcome", "Balance"].sliced;

    assert(dataframe.label!1[2] == "Balance");
}

/++
GC-Allocates an n-dimensional slice.
Params:
    lengths = List of lengths for each dimension.
    init = Value to initialize with (optional).
Returns:
    initialzed n-dimensional slice
+/
Slice!(T*, N)
    slice(size_t N, T)(size_t[N] lengths, T init)
{
    return .slice!T(lengths, init);
}

// TODO: make it a dataframe compatible. This function performs copy.
/// ditto
auto slice(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
{
    if (__ctfe)
    {
        import mir.ndslice.topology: flattened;
        import mir.array.allocation: array;
        return slice.flattened.array.sliced(slice.shape);
    }
    else
    {
        import mir.conv: emplaceRef;
        alias E = slice.DeepElement;

        auto result = (() @trusted => slice.shape.uninitSlice!(Unqual!E))();

        import mir.algorithm.iteration: each;
        each!(emplaceRef!E)(result, slice);

        return (() @trusted => cast(Slice!(E*, N)) result)();
    }
}

///
version(mir_test)
@safe pure nothrow unittest
{
    auto tensor = slice([2, 3], 5);
    assert(tensor.elementCount == 2 * 3);
    assert(tensor[1, 1] == 5);

    // creates duplicate using `slice`
    auto dup = tensor.slice;
    assert(dup == tensor);
}

/// ditto
auto slice(size_t dim, Slices...)(Concatenation!(dim, Slices) concatenation)
{
    alias T = Unqual!(concatenation.DeepElement);
    static if (hasElaborateAssign!T)
        alias fun = .slice;
    else
        alias fun = .uninitSlice;
    auto ret = (()@trusted => fun!T(concatenation.shape))();
    ret.opIndexAssign(concatenation);
    return ret;
}

///
version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.slice: Slice;
    import mir.ndslice.topology : iota;
    import mir.ndslice.concatenation;
    auto tensor = concatenation([2, 3].iota, [3].iota(6)).slice;
    assert(tensor == [3, 3].iota);

    static assert(is(typeof(tensor) == Slice!(ptrdiff_t*, 2)));
}

/++
GC-Allocates a bitwise packed n-dimensional boolean slice.
Params:
    lengths = List of lengths for each dimension.
Returns:
    n-dimensional bitwise slice
See_also: $(SUBREF topology, bitwise).
+/
Slice!(FieldIterator!(BitField!(size_t*)), N) bitSlice(size_t N)(size_t[N] lengths...)
{
    import mir.ndslice.topology: bitwise;
    enum elen = size_t.sizeof * 8;
    immutable len = lengths.lengthsProduct;
    immutable dlen = (len / elen + (len % elen != 0));
    return new size_t[dlen].sliced.bitwise[0 .. len].sliced(lengths);
}

/// 1D
@safe pure version(mir_test) unittest
{
    auto bitarray = bitSlice(100); // allocates 16 bytes total
    assert(bitarray.shape == [100]);
    assert(bitarray[72] == false);
    bitarray[72] = true;
    assert(bitarray[72] == true);
}

/// 2D
@safe pure version(mir_test) unittest
{
    auto bitmatrix = bitSlice(20, 6); // allocates 16 bytes total
    assert(bitmatrix.shape == [20, 6]);
    assert(bitmatrix[3, 4] == false);
    bitmatrix[3, 4] = true;
    assert(bitmatrix[3, 4] == true);
}

/++
GC-Allocates an uninitialized n-dimensional slice.
Params:
    lengths = list of lengths for each dimension
Returns:
    contiguous uninitialized n-dimensional slice
+/
auto uninitSlice(T, size_t N)(size_t[N] lengths...)
{
    immutable len = lengths.lengthsProduct;
    import std.array : uninitializedArray;
    auto arr = uninitializedArray!(T[])(len);
    return arr.sliced(lengths);
}

///
version(mir_test)
@safe pure nothrow unittest
{
    import mir.ndslice.slice: Slice;
    auto tensor = uninitSlice!int(5, 6, 7);
    assert(tensor.length == 5);
    assert(tensor.elementCount == 5 * 6 * 7);
    static assert(is(typeof(tensor) == Slice!(int*, 3)));
}

/++
GC-Allocates an uninitialized aligned an n-dimensional slice.
Params:
    lengths = list of lengths for each dimension
    alignment = memory alignment (bytes)
Returns:
    contiguous uninitialized n-dimensional slice
+/
auto uninitAlignedSlice(T, size_t N)(size_t[N] lengths, uint alignment) @system
{
    immutable len = lengths.lengthsProduct;
    import std.array : uninitializedArray;
    assert((alignment != 0) && ((alignment & (alignment - 1)) == 0), "'alignment' must be a power of two");
    size_t offset = alignment <= 16 ? 0 : alignment - 1;
    void* basePtr = uninitializedArray!(byte[])(len * T.sizeof + offset).ptr;
    T* alignedPtr = cast(T*)((cast(size_t)(basePtr) + offset) & ~offset);
    return alignedPtr.sliced(lengths);
}

///
version(mir_test)
@system pure nothrow unittest
{
    import mir.ndslice.slice: Slice;
    auto tensor = uninitAlignedSlice!double([5, 6, 7], 64);
    tensor[] = 0;
    assert(tensor.length == 5);
    assert(tensor.elementCount == 5 * 6 * 7);
    assert(cast(size_t)(tensor.ptr) % 64 == 0);
    static assert(is(typeof(tensor) == Slice!(double*, 3)));
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
    alias T = Unqual!(slice.DeepElement);
    return makeSlice!(T)(alloc, slice);
}

/// ditto
Slice!(T*, N)
makeSlice(T, Allocator, size_t N)(auto ref Allocator alloc, size_t[N] lengths...)
{
    import std.experimental.allocator : makeArray;
    return alloc.makeArray!T(lengths.lengthsProduct).sliced(lengths);
}

/// ditto
Slice!(T*, N)
makeSlice(T, Allocator, size_t N)(auto ref Allocator alloc, size_t[N] lengths, T init)
{
    import std.experimental.allocator : makeArray;
    immutable len = lengths.lengthsProduct;
    auto array = alloc.makeArray!T(len, init);
    return array.sliced(lengths);
}

/// ditto
auto makeSlice(Allocator, Iterator, size_t N, SliceKind kind)
    (auto ref Allocator allocator, Slice!(Iterator, N, kind) slice)
{
    import mir.conv: emplaceRef;
    alias E = slice.DeepElement;

    auto result = allocator.makeUninitSlice!(Unqual!E)(slice.shape);

    import mir.algorithm.iteration: each;
    each!(emplaceRef!E)(result, slice);

    return cast(Slice!(E*, N)) result;
}

/// Initialization with default value
version(mir_test)
@nogc unittest
{
    import std.experimental.allocator;
    import std.experimental.allocator.mallocator;
    import mir.algorithm.iteration: all;
    import mir.ndslice.topology: map;

    auto sl = Mallocator.instance.makeSlice([2, 3, 4], 10);
    auto ar = sl.field;
    assert(sl.all!"a == 10");

    auto sl2 = Mallocator.instance.makeSlice(sl.map!"a * 2");
    auto ar2 = sl2.field;
    assert(sl2.all!"a == 20");

    Mallocator.instance.dispose(ar);
    Mallocator.instance.dispose(ar2);
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
Slice!(T*, N)
makeUninitSlice(T, Allocator, size_t N)(auto ref Allocator alloc, size_t[N] lengths...)
    if (N)
{
    if (immutable len = lengths.lengthsProduct)
    {
        auto mem = alloc.allocate(len * T.sizeof);
        if (mem.length == 0) assert(0);
        auto array = () @trusted { return cast(T[]) mem; }();
        return array.sliced(lengths);
    }
    else
    {
        return T[].init.sliced(lengths);
    }
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
    assert(sl.elementCount    == 24);

    Mallocator.instance.dispose(ar);
}

/++
Allocates a common n-dimensional array from a slice.
Params:
    slice = slice
Returns:
    multidimensional D array
+/
auto ndarray(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
{
    import  mir.array.allocation : array;
    static if (slice.N == 1)
    {
        return array(slice);
    }
    else
    {
        import mir.ndslice.topology: ipack, map;
        return array(slice.ipack!1.map!(a => .ndarray(a)));
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
auto makeNdarray(T, Allocator, Iterator, size_t N, SliceKind kind)(auto ref Allocator alloc, Slice!(Iterator, N, kind) slice)
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
Allocates an uninitialized array using `core.stdc.stdlib.malloc` and creates an n-dimensional slice over it.
Params:
    lengths = list of lengths for each dimension
Returns:
    contiguous uninitialized n-dimensional slice
See_also:
    $(LREF stdcSlice), $(LREF stdcFreeSlice)
+/
Slice!(T*, N) stdcUninitSlice(T, size_t N)(size_t[N] lengths...)
{
    import core.stdc.stdlib: malloc;
    immutable len = lengths.lengthsProduct;
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
    $(LREF stdcUninitSlice), $(LREF stdcFreeSlice)
+/
auto stdcSlice(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
{
    alias E = slice.DeepElement;
    alias T = Unqual!E;
    static assert (!hasElaborateAssign!T, "stdcSlice is not miplemented for slices that have elaborate assign");
    auto ret = stdcUninitSlice!T(slice.shape);

    import mir.conv: emplaceRef;
    import mir.algorithm.iteration: each;
    each!(emplaceRef!E)(ret, slice);
    return ret;
}

/++
Frees memory using `core.stdc.stdlib.free`.
Params:
    slice = n-dimensional slice
See_also:
    $(LREF stdcSlice), $(LREF stdcUninitSlice)
+/
void stdcFreeSlice(T, size_t N)(Slice!(T*, N) slice)
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

/++
Allocates an uninitialized aligned array using `core.stdc.stdlib.malloc` and creates an n-dimensional slice over it.
Params:
    lengths = list of lengths for each dimension
    alignment = memory alignment (bytes)
Returns:
    contiguous uninitialized n-dimensional slice
+/
auto stdcUninitAlignedSlice(T, size_t N)(size_t[N] lengths, uint alignment) @system
{
    immutable len = lengths.lengthsProduct;
    import mir.internal.memory: alignedAllocate;
    auto arr = (cast(T*)alignedAllocate(len * T.sizeof, alignment))[0 .. len];
    return arr.sliced(lengths);
}

///
version(mir_test)
@system pure nothrow unittest
{
    auto tensor = stdcUninitAlignedSlice!double([5, 6, 7], 64);
    assert(tensor.length == 5);
    assert(tensor.elementCount == 5 * 6 * 7);
    assert(cast(size_t)(tensor.ptr) % 64 == 0);
    static assert(is(typeof(tensor) == Slice!(double*, 3)));
    stdcFreeAlignedSlice(tensor);
}

/++
Frees aligned memory allocaged by CRuntime.
Params:
    slice = n-dimensional slice
See_also:
    $(LREF stdcSlice), $(LREF stdcUninitSlice)
+/
void stdcFreeAlignedSlice(T, size_t N)(Slice!(T*, N) slice)
{
    import mir.internal.memory: alignedFree;
    slice._iterator.alignedFree;
}
