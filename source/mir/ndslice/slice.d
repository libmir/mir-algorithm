/++
This is a submodule of $(MREF mir, ndslice).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

$(BOOKTABLE $(H2 Definitions),
$(TR $(TH Name) $(TH Description))
$(T2 Slice, N-dimensional slice.)
$(T2 SliceKind, Kind of $(LREF Slice) enumeration.)
$(T2 Universal, Alias for $(LREF .SliceKind.universal).)
$(T2 Canonical, Alias for $(LREF .SliceKind.canonical).)
$(T2 Contiguous, Alias for $(LREF .SliceKind.contiguous).)
$(T2 sliced, Creates a slice on top of an iterator, a pointer, or an array's pointer.)
$(T2 slicedField, Creates a slice on top of a field, a random access range, or an array.)
$(T2 slicedNdField, Creates a slice on top of an ndField.)
$(T2 kindOf, Extracts $(LREF SliceKind).)
$(T2 isSlice, Extracts dimension packs from a type. Extracts `null` if the template argument is not a `Slice`.)
$(T2 DeepElementType, Extracts the element type of a $(LREF Slice).)
$(T2 Structure, A tuple of lengths and strides.)
)

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
STD = $(TD $(SMALL $0))
+/
module mir.ndslice.slice;

import std.traits;
import std.meta;

import mir.internal.utility;
import mir.ndslice.internal;
import mir.ndslice.concatenation;
import mir.primitives;
import mir.ndslice.iterator;
import mir.ndslice.field;

@fastmath:

///
template isSlice(T)
{
    static if (is(T : Slice!(kind, packs, Iterator), SliceKind kind, size_t[] packs, Iterator))
        enum size_t[] isSlice = packs[];
    else
        enum size_t[] isSlice = null;
}

///
unittest
{
    alias A = uint[];
    alias S = Slice!(Universal, [2, 3], int*);

    static assert(isSlice!S);
    static assert(!isSlice!A);

    static assert(isSlice!S == [2, 3]);
    static assert(isSlice!A == null);
}

/++
Kind of $(LREF Slice).
See_also:
    $(SUBREF topology, universal),
    $(SUBREF topology, canonical),
    $(SUBREF topology, assumeCanonical),
    $(SUBREF topology, assumeContiguous).
+/
enum SliceKind
{
    /// A slice has strides for all dimensions.
    universal,
    /// A slice has >=2 dimensions and row dimension is contiguous.
    canonical,
    /// A slice is a flat contiguous data without strides.
    contiguous,
}

/++
Alias for $(LREF .SliceKind.universal).

See_also:
    Internal Binary Representation section in $(LREF Slice).
+/
alias Universal = SliceKind.universal;
/++
Alias for $(LREF .SliceKind.canonical).

See_also:
    Internal Binary Representation section in $(LREF Slice).
+/
alias Canonical = SliceKind.canonical;
/++
Alias for $(LREF .SliceKind.contiguous).

See_also:
    Internal Binary Representation section in $(LREF Slice).
+/
alias Contiguous = SliceKind.contiguous;

/// Extracts $(LREF SliceKind).
enum kindOf(T : Slice!(kind, packs, Iterator), SliceKind kind, size_t[] packs, Iterator) = kind;

///
unittest
{
    static assert(kindOf!(Slice!(Universal, [1], int*)) == Universal);
}

private template SkipDimension(size_t dimension, size_t index)
{
    static if (index < dimension)
         enum SkipDimension = index;
    else
    static if (index == dimension)
        static assert (0, "SkipInex: wrong index");
    else
         enum SkipDimension = index - 1;
}

/++
Creates an n-dimensional slice-shell over an iterator.
Params:
    iterator = An iterator, a pointer, or an array.
    lengths = A list of lengths for each dimension
Returns:
    n-dimensional slice
+/
auto sliced(size_t N, Iterator)(Iterator iterator, size_t[N] lengths...)
    if (!isStaticArray!Iterator && !isNarrowString!Iterator && N
        && !is(Iterator : Slice!(kind, packs, _Iterator), SliceKind kind, size_t[] packs, _Iterator))
{
    alias C = ImplicitlyUnqual!(typeof(iterator));
    static if (isDynamicArray!Iterator)
        alias S = Slice!(Contiguous, [N], typeof(C.init[0])*);
    else
        alias S = Slice!(Contiguous, [N], C);
    S ret = S.init;
    static if (isDynamicArray!Iterator)
        ret._iterator = iterator.ptr;
    else
        ret._iterator = iterator;
    foreach(i; Iota!N)
        ret._lengths[i] = lengths[i];
    return ret;
}

/// $(LINK2 https://en.wikipedia.org/wiki/Vandermonde_matrix, Vandermonde matrix)
pure nothrow unittest
{
    auto vandermondeMatrix(Slice!(Universal, [1], double*) x)
    {
        import mir.ndslice.allocation: slice;
        auto ret = slice!double(x.length, x.length);
        foreach (i; 0 .. x.length)
        foreach (j; 0 .. x.length)
            ret[i, j] = x[i] ^^ j;
        return ret;
    }

    import mir.ndslice.topology: universal;
    auto x = [1.0, 2, 3, 4, 5].sliced.universal;
    auto v = vandermondeMatrix(x);
    assert(v ==
        [[  1.0,   1,   1,   1,   1],
         [  1.0,   2,   4,   8,  16],
         [  1.0,   3,   9,  27,  81],
         [  1.0,   4,  16,  64, 256],
         [  1.0,   5,  25, 125, 625]]);
}

/// Random access range primitives for slices over user defined types
pure nothrow @nogc unittest
{
    struct MyIota
    {
        //`[index]` operator overloading
        auto opIndex(size_t index)
        {
            return index;
        }
    }
    import mir.ndslice.iterator: FieldIterator;
    alias Iterator = FieldIterator!MyIota;
    alias S = Slice!(Contiguous, [2], Iterator);
    import std.range.primitives;
    static assert(hasLength!S);
    static assert(hasSlicing!S);
    static assert(isRandomAccessRange!S);

    auto slice = Iterator().sliced(20, 10);
    assert(slice[1, 2] == 12);
    auto sCopy = slice.save;
    assert(slice[1, 2] == 12);
}

/++
Creates an 1-dimensional slice-shell over an array.
Params:
    array = An array.
Returns:
    1-dimensional slice
+/
auto sliced(T)(T[] array)
{
    return .sliced(array, [array.length]);
}

/// Creates a slice from an array.
pure nothrow unittest
{
    auto slice = new int[10].sliced;
    assert(slice.length == 10);
    static assert(is(typeof(slice) == Slice!(Contiguous, [1], int*)));
}

/++
Creates an n-dimensional slice-shell over an iterator.
Params:
    slice = A slice, a pointer, or an array.
    lengths = A list of lengths for each dimension.
Returns:
    n-dimensional slice
+/
Slice!(kind, N ~ (packs[0] == 1 ? [] : [packs[0] - 1]) ~ packs[1 .. $], Iterator)
    sliced
    (SliceKind kind, size_t[] packs, Iterator, size_t N)
    (Slice!(kind, packs, Iterator) slice, size_t[N] lengths...)
    if (N)
{
    mixin _DefineRet;
    assert(lengths.lengthsProduct == slice.length, "elements count mismatch");
    foreach (i; Iota!N)
        ret._lengths[i] = lengths[i];
    foreach (i; Iota!(slice.N - 1))
        ret._lengths[N + i] = slice._lengths[i + 1];
    static if (kind != Contiguous)
    {
        foreach (i; Iota!(slice.S - 1))
            ret._strides[N + i] = slice._strides[i + 1];
        auto stride = slice._strides[0];
        foreach_reverse (i; Iota!N)
        {
            ret._strides[i] = stride;
            static if(i)
                stride *= lengths[i];
        }
    }
    ret._iterator = slice._iterator;
    return ret;
}

///
pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    auto data = new int[24];
    foreach (int i,ref e; data)
        e = i;
    auto a = data[0..10].sliced(10)[0..6].sliced(2, 3);
    auto b = iota!int(10)[0..6].sliced(2, 3);
    assert(a == b);
    a[] += b;
    foreach (int i, e; data[0..6])
        assert(e == 2*i);
    foreach (int i, e; data[6..$])
        assert(e == i+6);
    auto c  = data.sliced(12, 2)[0..6].sliced(2, 3);
    auto d  = iota(12, 2)[0..6].sliced(2, 3);
    auto cc = data[0..12].sliced(2, 3, 2);
    auto dc = iota(2, 3, 2);
    assert(c._lengths == cc._lengths);
    assert(c._strides == cc._strides);
    assert(d._lengths == dc._lengths);
    assert(d._strides == dc._strides);
    assert(cc == c);
    assert(dc == d);
    auto e = data.sliced(8, 3)[0..5].sliced(5);
    auto f = iota(8, 3)[0..5].sliced(5);
    assert(e == data[0..15].sliced(5, 3));
    assert(f == iota(5, 3));
}

/++
Creates an n-dimensional slice-shell over a field.
Params:
    field = A field. The length of the
        array should be equal to or less then the product of
        lengths. 
    lengths = A list of lengths for each dimension.
Returns:
    n-dimensional slice
+/
Slice!(Contiguous, [N], FieldIterator!Field)
slicedField(Field, size_t N)(Field field, size_t[N] lengths...)
    if (N)
{
    static if (hasLength!Field)
        assert(lengths.lengthsProduct <= field.length, "Length product should be less or equal to the field length.");
    return FieldIterator!Field(0, field).sliced(lengths);
}

///ditto
auto slicedField(Field)(Field field)
    if(hasLength!Field)
{
    return .slicedField(field, field.length);
}

/// Creates an 1-dimensional slice over a field, array, or random access range.
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    auto slice = 10.iota.slicedField;
    assert(slice.length == 10);
}

/++
Creates an n-dimensional slice-shell over an ndField.
Params:
    field = A ndField. Lengths should fit into field's shape.
    lengths = A list of lengths for each dimension.
Returns:
    n-dimensional slice
See_also: $(SUBREF concatenation, concatenation) examples.
+/
Slice!(Contiguous, [N], IndexIterator!(FieldIterator!(ndIotaField!N), ndField))
slicedNdField(ndField, size_t N)(ndField field, size_t[N] lengths...)
    if (N)
{
    static if(hasShape!ndField)
    {
        auto shape = field.shape;
        foreach (i; 0 .. N)
            assert(lengths[i] <= shape[i], "Lengths should fit into ndfield's shape.");
    }
    import mir.ndslice.topology: indexed, ndiota;
    return indexed(field, ndiota(lengths));
}

///ditto
auto slicedNdField(ndField)(ndField field)
    if(hasShape!ndField)
{
    return .slicedNdField(field, field.shape);
}


/++
Returns the element type of a $(LREF Slice).
+/
alias DeepElementType(S : Slice!(kind, packs, Iterator), SliceKind kind, size_t[] packs, Iterator) = S.DeepElemType;
/// ditto
alias DeepElementType(S : Concatenation!(dim, Slices), size_t dim, Slices...) = S.DeepElemType;

///
unittest
{
    import mir.ndslice.topology : iota;
    static assert(is(DeepElementType!(Slice!(Universal, [4], const(int)[]))     == const(int)));
    static assert(is(DeepElementType!(Slice!(Universal, [4], immutable(int)*))  == immutable(int)));
}

/++
Presents $(LREF .Slice.structure).
+/
struct Structure(size_t N)
{
    ///
    size_t[N] lengths;
    ///
    sizediff_t[N] strides;
}


/++
Presents an n-dimensional view over a range.

$(H3 Definitions)

In order to change data in a slice using
overloaded operators such as `=`, `+=`, `++`,
a syntactic structure of type
`<slice to change>[<index and interval sequence...>]` must be used.
It is worth noting that just like for regular arrays, operations `a = b`
and `a[] = b` have different meanings.
In the first case, after the operation is carried out, `a` simply points at the same data as `b`
does, and the data which `a` previously pointed at remains unmodified.
Here, `а` and `b` must be of the same type.
In the second case, `a` points at the same data as before,
but the data itself will be changed. In this instance, the number of dimensions of `b`
may be less than the number of dimensions of `а`; and `b` can be a Slice,
a regular multidimensional array, or simply a value (e.g. a number).

In the following table you will find the definitions you might come across
in comments on operator overloading.

$(BOOKTABLE
$(TR $(TH Operator Overloading) $(TH Examples at `N == 3`))
$(TR $(TD An $(B interval) is a part of a sequence of type `i .. j`.)
    $(STD `2..$-3`, `0..4`))
$(TR $(TD An $(B index) is a part of a sequence of type `i`.)
    $(STD `3`, `$-1`))
$(TR $(TD A $(B partially defined slice) is a sequence composed of
    $(B intervals) and $(B indexes) with an overall length strictly less than `N`.)
    $(STD `[3]`, `[0..$]`, `[3, 3]`, `[0..$,0..3]`, `[0..$,2]`))
$(TR $(TD A $(B fully defined index) is a sequence
    composed only of $(B indexes) with an overall length equal to `N`.)
    $(STD `[2,3,1]`))
$(TR $(TD A $(B fully defined slice) is an empty sequence
    or a sequence composed of $(B indexes) and at least one
    $(B interval) with an overall length equal to `N`.)
    $(STD `[]`, `[3..$,0..3,0..$-1]`, `[2,0..$,1]`))
$(TR $(TD An $(B indexed slice) is syntax sugar for $(SUBREF topology, indexed) and $(SUBREF topology, cartesian).)
    $(STD `[anNdslice]`, `[$.iota, anNdsliceForCartesian1, $.iota]`))
)

See_also:
    $(SUBREF topology, iota).

$(H3 Internal Binary Representation)

Multidimensional Slice is a structure that consists of lengths, strides, and a iterator (pointer).

$(SUBREF topology, FieldIterator) shell is used to wrap fields and random access ranges.
FieldIterator contains a shift of the current initial element of a multidimensional slice
and the field itself.

With the exception of $(MREF mir,ndslice,allocation) module, no functions in this
package move or copy data. The operations are only carried out on lengths, strides,
and pointers. If a slice is defined over a range, only the shift of the initial element
changes instead of the range.

$(H4 Internal Representation for Universal Slices)

Type definition

-------
Slice!(Universal, [N], Iterator)
-------

Schema

-------
Slice!(Universal, [N], Iterator)
    size_t[N]     _lengths
    sizediff_t[N] _strides
    Iterator      _iterator
-------

$(H5 Example)

Definitions

-------
import mir.ndslice;
auto a = new double[24];
Slice!(Universal, [3], double*) s = a.sliced(2, 3, 4).universal;
Slice!(Universal, [3], double*) t = s.transposed!(1, 2, 0);
Slice!(Universal, [3], double*) r = t.reversed!1;
-------

Representation

-------
s________________________
    lengths[0] ::=  2
    lengths[1] ::=  3
    lengths[2] ::=  4

    strides[0] ::= 12
    strides[1] ::=  4
    strides[2] ::=  1

    iterator        ::= &a[0]

t____transposed!(1, 2, 0)
    lengths[0] ::=  3
    lengths[1] ::=  4
    lengths[2] ::=  2

    strides[0] ::=  4
    strides[1] ::=  1
    strides[2] ::= 12

    iterator        ::= &a[0]

r______________reversed!1
    lengths[0] ::=  2
    lengths[1] ::=  3
    lengths[2] ::=  4

    strides[0] ::= 12
    strides[1] ::= -4
    strides[2] ::=  1

    iterator        ::= &a[8] // (old_strides[1] * (lengths[1] - 1)) = 8
-------

$(H4 Internal Representation for Canonical Slices)

Type definition

-------
Slice!(Canonical, [N], Iterator)
-------

Schema

-------
Slice!(Universal, [N], Iterator)
    size_t[N]       _lengths
    sizediff_t[N-1] _strides
    Iterator        _iterator
-------

$(H4 Internal Representation for Contiguous Slices)

Type definition

-------
Slice!(Contiguous, [N], Iterator)
-------

Schema

-------
Slice!(Universal, [N], Iterator)
    size_t[N]     _lengths
    sizediff_t[0] _strides
    Iterator      _iterator
-------
+/
struct Slice(SliceKind kind, size_t[] packs, Iterator)
    if (packs.sum < 255 && !(kind == Canonical && packs == [1]))
{
    @fastmath:

    package(mir):

    ///
    enum N = packs.sum;

    ///
    enum S = kind == Universal ? N : kind == Canonical ? N - 1 : 0;

    ///
    alias This = Slice!(kind, packs, Iterator);

    ///
    alias PureThis = Slice!(kind, [N], Iterator);

    enum doUnittest = is(Iterator == int*) && N == 1 && kind == Universal;

    template ElemType(size_t dimension)
        if (dimension < packs[0])
    {
        static if (N == 1)
            alias ElemType = typeof(Iterator.init[size_t.init]);
        else
        static if (kind == Universal || dimension == N - 1)
            alias ElemType = Slice!(Universal, packs.decDim, Iterator);
        else
        static if (N == 2 || kind == Contiguous && dimension == 0)
            alias ElemType = Slice!(Contiguous, packs.decDim, Iterator);
        else
            alias ElemType = Slice!(Canonical, packs.decDim, Iterator);
    }

    static if (packs.length == 1)
        alias DeepElemType = typeof(Iterator.init[size_t.init]);
    else
    static if (packs.length == 2 && packs[1] == 1 && kind == Canonical)
        alias DeepElemType = Slice!(Contiguous, packs[1 .. $], Iterator);
    else
        alias DeepElemType = Slice!(kind, packs[1 .. $], Iterator);

    enum hasAccessByRef = __traits(compiles, &_iterator[0]);

    enum PureIndexLength(Slices...) = Filter!(isIndex, Slices).length;

    enum isPureSlice(Slices...) =
        Slices.length <= packs[0]
        && PureIndexLength!Slices < packs[0]
        && allSatisfy!(templateOr!(isIndex, is_Slice), Slices);

    enum isFullPureSlice(Slices...) =
           Slices.length == 0
        || Slices.length == packs[0]
        && PureIndexLength!Slices < packs[0]
        && allSatisfy!(templateOr!(isIndex, is_Slice), Slices);

    enum isIndexedSlice(Slices...) =
           Slices.length
        && Slices.length <= packs[0]
        && allSatisfy!(templateOr!isSlice, Slices);

    ///
    public size_t[N] _lengths;
    ///
    public ptrdiff_t[S] _strides;
    ///
    public Iterator _iterator;

    sizediff_t backIndex(size_t dimension = 0)() @property const
        if (dimension < packs[0])
    {
        return _stride!dimension * (_lengths[dimension] - 1);
    }

    size_t indexStride(size_t I)(size_t[I] _indexes...) const
    {
        static if (_indexes.length)
        {
            static if (kind == Contiguous)
            {
                enum E = I - 1;
                assert(_indexes[E] < _lengths[E], indexError!(E, N));
                ptrdiff_t ball = this._stride!E;
                ptrdiff_t stride = _indexes[E] * ball;
                foreach_reverse (i; Iota!E) //static
                {
                    ball *= _lengths[i + 1];
                    assert(_indexes[i] < _lengths[i], indexError!(i, N));
                    stride += ball * _indexes[i];
                }
            }
            else
            static if (kind == Canonical)
            {
                enum E = I - 1;
                assert(_indexes[E] < _lengths[E], indexError!(E, N));
                static if (I == N)
                    size_t stride = _indexes[E];
                else
                    size_t stride = _strides[E] * _indexes[E];
                foreach_reverse (i; Iota!E) //static
                {
                    assert(_indexes[i] < _lengths[i], indexError!(i, N));
                    stride += _strides[i] * _indexes[i];
                }
            }
            else
            {
                enum E = I - 1;
                assert(_indexes[E] < _lengths[E], indexError!(E, N));
                size_t stride = _strides[E] * _indexes[E];
                foreach_reverse (i; Iota!E) //static
                {
                    assert(_indexes[i] < _lengths[i], indexError!(i, N));
                    stride += _strides[i] * _indexes[i];
                }
            }
            return stride;
        }
        else
        {
            return 0;
        }
    }

    public:

    /// Creates a 2-dimentional slice with custom strides.
    nothrow pure
    unittest
    {
        uint[8] array = [1, 2, 3, 4, 5, 6, 7, 8];
        auto slice = Slice!(Universal, [2], uint*)([2, 2], [4, 1], array.ptr);

        assert(&slice[0, 0] == &array[0]);
        assert(&slice[0, 1] == &array[1]);
        assert(&slice[1, 0] == &array[4]);
        assert(&slice[1, 1] == &array[5]);
        assert(slice == [[1, 2], [5, 6]]);

        array[2] = 42;
        assert(slice == [[1, 2], [5, 6]]);

        array[1] = 99;
        assert(slice == [[1, 99], [5, 6]]);
    }

    static if (isPointer!Iterator)
    {
        private alias ConstThis = Slice!(kind, packs, const(Unqual!(PointerTarget!Iterator))*);

        static if (!is(ConstThis == This))
        {
            /++
            Implicit cast to const slices in case of underlaying range is a pointer.
            +/
            ref ConstThis toConst()() const @trusted pure nothrow @nogc
            {
                pragma(inline, true);
                return *cast(ConstThis*) &this;
            }

            /// ditto
            alias toConst this;
        }
    }

    static if (doUnittest)
    ///
    unittest
    {
        Slice!(Universal, [2], double*) nn;
        Slice!(Universal, [2], immutable(double)*) ni;
        Slice!(Universal, [2], const(double)*) nc;

        const Slice!(Universal, [2], double*) cn;
        const Slice!(Universal, [2], immutable(double)*) ci;
        const Slice!(Universal, [2], const(double)*) cc;

        immutable Slice!(Universal, [2], double*) in_;
        immutable Slice!(Universal, [2], immutable(double)*) ii;
        immutable Slice!(Universal, [2], const(double)*) ic;

        nc = nc; nc = cn; nc = in_;
        nc = nc; nc = cc; nc = ic;
        nc = ni; nc = ci; nc = ii;

        void fun(size_t[] packs, T)(Slice!(Universal, packs, const(T)*) sl)
        {
            //...
        }

        fun(nn); fun(cn); fun(in_);
        fun(nc); fun(cc); fun(ic);
        fun(ni); fun(ci); fun(ii);
    }

    static if (doUnittest)
    unittest
    {
        Slice!(Universal, [2, 2], double*) nn;
        Slice!(Universal, [2, 2], immutable(double)*) ni;
        Slice!(Universal, [2, 2], const(double)*) nc;

        const Slice!(Universal, [2, 2], double*) cn;
        const Slice!(Universal, [2, 2], immutable(double)*) ci;
        const Slice!(Universal, [2, 2], const(double)*) cc;

        immutable Slice!(Universal, [2, 2], double*) in_;
        immutable Slice!(Universal, [2, 2], immutable(double)*) ii;
        immutable Slice!(Universal, [2, 2], const(double)*) ic;

        nc = nc; nc = cn; nc = in_;
        nc = nc; nc = cc; nc = ic;
        nc = ni; nc = ci; nc = ii;

        void fun(size_t[] packs, T)(Slice!(Universal, packs, const(T)*) sl)
        {
            //...
        }

        fun(nn); fun(cn); fun(in_);
        fun(nc); fun(cc); fun(ic);
        fun(ni); fun(ci); fun(ii);
    }

    /++
    Iterator
    Returns:
        Iterator (pointer) to the $(LREF Slice.first) element.
    +/
    auto iterator()() @property
    {
        return _iterator;
    }

    /++
    Field (array) data.
    Returns:
        Raw data slice.
    Constraints:
        Field is defined only for contiguous slices.
    +/
    auto field()() @property
    {
        static assert(kind == Contiguous, "Slice.field is defined only for contiguous slices. Slice kind is " ~ kind.stringof);
        static if (is(typeof(_iterator[size_t(0) .. elementsCount])))
        {
            return _iterator[size_t(0) .. elementsCount];
        }
        else
        {
            import mir.ndslice.topology: flattened;
            return this.flattened;
        }
    }

    /++
    Returns: static array of lengths
    See_also: $(LREF .Slice.structure)
    +/
    size_t[packs[0]] shape()() @property const
    {
        return _lengths[0 .. packs[0]];
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : iota;
        assert(iota(3, 4, 5).shape == cast(size_t[3])[3, 4, 5]);
    }

    static if (doUnittest)
    /// Packed slice
    @safe @nogc pure nothrow
    unittest
    {
        import mir.ndslice.topology : pack, iota;
        size_t[3] s = [3, 4, 5];
        assert(iota(3, 4, 5, 6, 7).pack!2.shape == s);
    }

    /++
    Returns: static array of lengths
    See_also: $(LREF .Slice.structure)
    +/
    ptrdiff_t[packs[0]] strides()() @property const
    {
        static if (packs[0] <= S)
            return _strides[0 .. packs[0]];
        else
        {
            typeof(return) ret;
            static if (kind == Canonical)
            {
                foreach (i; Iota!S)
                    ret[i] = _strides[i];
                ret[$-1] = 1;
            }
            else
            {
                ret[$ - 1] = _stride!(packs[0] - 1);
                foreach_reverse (i; Iota!(packs[0] - 1))
                    ret[i] = ret[i + 1] * _lengths[i + 1];
            }
            return ret;
        }
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow
    unittest
    {
        import mir.ndslice.topology : iota;
        size_t[3] s = [20, 5, 1];
        assert(iota(3, 4, 5).strides == s);
    }

    static if (doUnittest)
    /// Modified regular slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : pack, iota, universal;
        import mir.ndslice.dynamic : reversed, strided, transposed;
        assert(iota(3, 4, 50)
            .universal
            .reversed!2      //makes stride negative
            .strided!2(6)    //multiplies stride by 6 and changes corresponding length
            .transposed!2    //brings dimension `2` to the first position
            .strides == cast(ptrdiff_t[3])[-6, 200, 50]);
    }

    static if (doUnittest)
    /// Packed slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : pack, iota;
        size_t[3] s = [20 * 42, 5 * 42, 1 * 42];
        assert(iota(3, 4, 5, 6, 7)
            .pack!2
            .strides == s);
    }

    /++
    Returns: static array of lengths and static array of strides
    See_also: $(LREF .Slice.shape)
   +/
    Structure!(packs[0]) structure()() @property const
    {
        return typeof(return)(_lengths[0 .. packs[0]], strides);
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : iota;
        assert(iota(3, 4, 5)
            .structure == Structure!3([3, 4, 5], [20, 5, 1]));
    }

    static if (doUnittest)
    /// Modified regular slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : pack, iota, universal;
        import mir.ndslice.dynamic : reversed, strided, transposed;
        assert(iota(3, 4, 50)
            .universal
            .reversed!2      //makes stride negative
            .strided!2(6)    //multiplies stride by 6 and changes corresponding length
            .transposed!2    //brings dimension `2` to the first position
            .structure == Structure!3([9, 3, 4], [-6, 200, 50]));
    }

    static if (doUnittest)
    /// Packed slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : pack, iota;
        assert(iota(3, 4, 5, 6, 7)
            .pack!2
            .structure == Structure!3([3, 4, 5], [20 * 42, 5 * 42, 1 * 42]));
    }

    /++
    Save primitive.
    +/
    auto save()() @property
    {
        return this;
    }

    static if (doUnittest)
    /// Save range
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : iota;
        auto slice = iota(2, 3).save;
    }

    static if (doUnittest)
    /// Pointer type.
    pure nothrow unittest
    {
        import mir.ndslice.allocation;
        //sl type is `Slice!(2, int*)`
        auto sl = slice!int(2, 3).save;
    }


    /++
    Multidimensional `length` property.
    Returns: length of the corresponding dimension
    See_also: $(LREF .Slice.shape), $(LREF .Slice.structure)
    +/
    size_t length(size_t dimension = 0)() @property const
        if (dimension < packs[0])
    {
        return _lengths[dimension];
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : iota;
        auto slice = iota(3, 4, 5);
        assert(slice.length   == 3);
        assert(slice.length!0 == 3);
        assert(slice.length!1 == 4);
        assert(slice.length!2 == 5);
    }

    alias opDollar = length;

    /++
        Multidimensional `stride` property.
        Returns: stride of the corresponding dimension
        See_also: $(LREF .Slice.structure)
    +/
    sizediff_t _stride(size_t dimension = 0)() @property const
        if (dimension < packs[0])
    {
        static if (dimension < S)
        {
            return _strides[dimension];
        }
        else
        static if (dimension + 1 == N)
        {
            return 1;
        }
        else
        {
            size_t ball = _lengths[$ - 1];
            foreach_reverse(i; Iota!(dimension + 1, N - 1))
                ball *= _lengths[i];
            return ball;
        }

    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : iota;
        auto slice = iota(3, 4, 5);
        assert(slice._stride   == 20);
        assert(slice._stride!0 == 20);
        assert(slice._stride!1 == 5);
        assert(slice._stride!2 == 1);
    }

    static if (doUnittest)
    /// Modified regular slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.dynamic : reversed, strided, swapped;
        import mir.ndslice.topology : universal, iota;
        assert(iota(3, 4, 50)
            .universal
            .reversed!2      //makes stride negative
            .strided!2(6)    //multiplies stride by 6 and changes the corresponding length
            .swapped!(1, 2)  //swaps dimensions `1` and `2`
            ._stride!1 == -6);
    }

    /++
    Multidimensional input range primitive.
    +/
    bool empty(size_t dimension = 0)()
    @property const
        if (dimension < packs[0])
    {
        return _lengths[dimension] == 0;
    }

    ///ditto
    auto ref front(size_t dimension = 0)() @property
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (N == 1)
        {
            return *_iterator;
        }
        else
        {
            static if (hasElaborateAssign!Iterator)
                ElemType!dimension ret;
            else
                ElemType!dimension ret = ElemType!dimension.init;

            foreach (i; Iota!(ret.N))
            {
                enum j = i >= dimension ? i + 1 : i;
                ret._lengths[i] = _lengths[j];
            }

            static if (!ret.S || ret.S + 1 == S)
                alias s =_strides;
            else
                auto s = strides;

            foreach (i; Iota!(ret.S))
            {
                enum j = i >= dimension ? i + 1 : i;
                ret._strides[i] = s[j];
            }

            ret._iterator = _iterator;
            return ret;
        }
    }

    static if (N == 1 && isMutable!DeepElemType && !hasAccessByRef)
    {
        ///ditto
        auto ref front(size_t dimension = 0, T)(auto ref T value) @property
            if (dimension == 0)
        {
            assert(!empty!dimension);
            static if (__traits(compiles, *_iterator = value))
                return *_iterator = value;
            else
                return _iterator[0] = value;
        }
    }

    ///ditto
    auto ref back(size_t dimension = 0)() @property
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (N == 1)
        {
            return _iterator[backIndex];
        }
        else
        {
            static if (hasElaborateAssign!Iterator)
                ElemType!dimension ret;
            else
                ElemType!dimension ret = ElemType!dimension.init;

            foreach (i; Iota!(ret.N))
            {
                enum j = i >= dimension ? i + 1 : i;
                ret._lengths[i] = _lengths[j];
            }

            static if (!ret.S || ret.S + 1 == S)
                alias s =_strides;
            else
                auto s = strides;

            foreach (i; Iota!(ret.S))
            {
                enum j = i >= dimension ? i + 1 : i;
                ret._strides[i] = s[j];
            }

            ret._iterator = _iterator;
            ret._iterator += backIndex!dimension;
            return ret;
        }
    }

    static if (N == 1 && isMutable!DeepElemType && !hasAccessByRef)
    {
        ///ditto
        auto ref back(size_t dimension = 0, T)(auto ref T value) @property
            if (dimension == 0)
        {
            assert(!empty!dimension);
            return _iterator[backIndex] = value;
        }
    }

    ///ditto
    void popFront(size_t dimension = 0)()
        if (dimension < packs[0] && (dimension == 0 || kind != Contiguous))
    {
        assert(_lengths[dimension], __FUNCTION__ ~ ": length!" ~ dimension.stringof ~ " should be greater than 0.");
        _lengths[dimension]--;
        static if ((kind == Contiguous || kind == Canonical) && dimension + 1 == N)
            ++_iterator;
        else
        static if (kind == Canonical || kind == Universal)
            _iterator += _strides[dimension];
        else
            _iterator += _stride!dimension;
    }

    ///ditto
    void popBack(size_t dimension = 0)()
        if (dimension < packs[0] && (dimension == 0 || kind != Contiguous))
    {
        assert(_lengths[dimension], __FUNCTION__ ~ ": length!" ~ dimension.stringof ~ " should be greater than 0.");
        --_lengths[dimension];
    }

    ///ditto
    void popFrontExactly(size_t dimension = 0)(size_t n)
        if (dimension < packs[0] && (dimension == 0 || kind != Contiguous))
    {
        assert(n <= _lengths[dimension],
            __FUNCTION__ ~ ": n should be less than or equal to length!" ~ dimension.stringof);
        _lengths[dimension] -= n;
        _iterator += _stride!dimension * n;
    }

    ///ditto
    void popBackExactly(size_t dimension = 0)(size_t n)
        if (dimension < packs[0] && (dimension == 0 || kind != Contiguous))
    {
        assert(n <= _lengths[dimension],
            __FUNCTION__ ~ ": n should be less than or equal to length!" ~ dimension.stringof);
        _lengths[dimension] -= n;
    }

    ///ditto
    void popFrontN(size_t dimension = 0)(size_t n)
        if (dimension < packs[0] && (dimension == 0 || kind != Contiguous))
    {
        import mir.utility : min;
        popFrontExactly!dimension(min(n, _lengths[dimension]));
    }

    ///ditto
    void popBackN(size_t dimension = 0)(size_t n)
        if (dimension < packs[0] && (dimension == 0 || kind != Contiguous))
    {
        import mir.utility : min;
        popBackExactly!dimension(min(n, _lengths[dimension]));
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow unittest
    {
        import std.range.primitives;
        import mir.ndslice.topology : iota, canonical;
        auto slice = iota(10, 20, 30).canonical;

        static assert(isRandomAccessRange!(typeof(slice)));
        static assert(hasSlicing!(typeof(slice)));
        static assert(hasLength!(typeof(slice)));

        assert(slice.shape == cast(size_t[3])[10, 20, 30]);
        slice.popFront;
        slice.popFront!1;
        slice.popBackExactly!2(4);
        assert(slice.shape == cast(size_t[3])[9, 19, 26]);

        auto matrix = slice.front!1;
        assert(matrix.shape == cast(size_t[2])[9, 26]);

        auto column = matrix.back!1;
        assert(column.shape == cast(size_t[1])[9]);

        slice.popFrontExactly!1(slice.length!1);
        assert(slice.empty   == false);
        assert(slice.empty!1 == true);
        assert(slice.empty!2 == false);
        assert(slice.shape == cast(size_t[3])[9, 0, 26]);

        assert(slice.back.front!1.empty);

        slice.popFrontN!0(40);
        slice.popFrontN!2(40);
        assert(slice.shape == cast(size_t[3])[0, 0, 0]);
    }

    package(mir) ptrdiff_t lastIndex()() const @property
    {
        static if (kind == Contiguous)
        {
            return elementsCount - 1;
        }
        else
        {
            auto strides = strides;
            ptrdiff_t shift = 0;
            foreach(i; Iota!(packs[0]))
                shift += strides[i] * (_lengths[i] - 1);
            return shift;
        }
    }

    static if (packs[0] > 1)
    {
        /// Accesses the first deep element of the slice.
        auto ref first()() @property
        {
            assert(!anyEmpty);
            static if (packs.length == 1)
                return *_iterator;
            else
                static if (S)
                    return DeepElemType(_lengths[packs[0] .. $], _strides[packs[0] .. $], _iterator);
                else
                    return DeepElemType(_lengths[packs[0] .. $], _strides, _iterator);
        }

        static if (isMutable!DeepElemType && !hasAccessByRef)
        ///ditto
        auto ref first(T)(auto ref T value) @property
        {
            assert(!anyEmpty);
            static if (__traits(compiles, *_iterator = value))
                return *_iterator = value;
            else
                return _iterator[0] = value;
        }

        ///
        unittest
        {
            import mir.ndslice.topology: iota, universal, canonical;
            auto f = 5;
            assert([2, 3].iota(f).first == f);
        }

        /// Accesses the last deep element of the slice.
        auto ref last()() @property
        {
            assert(!anyEmpty);
            import mir.ndslice.topology: retro;
            static if (packs.length == 1)
                return _iterator[lastIndex];
            else
                static if (S)
                    return DeepElemType(_lengths[packs[0] .. $], _strides[packs[0] .. $], _iterator + lastIndex);
                else
                    return DeepElemType(_lengths[packs[0] .. $], _strides, _iterator + lastIndex);
        }

        static if (isMutable!DeepElemType && !hasAccessByRef)
        ///ditto
        auto ref last(T)(auto ref T value) @property
        {
            assert(!anyEmpty);
            return _iterator[lastIndex] = value;
        }

        ///
        unittest
        {
            import mir.ndslice.topology: iota;
            auto f = 5;
            assert([2, 3].iota(f).last == f + 2 * 3 - 1);
        }
    }
    else
    {
        alias first = front;
        alias last = back;
    }

    /++
    Returns: `true` if for any dimension the length equals to `0`, and `false` otherwise.
    +/
    bool anyEmpty()() const
    {
        foreach (i; Iota!(packs[0]))
            if (_lengths[i] == 0)
                return true;
        return false;
    }

    static if (doUnittest)
    ///
    unittest
    {
        import mir.ndslice.topology : iota, canonical;
        auto s = iota(2, 3).canonical;
        assert(!s.anyEmpty);
        s.popFrontExactly!1(3);
        assert(s.anyEmpty);
    }

    /++
    Convenience function for backward indexing.

    Returns: `this[$-index[0], $-index[1], ..., $-index[N-1]]`
    +/
    auto ref backward()(size_t[packs[0]] index)
    {
        foreach (i; Iota!(packs[0]))
            index[i] = _lengths[i] - index[i];
        return this[index];
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : iota;
        auto s = iota(2, 3);
        assert(s[$ - 1, $ - 2] == s.backward([1, 2]));
    }

    /++
    Returns: Total number of elements in a slice
    +/
    size_t elementsCount() const
    {
        size_t len = 1;
        foreach (i; Iota!(packs[0]))
            len *= _lengths[i];
        return len;
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : iota;
        assert(iota(3, 4, 5).elementsCount == 60);
    }


    static if (doUnittest)
    /// Packed slice
    @safe @nogc pure nothrow unittest
    {
        import mir.ndslice.topology : pack, evertPack, iota;
        auto slice = iota(3, 4, 5, 6, 7, 8);
        auto p = slice.pack!2;
        assert(p.elementsCount == 360);
        assert(p[0, 0, 0, 0].elementsCount == 56);
        assert(p.evertPack.elementsCount == 56);
    }

    /++
    Overloading `==` and `!=`
    +/
    bool opEquals(SliceKind rkind, size_t[] rpacks, IteratorR)(const Slice!(rkind, rpacks, IteratorR) rslice) const
        if (rpacks.sum == N)
    {
        foreach (i; Iota!N)
            if (this._lengths[i] != rslice._lengths[i])
                return false;
        static if (
               !hasReference!(typeof(this))
            && !hasReference!(typeof(rslice))
            && __traits(compiles, this._iterator == rslice._iterator)
            )
        {
            if (this._strides == rslice._strides && this._iterator == rslice._iterator)
                return true;
        }
        import mir.ndslice.topology : unpack;
        if ((cast(This)this).unpack.anyEmpty)
                return true;
        static if (N > 1 && kind == Contiguous && rkind == Contiguous)
        {
            import mir.ndslice.topology : flattened;
            return opEqualsImpl((cast(This)this).unpack.flattened, rslice.unpack.flattened);
        }
        else
            return opEqualsImpl((cast(This)this).unpack, (cast(rslice.This)rslice).unpack);
    }

    ///ditto
    bool opEquals(T)(T[] arr) const
    {
        auto slice = cast(This)this;
        if (slice.length != arr.length)
            return false;
        if (arr.length) do
        {
            if (slice.front != arr[0])
                return false;
            slice.popFront;
            arr = arr[1 .. $];
        }
        while (arr.length);
        return true;
    }

    static if (doUnittest)
    ///
    pure nothrow
    unittest
    {
        auto a = [1, 2, 3, 4].sliced(2, 2);

        assert(a != [1, 2, 3, 4, 5, 6].sliced(2, 3));
        assert(a != [[1, 2, 3], [4, 5, 6]]);

        assert(a == [1, 2, 3, 4].sliced(2, 2));
        assert(a == [[1, 2], [3, 4]]);

        assert(a != [9, 2, 3, 4].sliced(2, 2));
        assert(a != [[9, 2], [3, 4]]);
    }

    static if (doUnittest)
    pure nothrow unittest
    {
        import mir.ndslice.allocation: slice;
        import mir.ndslice.topology : iota;
        assert(iota(2, 3).slice[0 .. $ - 2] == iota([4, 3], 2)[0 .. $ - 4]);
    }

    _Slice!() opSlice(size_t dimension)(size_t i, size_t j) const
        if (dimension < packs[0])
    in
    {
        assert(i <= j,
            "Slice.opSlice!" ~ dimension.stringof ~ ": the left bound must be less than or equal to the right bound.");
        enum errorMsg = ": difference between the right and the left bounds"
                        ~ " must be less than or equal to the length of the given dimension.";
        assert(j - i <= _lengths[dimension],
              "Slice.opSlice!" ~ dimension.stringof ~ errorMsg);
    }
    body
    {
        return typeof(return)(i, j);
    }

    /++
    $(BOLD Fully defined index)
    +/
    auto ref opIndex(size_t I)(size_t[I] _indexes...)
        if (I && I <= packs[0])
    {
        static if (I == N)
            return _iterator[indexStride(_indexes)];
        else
        {
            static if (I == packs[0])
                static if (S)
                    return DeepElemType(_lengths[packs[0] .. $], _strides[packs[0] .. $], _iterator + indexStride(_indexes));
                else
                    return DeepElemType(_lengths[packs[0] .. $], _strides, _iterator + indexStride(_indexes));
            else
            {
                enum size_t diff = packs[0] - I;
                alias Ret = Slice!(
                    diff == 1 && kind == Canonical ?
                        Contiguous:
                        kind,
                    diff ~ packs[1 .. $],
                    Iterator);
                static if (S)
                    return Ret(_lengths[I .. N], _strides[I .. S], _iterator + indexStride(_indexes));
                else
                    return Ret(_lengths[I .. N], _strides, _iterator + indexStride(_indexes));
            }
        }

    }

    /++
    $(BOLD Partially or fully defined slice.)
    +/
    auto opIndex(Slices...)(Slices slices)
        if (isPureSlice!Slices)
    {
        static if (Slices.length)
        {
            enum size_t j(size_t n) = n - Filter!(isIndex, Slices[0 .. n]).length;
            enum size_t F = PureIndexLength!Slices;
            enum size_t S = Slices.length;
            static assert(N - F > 0);
            size_t stride;
            static if (Slices.length == 1)
                enum K = kind;
            else
            static if (kind == Universal || Slices.length == N && isIndex!(Slices[$-1]))
                enum K = Universal;
            else
            static if (Filter!(isIndex, Slices[0 .. $-1]).length == Slices.length - 1 || N - F == 1)
                enum K = Contiguous;
            else
                enum K = Canonical;
            alias Ret = Slice!(K, (packs[0] - F) ~ packs[1 .. $], Iterator);
            mixin _DefineRet_;
            enum bool shrink = kind == Canonical && slices.length == N;
            static if (shrink)
            {
                {
                    enum i = Slices.length - 1;
                    auto slice = slices[i];
                    static if (isIndex!(Slices[i]))
                    {
                        assert(slice < _lengths[i], "Slice.opIndex: index must be less than length");
                        stride += slice;
                    }
                    else
                    {
                        stride += slice.i;
                        ret._lengths[j!i] = slice.j - slice.i;
                    }
                }
            }
            static if (kind == Universal || kind == Canonical)
            {
                foreach_reverse (i, slice; slices[0 .. $ - shrink]) //static
                {
                    static if (isIndex!(Slices[i]))
                    {
                        assert(slice < _lengths[i], "Slice.opIndex: index must be less than length");
                        stride += _strides[i] * slice;
                    }
                    else
                    {
                        stride += _strides[i] * slice.i;
                        ret._lengths[j!i] = slice.j - slice.i;
                        ret._strides[j!i] = _strides[i];
                    }
                }
            }
            else
            {
                ptrdiff_t ball = this._stride!(slices.length - 1);
                foreach_reverse (i, slice; slices) //static
                {
                    static if (isIndex!(Slices[i]))
                    {
                        assert(slice < _lengths[i], "Slice.opIndex: index must be less than length");
                        stride += ball * slice;
                    }
                    else
                    {
                        stride += ball * slice.i;
                        ret._lengths[j!i] = slice.j - slice.i;
                        static if (j!i < ret.S)
                            ret._strides[j!i] = ball;
                    }
                    static if (i)
                        ball *= _lengths[i];
                }
            }
            foreach (i; Iota!(Slices.length, N))
                ret._lengths[i - F] = _lengths[i];
            
            foreach (i; Iota!(Slices.length, N))
                static if (ret.S > i - F)
                    ret._strides[i - F] = _strides[i];
            ret._iterator = _iterator;
            ret._iterator += stride;
            return ret;
        }
        else
        {
            return this;
        }
    }

    static if (doUnittest)
    ///
    pure nothrow unittest
    {
        import mir.ndslice.allocation;
        auto slice = slice!int(5, 3);

        /// Fully defined slice
        assert(slice[] == slice);
        auto sublice = slice[0..$-2, 1..$];

        /// Partially defined slice
        auto row = slice[3];
        auto col = slice[0..$, 1];
    }

    /++
    $(BOLD Indexed slice.)
    +/
    auto opIndex(Slices...)(Slices slices)
        if (isIndexedSlice!Slices)
    {
        import mir.ndslice.topology: indexed, cartesian, map;
        static if (Slices.length == 1)
            alias index = slices[0];
        else
            auto index = slices.cartesian;
        return this.indexed(index);
    }

    ///
    pure nothrow unittest
    {
        import mir.ndslice.allocation: slice;
        auto sli = slice!int(4, 3);
        auto idx = slice!(size_t[2])(3);
        idx[] = [
            cast(size_t[2])[0, 2],
            cast(size_t[2])[3, 1],
            cast(size_t[2])[2, 0]];

        // equivalent to:
        // import mir.ndslice.topology: indexed;
        // sli.indexed(indx)[] = 1;
        sli[idx][] = 1;

        assert(sli == [
            [0, 0, 1],
            [0, 0, 0],
            [1, 0, 0],
            [0, 1, 0],
            ]);

        foreach (row; sli[[1, 3].sliced])
            row[] += 2;

        assert(sli == [
            [0, 0, 1],
            [2, 2, 2], // <--  += 2
            [1, 0, 0],
            [2, 3, 2], // <--  += 2
            ]);
    }

    ///
    pure nothrow unittest
    {
        import mir.ndslice.topology: iota;
        import mir.ndslice.allocation: slice;
        auto sli = slice!int(5, 6);

        // equivalent to
        // import mir.ndslice.topology: indexed, cartesian;
        // auto a = [0, sli.length!0 / 2, sli.length!0 - 1].sliced;
        // auto b = [0, sli.length!1 / 2, sli.length!1 - 1].sliced;
        // auto c = cartesian(a, b);
        // auto minor = sli.indexed(c);
        auto minor = sli[[0, $ / 2, $ - 1].sliced, [0, $ / 2, $ - 1].sliced];

        minor[] = iota([3, 3], 1);

        assert(sli == [
        //   ↓     ↓        ↓︎
            [1, 0, 0, 2, 0, 3], // <---
            [0, 0, 0, 0, 0, 0],
            [4, 0, 0, 5, 0, 6], // <---
            [0, 0, 0, 0, 0, 0],
            [7, 0, 0, 8, 0, 9], // <---
            ]);
    }

    static if (isMutable!(PureThis.DeepElemType))
    {
        private void opIndexOpAssignImplSlice(string op, SliceKind rkind, size_t[] rpacks, RIterator)(Slice!(rkind, rpacks, RIterator) value)
        {
            static if (N > 1 && rpacks == packs && kind == Contiguous && rkind == Contiguous)
            {
                import mir.ndslice.topology : flattened;
                this.flattened.opIndexOpAssignImplSlice!op(value.flattened);
            }
            else
            {
                auto ls = this;
                do
                {
                    static if (packs[0] > rpacks[0])
                    {
                        ls.front.opIndexOpAssignImplSlice!op(value);
                    }
                    else
                    {
                        static if (ls.N == 1)
                            mixin("ls.front " ~ op ~ "= value.front;");
                        else
                        static if (rpacks == [1])
                            ls.front.opIndexOpAssignImplValue!op(value.front);
                        else
                            ls.front.opIndexOpAssignImplSlice!op(value.front);
                        value.popFront;
                    }
                    ls.popFront;
                }
                while (ls._lengths[0]);
            }
        }

        /++
        Assignment of a value of `Slice` type to a $(B fully defined slice).
        +/
        void opIndexAssign(SliceKind rkind, size_t[] rpacks, RIterator, Slices...)(Slice!(rkind, rpacks, RIterator) value, Slices slices)
            if (isFullPureSlice!Slices)
        {
            auto sl = this[slices];
            assert(_checkAssignLengths(sl, value));
            import mir.ndslice.topology: unpack;
            if(!sl.unpack.anyEmpty)
                sl.opIndexOpAssignImplSlice!""(value);
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);
            auto b = [1, 2, 3, 4].sliced(2, 2);

            a[0..$, 0..$-1] = b;
            assert(a == [[1, 2, 0], [3, 4, 0]]);

            // fills both rows with b[0]
            a[0..$, 0..$-1] = b[0];
            assert(a == [[1, 2, 0], [1, 2, 0]]);

            a[1, 0..$-1] = b[1];
            assert(a[1] == [3, 4, 0]);

            a[1, 0..$-1][] = b[0];
            assert(a[1] == [1, 2, 0]);
        }

        static if (doUnittest)
        /// Left slice is packed
        pure nothrow unittest
        {
            import mir.ndslice.topology : blocks, iota;
            import mir.ndslice.allocation : slice;
            auto a = slice!int(4, 4);
            a.blocks(2, 2)[] = iota!int(2, 2);

            assert(a ==
                    [[0, 0, 1, 1],
                     [0, 0, 1, 1],
                     [2, 2, 3, 3],
                     [2, 2, 3, 3]]);
        }

        static if (doUnittest)
        /// Both slices are packed
        pure nothrow unittest
        {
            import mir.ndslice.topology : blocks, iota, pack;
            import mir.ndslice.allocation : slice;
            auto a = slice!int(4, 4);
            a.blocks(2, 2)[] = iota!int(2, 2, 2).pack!1;

            assert(a ==
                    [[0, 1, 2, 3],
                     [0, 1, 2, 3],
                     [4, 5, 6, 7],
                     [4, 5, 6, 7]]);
        }

        void opIndexOpAssignImplArray(string op, T, Slices...)(T[] value)
        {
            auto ls = this;
            assert(ls.length == value.length, __FUNCTION__ ~ ": argument must have the same length.");
            static if (packs[0] == 1)
            {
                do
                {
                    static if (ls.N == 1)
                        mixin("ls.front " ~ op ~ "= value[0];");
                    else
                        mixin("ls.front[] " ~ op ~ "= value[0];");
                    value = value[1 .. $];
                    ls.popFront;
                }
                while (ls.length);
            }
            else
            static if (packs[0] == DynamicArrayDimensionsCount!(T[]))
            {
                do
                {
                    ls.front.opIndexOpAssignImplArray!op(value[0]);
                    value = value[1 .. $];
                    ls.popFront;
                }
                while (ls.length);
            }
            else
            {
                do
                {
                    ls.front.opIndexOpAssignImplArray!op(value);
                    ls.popFront;
                }
                while (ls.length);
            }
        }

        /++
        Assignment of a regular multidimensional array to a $(B fully defined slice).
        +/
        void opIndexAssign(T, Slices...)(T[] value, Slices slices)
            if (isFullPureSlice!Slices
                && !isDynamicArray!DeepElemType
                && DynamicArrayDimensionsCount!(T[]) <= ReturnType!(opIndex!Slices).N)
        {
            this[slices].opIndexOpAssignImplArray!""(value);
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);
            auto b = [[1, 2], [3, 4]];

            a[] = [[1, 2, 3], [4, 5, 6]];
            assert(a == [[1, 2, 3], [4, 5, 6]]);

            a[0..$, 0..$-1] = [[1, 2], [3, 4]];
            assert(a == [[1, 2, 3], [3, 4, 6]]);

            a[0..$, 0..$-1] = [1, 2];
            assert(a == [[1, 2, 3], [1, 2, 6]]);

            a[1, 0..$-1] = [3, 4];
            assert(a[1] == [3, 4, 6]);

            a[1, 0..$-1][] = [3, 4];
            assert(a[1] == [3, 4, 6]);
        }

        static if (doUnittest)
        /// Packed slices
        pure nothrow unittest
        {
            import mir.ndslice.allocation : slice;
            import mir.ndslice.topology : blocks;
            auto a = slice!int(4, 4);
            a.blocks(2, 2)[] = [[0, 1], [2, 3]];

            assert(a ==
                    [[0, 0, 1, 1],
                     [0, 0, 1, 1],
                     [2, 2, 3, 3],
                     [2, 2, 3, 3]]);
        }


        private void opIndexOpAssignImplConcatenation(string op, T)(T value)
        {
            auto sl = this;
            static if (concatenationDimension!T)
            {
                if (!sl.empty) do
                {
                    mixin(`sl.front[] ` ~ op ~ `= value.front;`);
                    value.popFront;
                    sl.popFront;
                }
                while(!sl.empty);
            }
            else
            {
                foreach (ref slice; value._slices)
                {
                    mixin("sl[0 .. slice.length][] " ~ op ~ "= slice;");
                    sl = sl[slice.length .. $];
                }
                assert(sl.empty);
            }
        }

        ///
        void opIndexAssign(T, Slices...)(T concatenation, Slices slices)
            if (isFullPureSlice!Slices && isConcatenation!T)
        {
            import mir.ndslice.topology : unpack;
            auto sl = this[slices].unpack;
            static assert(isSlice!(typeof(sl))[0] == concatenation.N);
            sl.opIndexOpAssignImplConcatenation!""(concatenation);
        }

        /++
        Assignment of a value (e.g. a number) to a $(B fully defined slice).
        +/
        void opIndexAssign(T, Slices...)(T value, Slices slices)
            if (isFullPureSlice!Slices
                && (!isDynamicArray!T || isDynamicArray!DeepElemType)
                && !isSlice!T
                && !isConcatenation!T)
        {
            import mir.ndslice.topology : unpack;
            auto sl = this[slices].unpack;
            if(!sl.anyEmpty)
                sl.opIndexOpAssignImplValue!""(value);
        }

        static if (doUnittest)
        ///
        pure nothrow
        unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            a[] = 9;
            assert(a == [[9, 9, 9], [9, 9, 9]]);

            a[0..$, 0..$-1] = 1;
            assert(a == [[1, 1, 9], [1, 1, 9]]);

            a[0..$, 0..$-1] = 2;
            assert(a == [[2, 2, 9], [2, 2, 9]]);

            a[1, 0..$-1] = 3;
            //assert(a[1] == [3, 3, 9]);

            a[1, 0..$-1] = 4;
            //assert(a[1] == [4, 4, 9]);

            a[1, 0..$-1][] = 5;

            assert(a[1] == [5, 5, 9]);
        }

        static if (doUnittest)
        /// Packed slices have the same behavior.
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            import mir.ndslice.topology : pack;
            auto a = slice!int(2, 3).pack!1;

            a[] = 9;
            //assert(a == [[9, 9, 9], [9, 9, 9]]);
        }

        static if (packs.length == 1)
        /++
        Assignment of a value (e.g. a number) to a $(B fully defined index).
        +/
        auto ref opIndexAssign(T)(T value, size_t[N] _indexes...)
        {
            return _iterator[indexStride(_indexes)] = value;
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            a[1, 2] = 3;
            assert(a[1, 2] == 3);
        }

        static if (doUnittest)
        pure nothrow unittest
        {
            auto a = new int[6].sliced(2, 3);

            a[[1, 2]] = 3;
            assert(a[[1, 2]] == 3);
        }

        static if (packs.length == 1)
        /++
        Op Assignment `op=` of a value (e.g. a number) to a $(B fully defined index).
        +/
        auto ref opIndexOpAssign(string op, T)(T value, size_t[N] _indexes...)
        {
            return mixin (`_iterator[indexStride(_indexes)] ` ~ op ~ `= value`);
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            a[1, 2] += 3;
            assert(a[1, 2] == 3);
        }

        static if (doUnittest)
        pure nothrow unittest
        {
            auto a = new int[6].sliced(2, 3);

            a[[1, 2]] += 3;
            assert(a[[1, 2]] == 3);
        }

        /++
        Op Assignment `op=` of a value of `Slice` type to a $(B fully defined slice).
        +/
        void opIndexOpAssign(string op, SliceKind kind, size_t[] rpacks, RIterator, Slices...)
            (Slice!(kind, rpacks, RIterator) value, Slices slices)
            if (isFullPureSlice!Slices)
        {
            auto sl = this[slices];
            assert(_checkAssignLengths(sl, value));
            import mir.ndslice.topology: unpack;
            if(!sl.unpack.anyEmpty)
                sl.opIndexOpAssignImplSlice!op(value);
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);
            auto b = [1, 2, 3, 4].sliced(2, 2);

            a[0..$, 0..$-1] += b;
            assert(a == [[1, 2, 0], [3, 4, 0]]);

            a[0..$, 0..$-1] += b[0];
            assert(a == [[2, 4, 0], [4, 6, 0]]);

            a[1, 0..$-1] += b[1];
            assert(a[1] == [7, 10, 0]);

            a[1, 0..$-1][] += b[0];
            assert(a[1] == [8, 12, 0]);
        }

        static if (doUnittest)
        /// Left slice is packed
        pure nothrow unittest
        {
            import mir.ndslice.allocation : slice;
            import mir.ndslice.topology : blocks, iota;
            auto a = slice!size_t(4, 4);
            a.blocks(2, 2)[] += iota(2, 2);

            assert(a ==
                    [[0, 0, 1, 1],
                     [0, 0, 1, 1],
                     [2, 2, 3, 3],
                     [2, 2, 3, 3]]);
        }

        static if (doUnittest)
        /// Both slices are packed
        pure nothrow unittest
        {
            import mir.ndslice.allocation : slice;
            import mir.ndslice.topology : blocks, iota, pack;
            auto a = slice!size_t(4, 4);
            a.blocks(2, 2)[] += iota(2, 2, 2).pack!1;

            assert(a ==
                    [[0, 1, 2, 3],
                     [0, 1, 2, 3],
                     [4, 5, 6, 7],
                     [4, 5, 6, 7]]);
        }

        /++
        Op Assignment `op=` of a regular multidimensional array to a $(B fully defined slice).
        +/
        void opIndexOpAssign(string op, T, Slices...)(T[] value, Slices slices)
            if (isFullPureSlice!Slices
                && !isDynamicArray!DeepElemType
                && DynamicArrayDimensionsCount!(T[]) <= ReturnType!(opIndex!Slices).N)
        {
            this[slices].opIndexOpAssignImplArray!op(value);
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation : slice;
            auto a = slice!int(2, 3);

            a[0..$, 0..$-1] += [[1, 2], [3, 4]];
            assert(a == [[1, 2, 0], [3, 4, 0]]);

            a[0..$, 0..$-1] += [1, 2];
            assert(a == [[2, 4, 0], [4, 6, 0]]);

            a[1, 0..$-1] += [3, 4];
            assert(a[1] == [7, 10, 0]);

            a[1, 0..$-1][] += [1, 2];
            assert(a[1] == [8, 12, 0]);
        }

        static if (doUnittest)
        /// Packed slices
        pure nothrow 
        unittest
        {
            import mir.ndslice.allocation : slice;
            import mir.ndslice.topology : blocks;
            auto a = slice!int(4, 4);
            a.blocks(2, 2)[].opIndexOpAssign!"+"([[0, 1], [2, 3]]);

            assert(a ==
                    [[0, 0, 1, 1],
                     [0, 0, 1, 1],
                     [2, 2, 3, 3],
                     [2, 2, 3, 3]]);
        }

        private void opIndexOpAssignImplValue(string op, T)(T value)
        {
            static if (N > 1 && kind == Contiguous)
            {
                import mir.ndslice.topology : flattened;
                this.flattened.opIndexOpAssignImplValue!op(value);
            }
            else
            {
                auto sl = this;
                do
                {
                    static if (N == 1)
                        mixin (`sl.front ` ~ op ~ `= value;`);
                    else
                        sl.front.opIndexOpAssignImplValue!op(value);
                    sl.popFront;
                }
                while(sl._lengths[0]);
            }
        }

        /++
        Op Assignment `op=` of a value (e.g. a number) to a $(B fully defined slice).
       +/
        void opIndexOpAssign(string op, T, Slices...)(T value, Slices slices)
            if (isFullPureSlice!Slices
                && (!isDynamicArray!T || isDynamicArray!DeepElemType)
                && !isSlice!T
                && !isConcatenation!T)
        {
            import mir.ndslice.topology : unpack;
            auto sl = this[slices].unpack;
            if(!sl.anyEmpty)
                sl.opIndexOpAssignImplValue!op(value);
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            a[] += 1;
            assert(a == [[1, 1, 1], [1, 1, 1]]);

            a[0..$, 0..$-1] += 2;
            assert(a == [[3, 3, 1], [3, 3, 1]]);

            a[1, 0..$-1] += 3;
            assert(a[1] == [6, 6, 1]);
        }

        ///
        void opIndexOpAssign(string op,T, Slices...)(T concatenation, Slices slices)
            if (isFullPureSlice!Slices && isConcatenation!T)
        {
            import mir.ndslice.topology : unpack;
            auto sl = this[slices].unpack;
            static assert(isSlice!(typeof(sl))[0] == concatenation.N);
            sl.opIndexOpAssignImplConcatenation!op(concatenation);
        }

        static if (doUnittest)
        /// Packed slices have the same behavior.
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            import mir.ndslice.topology : pack;
            auto a = slice!int(2, 3).pack!1;

            a[] += 9;
            assert(a == [[9, 9, 9], [9, 9, 9]]);
        }

        static if (packs.length == 1)
        /++
        Increment `++` and Decrement `--` operators for a $(B fully defined index).
        +/
        auto ref opIndexUnary(string op)(size_t[N] _indexes...)
            // @@@workaround@@@ for Issue 16473
            //if (op == `++` || op == `--`)
        {
            return mixin (op ~ `_iterator[indexStride(_indexes)]`);
        }

        static if (doUnittest)
        ///
        pure nothrow unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            ++a[1, 2];
            assert(a[1, 2] == 1);
        }

        // Issue 16473
        static if (doUnittest)
        unittest
        {
            import mir.ndslice.allocation;
            auto sl = slice!double(2, 5);
            auto d = -sl[0, 1];
        }

        static if (doUnittest)
        pure nothrow unittest
        {
            auto a = new int[6].sliced(2, 3);

            ++a[[1, 2]];
            assert(a[[1, 2]] == 1);
        }

        private void opIndexUnaryImpl(string op, Slices...)(Slices slices)
        {
            auto sl = this;
            do
            {
                static if (N == 1)
                    mixin (op ~ `sl.front;`);
                else
                    sl.front.opIndexUnaryImpl!op;
                sl.popFront;
            }
            while(sl._lengths[0]);
        }

        static if (packs.length == 1)
        /++
        Increment `++` and Decrement `--` operators for a $(B fully defined slice).
        +/
        void opIndexUnary(string op, Slices...)(Slices slices)
            if (isFullPureSlice!Slices && (op == `++` || op == `--`))
        {
            import mir.ndslice.topology: unpack;
            auto sl = this[slices].unpack;
            if (!sl.anyEmpty)
                sl.opIndexUnaryImpl!op;
        }

        static if (doUnittest)
        ///
        pure nothrow
        unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            ++a[];
            assert(a == [[1, 1, 1], [1, 1, 1]]);

            --a[1, 0..$-1];

            assert(a[1] == [0, 0, 1]);
        }
    }
}

/++
Slicing, indexing, and arithmetic operations.
+/
pure nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.dynamic : transposed;
    import mir.ndslice.topology : iota, universal;
    auto tensor = iota(3, 4, 5).slice;

    assert(tensor[1, 2] == tensor[1][2]);
    assert(tensor[1, 2, 3] == tensor[1][2][3]);

    assert( tensor[0..$, 0..$, 4] == tensor.universal.transposed!2[4]);
    assert(&tensor[0..$, 0..$, 4][1, 2] is &tensor[1, 2, 4]);

    tensor[1, 2, 3]++; //`opIndex` returns value by reference.
    --tensor[1, 2, 3]; //`opUnary`

    ++tensor[];
    tensor[] -= 1;

    // `opIndexAssing` accepts only fully defined indexes and slices.
    // Use an additional empty slice `[]`.
    static assert(!__traits(compiles, tensor[0 .. 2] *= 2));

    tensor[0 .. 2][] *= 2;          //OK, empty slice
    tensor[0 .. 2, 3, 0..$] /= 2; //OK, 3 index or slice positions are defined.

    //fully defined index may be replaced by a static array
    size_t[3] index = [1, 2, 3];
    assert(tensor[index] == tensor[1, 2, 3]);
}

/++
Operations with rvalue slices.
+/
pure nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.topology: universal;
    import mir.ndslice.dynamic: transposed, everted;

    auto tensor = slice!int(3, 4, 5).universal;
    auto matrix = slice!int(3, 4).universal;
    auto vector = slice!int(3);

    foreach (i; 0..3)
        vector[i] = i;

    // fills matrix columns
    matrix.transposed[] = vector;

    // fills tensor with vector
    // transposed tensor shape is (4, 5, 3)
    //            vector shape is (      3)
    tensor.transposed!(1, 2)[] = vector;


    // transposed tensor shape is (5, 3, 4)
    //            matrix shape is (   3, 4)
    tensor.transposed!2[] += matrix;

    // transposed tensor shape is (5, 4, 3)
    // transposed matrix shape is (   4, 3)
    tensor.everted[] ^= matrix.transposed; // XOR
}

/++
Creating a slice from text.
See also $(MREF std, format).
+/
unittest
{
    import mir.ndslice.allocation;
    import std.algorithm,  std.conv, std.exception, std.format,
        std.functional, std.string, std.range;

    Slice!(Contiguous, [2], int*) toMatrix(string str)
    {
        string[][] data = str.lineSplitter.filter!(not!empty).map!split.array;

        size_t rows    = data   .length.enforce("empty input");
        size_t columns = data[0].length.enforce("empty first row");

        data.each!(a => enforce(a.length == columns, "rows have different lengths"));
        auto slice = slice!int(rows, columns);
        foreach (i, line; data)
            foreach (j, num; line)
                slice[i, j] = num.to!int;
        return slice;
    }

    auto input = "\r1 2  3\r\n 4 5 6\n";

    auto matrix = toMatrix(input);
    assert(matrix == [[1, 2, 3], [4, 5, 6]]);

    // back to text
    auto text2 = format("%(%(%s %)\n%)\n", matrix);
    assert(text2 == "1 2 3\n4 5 6\n");
}

// Slicing
@safe @nogc pure nothrow unittest
{
    import mir.ndslice.topology : iota;
    auto a = iota(10, 20, 30, 40);
    auto b = a[0..$, 10, 4 .. 27, 4];
    auto c = b[2 .. 9, 5 .. 10];
    auto d = b[3..$, $-2];
    assert(b[4, 17] == a[4, 10, 21, 4]);
    assert(c[1, 2] == a[3, 10, 11, 4]);
    assert(d[3] == a[6, 10, 25, 4]);
}

// Operator overloading. # 1
pure nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.topology : iota;

    auto fun(ref size_t x) { x *= 3; }

    auto tensor = iota(8, 9, 10).slice;

    ++tensor[];
    fun(tensor[0, 0, 0]);

    assert(tensor[0, 0, 0] == 3);

    tensor[0, 0, 0] *= 4;
    tensor[0, 0, 0]--;
    assert(tensor[0, 0, 0] == 11);
}

// Operator overloading. # 2
pure nothrow unittest
{
    import std.algorithm.iteration : map;
    import std.array : array;
    import std.bigint;
    import std.range : iota;

    auto matrix = 72
        .iota
        .map!(i => BigInt(i))
        .array
        .sliced(8, 9);

    matrix[3 .. 6, 2] += 100;
    foreach (i; 0 .. 8)
        foreach (j; 0 .. 9)
            if (i >= 3 && i < 6 && j == 2)
                assert(matrix[i, j] >= 100);
            else
                assert(matrix[i, j] < 100);
}

// Operator overloading. # 3
pure nothrow unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.topology : iota;

    auto matrix = iota(8, 9).slice;
    matrix[] = matrix;
    matrix[] += matrix;
    assert(matrix[2, 3] == (2 * 9 + 3) * 2);

    auto vec = iota([9], 100);
    matrix[] = vec;
    foreach (v; matrix)
        assert(v == vec);

    matrix[] += vec;
    foreach (vector; matrix)
        foreach (elem; vector)
            assert(elem >= 200);
}

// Type deduction
unittest
{
    // Arrays
    foreach (T; AliasSeq!(int, const int, immutable int))
        static assert(is(typeof((T[]).init.sliced(3, 4)) == Slice!(Contiguous, [2], T*)));

    // Container Array
    import std.container.array;
    Array!int ar;
    ar.length = 12;
    Slice!(Contiguous, [2], typeof(ar[])) arSl = ar[].sliced(3, 4);
}

// Test for map #1
unittest
{
    import std.algorithm.iteration : map;
    import std.range.primitives;
    auto slice = [1, 2, 3, 4].sliced(2, 2);

    auto r = slice.map!(a => a.map!(a => a * 6));
    assert(r.front.front == 6);
    assert(r.front.back == 12);
    assert(r.back.front == 18);
    assert(r.back.back == 24);
    assert(r[0][0] ==  6);
    assert(r[0][1] == 12);
    assert(r[1][0] == 18);
    assert(r[1][1] == 24);
    static assert(hasSlicing!(typeof(r)));
    static assert(isForwardRange!(typeof(r)));
    static assert(isRandomAccessRange!(typeof(r)));
}

// Test for map #2
unittest
{
    import std.algorithm.iteration : map;
    import std.range.primitives;
    auto data = [1, 2, 3, 4]
        //.map!(a => a * 2)
        ;
    static assert(hasSlicing!(typeof(data)));
    static assert(isForwardRange!(typeof(data)));
    static assert(isRandomAccessRange!(typeof(data)));
    auto slice = data.sliced(2, 2);
    static assert(hasSlicing!(typeof(slice)));
    static assert(isForwardRange!(typeof(slice)));
    static assert(isRandomAccessRange!(typeof(slice)));
    auto r = slice.map!(a => a.map!(a => a * 6));
    static assert(hasSlicing!(typeof(r)));
    static assert(isForwardRange!(typeof(r)));
    static assert(isRandomAccessRange!(typeof(r)));
    assert(r.front.front == 6);
    assert(r.front.back == 12);
    assert(r.back.front == 18);
    assert(r.back.back == 24);
    assert(r[0][0] ==  6);
    assert(r[0][1] == 12);
    assert(r[1][0] == 18);
    assert(r[1][1] == 24);
}

private bool opEqualsImpl
    (SliceKind lkind, SliceKind rkind, size_t[] packs, LIterator, RIterator)
    (Slice!(lkind, packs, LIterator) ls, Slice!(rkind, packs, RIterator) rs)
{
    do
    {
        static if (packs[0] == 1)
        {
            if (*ls._iterator != *rs._iterator)
                return false;
        }
        else
        {
            if (!opEqualsImpl(ls.front, rs.front))
                return false;
        }
        rs.popFront;
        ls.popFront;
    }
    while (ls._lengths[0]);
    return true;
}

private enum bool isType(alias T) = false;

private enum bool isType(T) = true;

private enum isStringValue(alias T) = is(typeof(T) : string);


private bool _checkAssignLengths(
    SliceKind lkind, SliceKind rkind,
    size_t[] rpacks, size_t[] lpacks,
    LIterator, RIterator)
    (Slice!(lkind, lpacks, LIterator) ls,
     Slice!(rkind, rpacks, RIterator) rs)
    if (lpacks[0] >= rpacks[0])
{
    foreach (i; Iota!(0, rpacks[0]))
        if (ls._lengths[i + lpacks[0] - rpacks[0]] != rs._lengths[i])
            return false;

    static if (ls.N > lpacks[0] && rs.N > rpacks[0])
    {
        ls.DeepElemType a;
        rs.DeepElemType b;
        a._lengths = ls._lengths[lpacks[0] .. $];
        b._lengths = rs._lengths[rpacks[0] .. $];
        return _checkAssignLengths(a, b);
    }
    else
    {
        return true;
    }
}

@safe pure nothrow @nogc unittest
{
    import mir.ndslice.topology : iota;

    assert(_checkAssignLengths(iota(2, 2), iota(2, 2)));
    assert(!_checkAssignLengths(iota(2, 2), iota(2, 3)));
    assert(!_checkAssignLengths(iota(2, 2), iota(3, 2)));
    assert(!_checkAssignLengths(iota(2, 2), iota(3, 3)));
}

pure nothrow unittest
{
    auto slice = new int[15].slicedField(5, 3);

    /// Fully defined slice
    assert(slice[] == slice);
    auto sublice = slice[0..$-2, 1..$];

    /// Partially defined slice
    auto row = slice[3];
    auto col = slice[0..$, 1];
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);
    auto b = [1, 2, 3, 4].sliced(2, 2);

    a[0..$, 0..$-1] = b;
    assert(a == [[1, 2, 0], [3, 4, 0]]);

    a[0..$, 0..$-1] = b[0];
    assert(a == [[1, 2, 0], [1, 2, 0]]);

    a[1, 0..$-1] = b[1];
    assert(a[1] == [3, 4, 0]);

    a[1, 0..$-1][] = b[0];
    assert(a[1] == [1, 2, 0]);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);
    auto b = [[1, 2], [3, 4]];

    a[] = [[1, 2, 3], [4, 5, 6]];
    assert(a == [[1, 2, 3], [4, 5, 6]]);

    a[0..$, 0..$-1] = [[1, 2], [3, 4]];
    assert(a == [[1, 2, 3], [3, 4, 6]]);

    a[0..$, 0..$-1] = [1, 2];
    assert(a == [[1, 2, 3], [1, 2, 6]]);

    a[1, 0..$-1] = [3, 4];
    assert(a[1] == [3, 4, 6]);

    a[1, 0..$-1][] = [3, 4];
    assert(a[1] == [3, 4, 6]);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[] = 9;
    //assert(a == [[9, 9, 9], [9, 9, 9]]);

    a[0..$, 0..$-1] = 1;
    //assert(a == [[1, 1, 9], [1, 1, 9]]);

    a[0..$, 0..$-1] = 2;
    //assert(a == [[2, 2, 9], [2, 2, 9]]);

    a[1, 0..$-1] = 3;
    //assert(a[1] == [3, 3, 9]);

    a[1, 0..$-1] = 4;
    //assert(a[1] == [4, 4, 9]);

    a[1, 0..$-1][] = 5;
    //assert(a[1] == [5, 5, 9]);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[1, 2] = 3;
    assert(a[1, 2] == 3);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[[1, 2]] = 3;
    assert(a[[1, 2]] == 3);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[1, 2] += 3;
    assert(a[1, 2] == 3);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[[1, 2]] += 3;
    assert(a[[1, 2]] == 3);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);
    auto b = [1, 2, 3, 4].sliced(2, 2);

    a[0..$, 0..$-1] += b;
    assert(a == [[1, 2, 0], [3, 4, 0]]);

    a[0..$, 0..$-1] += b[0];
    assert(a == [[2, 4, 0], [4, 6, 0]]);

    a[1, 0..$-1] += b[1];
    assert(a[1] == [7, 10, 0]);

    a[1, 0..$-1][] += b[0];
    assert(a[1] == [8, 12, 0]);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[0..$, 0..$-1] += [[1, 2], [3, 4]];
    assert(a == [[1, 2, 0], [3, 4, 0]]);

    a[0..$, 0..$-1] += [1, 2];
    assert(a == [[2, 4, 0], [4, 6, 0]]);

    a[1, 0..$-1] += [3, 4];
    assert(a[1] == [7, 10, 0]);

    a[1, 0..$-1][] += [1, 2];
    assert(a[1] == [8, 12, 0]);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[] += 1;
    assert(a == [[1, 1, 1], [1, 1, 1]]);

    a[0..$, 0..$-1] += 2;
    assert(a == [[3, 3, 1], [3, 3, 1]]);

    a[1, 0..$-1] += 3;
    assert(a[1] == [6, 6, 1]);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    ++a[1, 2];
    assert(a[1, 2] == 1);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    ++a[[1, 2]];
    assert(a[[1, 2]] == 1);
}

pure nothrow unittest
{
    auto a = new int[6].slicedField(2, 3);

    ++a[];
    assert(a == [[1, 1, 1], [1, 1, 1]]);

    --a[1, 0..$-1];
    assert(a[1] == [0, 0, 1]);
}

unittest
{
    import mir.ndslice.topology: iota, universal;

    auto sl = iota(3, 4).universal;
    assert(sl[0 .. $] == sl);
}

unittest
{
    import mir.ndslice.topology: canonical, iota;
    static assert(kindOf!(typeof(iota([1, 2]).canonical[1])) == Contiguous);
}

unittest
{
    import mir.ndslice.topology: iota;
    auto s = iota(2, 3);
    assert(s.front!1 == [0, 3]);
    assert(s.back!1 == [2, 5]);
}
