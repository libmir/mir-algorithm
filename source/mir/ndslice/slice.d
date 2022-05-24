/++
This is a submodule of $(MREF mir, ndslice).

Safety_note:
    User-defined iterators should care about their safety except bounds checks.
    Bounds are checked in ndslice code.

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilya Yaroshenko

$(BOOKTABLE $(H2 Definitions),
$(TR $(TH Name) $(TH Description))
$(T2 Slice, N-dimensional slice.)
$(T2 SliceKind, SliceKind of $(LREF Slice) enumeration.)
$(T2 Universal, Alias for $(LREF .SliceKind.universal).)
$(T2 Canonical, Alias for $(LREF .SliceKind.canonical).)
$(T2 Contiguous, Alias for $(LREF .SliceKind.contiguous).)
$(T2 sliced, Creates a slice on top of an iterator, a pointer, or an array's pointer.)
$(T2 slicedField, Creates a slice on top of a field, a random access range, or an array.)
$(T2 slicedNdField, Creates a slice on top of an ndField.)
$(T2 kindOf, Extracts $(LREF SliceKind).)
$(T2 isSlice, Checks if the type is `Slice` instance.)
$(T2 Structure, A tuple of lengths and strides.)
)

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
STD = $(TD $(SMALL $0))
+/
module mir.ndslice.slice;

import mir.internal.utility : Iota;
import mir.math.common : optmath;
import mir.ndslice.concatenation;
import mir.ndslice.field;
import mir.ndslice.internal;
import mir.ndslice.iterator;
import mir.ndslice.traits: isIterator;
import mir.primitives;
import mir.qualifier;
import mir.utility;
import std.meta;
import std.traits;

///
public import mir.primitives: DeepElementType;

/++
Checks if type T has asSlice property and its returns a slices.
Aliases itself to a dimension count
+/
template hasAsSlice(T)
{
    static if (__traits(hasMember, T, "asSlice"))
        enum size_t hasAsSlice = typeof(T.init.asSlice).N;
    else
        enum size_t hasAsSlice = 0;
}

///
version(mir_ndslice_test) unittest
{
    import mir.series;
    static assert(!hasAsSlice!(int[]));
    static assert(hasAsSlice!(SeriesMap!(int, string)) == 1);
}

/++
Check if $(LREF toConst) function can be called with type T.
+/
enum isConvertibleToSlice(T) = isSlice!T || isDynamicArray!T || hasAsSlice!T;

///
version(mir_ndslice_test) unittest
{
    import mir.series: SeriesMap;
    static assert(isConvertibleToSlice!(immutable int[]));
    static assert(isConvertibleToSlice!(string[]));
    static assert(isConvertibleToSlice!(SeriesMap!(string, int)));
    static assert(isConvertibleToSlice!(Slice!(int*)));
}

/++
Reurns:
    Ndslice view in the same data.
See_also: $(LREF isConvertibleToSlice).
+/
auto toSlice(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) val)
{
    import core.lifetime: move;
    return val.move;
}

/// ditto
auto toSlice(Iterator, size_t N, SliceKind kind)(const Slice!(Iterator, N, kind) val)
{
    return val[];
}

/// ditto
auto toSlice(Iterator, size_t N, SliceKind kind)(immutable Slice!(Iterator, N, kind) val)
{
    return val[];
}

/// ditto
auto toSlice(T)(T[] val)
{
    return val.sliced;
}

/// ditto
auto toSlice(T)(T val)
    if (hasAsSlice!T || __traits(hasMember, T, "moveToSlice"))
{
    static if (__traits(hasMember, T, "moveToSlice"))
        return val.moveToSlice;
    else
        return val.asSlice;
}

/// ditto
auto toSlice(T)(ref T val)
    if (hasAsSlice!T)
{
    return val.asSlice;
}

///
template toSlices(args...)
{
    static if (args.length)
    {
        alias arg = args[0];
        alias Arg = typeof(arg);
        static if (isMutable!Arg && isSlice!Arg)
            alias slc = arg;
        else
        @optmath @property auto ref slc()()
        {
            return toSlice(arg);
        }
        alias toSlices = AliasSeq!(slc, toSlices!(args[1..$]));
    }
    else
        alias toSlices = AliasSeq!();
}

/++
Checks if the type is `Slice` instance.
+/
enum isSlice(T) = is(T : Slice!(Iterator, N, kind), Iterator, size_t N, SliceKind kind);

///
@safe pure nothrow @nogc
version(mir_ndslice_test) unittest
{
    alias A = uint[];
    alias S = Slice!(int*);

    static assert(isSlice!S);
    static assert(!isSlice!A);
}

/++
SliceKind of $(LREF Slice).
See_also:
    $(SUBREF topology, universal),
    $(SUBREF topology, canonical),
    $(SUBREF topology, assumeCanonical),
    $(SUBREF topology, assumeContiguous).
+/
enum mir_slice_kind
{
    /// A slice has strides for all dimensions.
    universal,
    /// A slice has >=2 dimensions and row dimension is contiguous.
    canonical,
    /// A slice is a flat contiguous data without strides.
    contiguous,
}
/// ditto
alias SliceKind = mir_slice_kind;

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
enum kindOf(T : Slice!(Iterator, N, kind), Iterator, size_t N, SliceKind kind) = kind;

///
@safe pure nothrow @nogc
version(mir_ndslice_test) unittest
{
    static assert(kindOf!(Slice!(int*, 1, Universal)) == Universal);
}

/// Extracts iterator type from a $(LREF Slice).
alias IteratorOf(T : Slice!(Iterator, N, kind), Iterator, size_t N, SliceKind kind) = Iterator;

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
    if (!__traits(isStaticArray, Iterator) && N
        && !is(Iterator : Slice!(_Iterator, _N, kind), _Iterator, size_t _N, SliceKind kind))
{
    alias C = ImplicitlyUnqual!(typeof(iterator));
    size_t[N] _lengths;
    foreach (i; Iota!N)
        _lengths[i] = lengths[i];
    ptrdiff_t[1] _strides = 0;
    static if (isDynamicArray!Iterator)
    {
        assert(lengthsProduct(_lengths) <= iterator.length,
            "array length should be greater or equal to the product of constructed ndslice lengths");
        auto ptr = iterator.length ? &iterator[0] : null;
        return Slice!(typeof(C.init[0])*, N)(_lengths, ptr);
    }
    else
    {
        // break safety
        if (false)
        {
            ++iterator;
            --iterator;
            iterator += 34;
            iterator -= 34;
        }
        import core.lifetime: move;
        return Slice!(C, N)(_lengths, iterator.move);
    }
}

/// Random access range primitives for slices over user defined types
@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    struct MyIota
    {
        //`[index]` operator overloading
        auto opIndex(size_t index) @safe nothrow
        {
            return index;
        }

        auto lightConst()() const @property { return MyIota(); }
        auto lightImmutable()() immutable @property { return MyIota(); }
    }

    import mir.ndslice.iterator: FieldIterator;
    alias Iterator = FieldIterator!MyIota;
    alias S = Slice!(Iterator, 2);
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
Slice!(T*) sliced(T)(T[] array) @trusted
{
    version(LDC) pragma(inline, true);
    return Slice!(T*)([array.length], array.ptr);
}

/// Creates a slice from an array.
@safe pure nothrow version(mir_ndslice_test) unittest
{
    auto slice = new int[10].sliced;
    assert(slice.length == 10);
    static assert(is(typeof(slice) == Slice!(int*)));
}

/++
Creates an n-dimensional slice-shell over the 1-dimensional input slice.
Params:
    slice = slice
    lengths = A list of lengths for each dimension.
Returns:
    n-dimensional slice
+/
Slice!(Iterator, N, kind)
    sliced
    (Iterator, size_t N, SliceKind kind)
    (Slice!(Iterator, 1, kind) slice, size_t[N] lengths...)
    if (N)
{
    auto structure = typeof(return)._Structure.init;
    structure[0] = lengths;
    static if (kind != Contiguous)
    {
        import mir.ndslice.topology: iota;
        structure[1] = structure[0].iota.strides;
    }
    import core.lifetime: move;
    return typeof(return)(structure, slice._iterator.move);
}

///
@safe pure nothrow version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology : iota;
    auto data = new int[24];
    foreach (i, ref e; data)
        e = cast(int)i;
    auto a = data[0..10].sliced(10)[0..6].sliced(2, 3);
    auto b = iota!int(10)[0..6].sliced(2, 3);
    assert(a == b);
    a[] += b;
    foreach (i, e; data[0..6])
        assert(e == 2*i);
    foreach (i, e; data[6..$])
        assert(e == i+6);
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
Slice!(FieldIterator!Field, N)
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
@safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
Slice!(IndexIterator!(FieldIterator!(ndIotaField!N), ndField), N)
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
Combination of coordinate(s) and value.
+/
struct CoordinateValue(T, size_t N = 1)
{
    ///
    size_t[N] index;

    ///
    T value;

    ///
    int opCmp()(scope auto ref const typeof(this) rht) const
    {
        return cmpCoo(this.index, rht.index);
    }
}

private int cmpCoo(size_t N)(scope const auto ref size_t[N] a, scope const auto ref size_t[N] b)
{
    foreach (i; Iota!(0, N))
        if (a[i] != b[i])
            return a[i] > b[i] ? 1 : -1;
    return 0;
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

package(mir) alias LightConstOfLightScopeOf(Iterator) = LightConstOf!(LightScopeOf!Iterator);
package(mir) alias LightImmutableOfLightConstOf(Iterator) = LightImmutableOf!(LightScopeOf!Iterator);
package(mir) alias ImmutableOfUnqualOfPointerTarget(Iterator) = immutable(Unqual!(PointerTarget!Iterator))*;
package(mir) alias ConstOfUnqualOfPointerTarget(Iterator) = const(Unqual!(PointerTarget!Iterator))*;

package(mir) template allLightScope(args...)
{
    static if (args.length)
    {
        alias Arg = typeof(args[0]);
        static if(!isDynamicArray!Arg)
        {
            static if(!is(LightScopeOf!Arg == Arg))
            @optmath @property auto allLightScopeMod()()
            {
                import mir.qualifier: lightScope;
                return args[0].lightScope;
            }
            else alias allLightScopeMod = args[0];
        }
        else alias allLightScopeMod = args[0];
        alias allLightScope = AliasSeq!(allLightScopeMod, allLightScope!(args[1..$]));
    }
    else
        alias allLightScope = AliasSeq!();
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
    $(B intervals) and $(B indices) with an overall length strictly less than `N`.)
    $(STD `[3]`, `[0..$]`, `[3, 3]`, `[0..$,0..3]`, `[0..$,2]`))
$(TR $(TD A $(B fully defined index) is a sequence
    composed only of $(B indices) with an overall length equal to `N`.)
    $(STD `[2,3,1]`))
$(TR $(TD A $(B fully defined slice) is an empty sequence
    or a sequence composed of $(B indices) and at least one
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

Mir n-dimensional Slices can be one of the three kinds.

$(H4 Contiguous slice)

Contiguous in memory (or in a user-defined iterator's field) row-major tensor that doesn't store strides because they can be computed on the fly using lengths.
The row stride is always equaled 1.

$(H4 Canonical slice)

Canonical slice as contiguous in memory (or in a user-defined iterator's field) rows of a row-major tensor, it doesn't store the stride for row dimension because it is always equaled 1.
BLAS/LAPACK matrices are Canonical but originally have column-major order.
In the same time you can use 2D Canonical Slices with LAPACK assuming that rows are columns and columns are rows.

$(H4 Universal slice)

A row-major tensor that stores the strides for all dimensions.
NumPy strides are Universal.

$(H4 Internal Representation for Universal Slices)

Type definition

-------
Slice!(Iterator, N, Universal)
-------

Schema

-------
Slice!(Iterator, N, Universal)
    size_t[N]     _lengths
    sizediff_t[N] _strides
    Iterator      _iterator
-------

$(H5 Example)

Definitions

-------
import mir.ndslice;
auto a = new double[24];
Slice!(double*, 3, Universal) s = a.sliced(2, 3, 4).universal;
Slice!(double*, 3, Universal) t = s.transposed!(1, 2, 0);
Slice!(double*, 3, Universal) r = t.reversed!1;
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
Slice!(Iterator, N, Canonical)
-------

Schema

-------
Slice!(Iterator, N, Canonical)
    size_t[N]       _lengths
    sizediff_t[N-1] _strides
    Iterator        _iterator
-------

$(H4 Internal Representation for Contiguous Slices)

Type definition

-------
Slice!(Iterator, N)
-------

Schema

-------
Slice!(Iterator, N, Contiguous)
    size_t[N]     _lengths
    sizediff_t[0] _strides
    Iterator      _iterator
-------
+/
struct mir_slice(Iterator_, size_t N_ = 1, SliceKind kind_ = Contiguous, Labels_...)
    if (0 < N_ && N_ < 255 && !(kind_ == Canonical && N_ == 1) && Labels_.length <= N_ && isIterator!Iterator_)
{
@optmath:

    /// $(LREF SliceKind)
    enum SliceKind kind = kind_;

    /// Dimensions count
    enum size_t N = N_;

    /// Strides count
    enum size_t S = kind == Universal ? N : kind == Canonical ? N - 1 : 0;

    /// Labels count.
    enum size_t L = Labels_.length;

    /// Data iterator type
    alias Iterator = Iterator_;

    /// This type
    alias This = Slice!(Iterator, N, kind);

    /// Data element type
    alias DeepElement = typeof(Iterator.init[size_t.init]);

    ///
    alias serdeKeysProxy = Unqual!DeepElement;

    /// Label Iterators types
    alias Labels = Labels_;

    ///
    template Element(size_t dimension)
        if (dimension < N)
    {
        static if (N == 1)
            alias Element = DeepElement;
        else
        {
            static if (kind == Universal || dimension == N - 1)
                alias Element = mir_slice!(Iterator, N - 1, Universal);
            else
            static if (N == 2 || kind == Contiguous && dimension == 0)
                alias Element = mir_slice!(Iterator, N - 1);
            else
                alias Element = mir_slice!(Iterator, N - 1, Canonical);
        }
    }

package(mir):

    enum doUnittest = is(Iterator == int*) && (N == 1 || N == 2) && kind == Contiguous;

    enum hasAccessByRef = __traits(compiles, &_iterator[0]);

    enum PureIndexLength(Slices...) = Filter!(isIndex, Slices).length;

    enum isPureSlice(Slices...) =
        Slices.length == 0
        || Slices.length <= N
        && PureIndexLength!Slices < N
        && Filter!(isIndex, Slices).length < Slices.length
        && allSatisfy!(templateOr!(isIndex, is_Slice), Slices);


    enum isFullPureSlice(Slices...) =
           Slices.length == 0
        || Slices.length == N
        && PureIndexLength!Slices < N
        && allSatisfy!(templateOr!(isIndex, is_Slice), Slices);

    enum isIndexedSlice(Slices...) =
           Slices.length
        && Slices.length <= N
        && allSatisfy!(isSlice, Slices)
        && anySatisfy!(templateNot!is_Slice, Slices);

    static if (S)
    {
        ///
        public alias _Structure = AliasSeq!(size_t[N], ptrdiff_t[S]);
        ///
        public _Structure _structure;
        ///
        public alias _lengths = _structure[0];
        ///
        public alias _strides = _structure[1];
    }
    else
    {
        ///
        public alias _Structure = AliasSeq!(size_t[N]);
        ///
        public _Structure _structure;
        ///
        public alias _lengths = _structure[0];
        ///
        public enum ptrdiff_t[S] _strides = ptrdiff_t[S].init;
    }

    /// Data Iterator
    public Iterator _iterator;
    /// Labels iterators
    public Labels _labels;

    sizediff_t backIndex(size_t dimension = 0)() @safe @property scope const
        if (dimension < N)
    {
        return _stride!dimension * (_lengths[dimension] - 1);
    }

    size_t indexStride(size_t I)(size_t[I] _indices) @safe scope const
    {
        static if (_indices.length)
        {
            static if (kind == Contiguous)
            {
                enum E = I - 1;
                assert(_indices[E] < _lengths[E], indexError!(E, N));
                ptrdiff_t ball = this._stride!E;
                ptrdiff_t stride = _indices[E] * ball;
                foreach_reverse (i; Iota!E) //static
                {
                    ball *= _lengths[i + 1];
                    assert(_indices[i] < _lengths[i], indexError!(i, N));
                    stride += ball * _indices[i];
                }
            }
            else
            static if (kind == Canonical)
            {
                enum E = I - 1;
                assert(_indices[E] < _lengths[E], indexError!(E, N));
                static if (I == N)
                    size_t stride = _indices[E];
                else
                    size_t stride = _strides[E] * _indices[E];
                foreach_reverse (i; Iota!E) //static
                {
                    assert(_indices[i] < _lengths[i], indexError!(i, N));
                    stride += _strides[i] * _indices[i];
                }
            }
            else
            {
                enum E = I - 1;
                assert(_indices[E] < _lengths[E], indexError!(E, N));
                size_t stride = _strides[E] * _indices[E];
                foreach_reverse (i; Iota!E) //static
                {
                    assert(_indices[i] < _lengths[i], indexError!(i, N));
                    stride += _strides[i] * _indices[i];
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

    // static if (S == 0)
    // {
        /// Defined for Contiguous Slice only
        // this()(size_t[N] lengths, in ptrdiff_t[] empty, Iterator iterator, Labels labels)
        // {
        //     version(LDC) pragma(inline, true);
        //     assert(empty.length == 0);
        //     this._lengths = lengths;
        //     this._iterator = iterator;
        // }

        // /// ditto
        // this()(size_t[N] lengths, Iterator iterator, Labels labels)
        // {
        //     version(LDC) pragma(inline, true);
        //     this._lengths = lengths;
        //     this._iterator = iterator;
        // }

        // /// ditto
        // this()(size_t[N] lengths, in ptrdiff_t[] empty, Iterator iterator, Labels labels)
        // {
        //     version(LDC) pragma(inline, true);
        //     assert(empty.length == 0);
        //     this._lengths = lengths;
        //     this._iterator = iterator;
        // }

        // /// ditto
        // this()(size_t[N] lengths, Iterator iterator, Labels labels)
        // {
        //     version(LDC) pragma(inline, true);
        //     this._lengths = lengths;
        //     this._iterator = iterator;
        // }
    // }

    // version(LDC)
    //     private enum classicConstructor = true;
    // else
    //     private enum classicConstructor = S > 0;

    // static if (classicConstructor)
    // {
        /// Defined for Canonical and Universal Slices (DMD, GDC, LDC) and for Contiguous Slices (LDC)
        // this()(size_t[N] lengths, ptrdiff_t[S] strides, Iterator iterator, Labels labels)
        // {
        //     version(LDC) pragma(inline, true);
        //     this._lengths = lengths;
        //     this._strides = strides;
        //     this._iterator = iterator;
        //     this._labels = labels;
        // }

        // /// ditto
        // this()(size_t[N] lengths, ptrdiff_t[S] strides, ref Iterator iterator, Labels labels)
        // {
        //     version(LDC) pragma(inline, true);
        //     this._lengths = lengths;
        //     this._strides = strides;
        //     this._iterator = iterator;
        //     this._labels = labels;
        // }
    // }

    // /// Construct from null
    // this()(typeof(null))
    // {
    //     version(LDC) pragma(inline, true);
    // }

    // static if (doUnittest)
    // ///
    // @safe pure version(mir_ndslice_test) unittest
    // {
    //     import mir.ndslice.slice;
    //     alias Array = Slice!(double*);
        // Array a = null;
        // auto b = Array(null);
        // assert(a.empty);
        // assert(b.empty);

        // auto fun(Array a = null)
        // {

        // }
    // }

    static if (doUnittest)
    /// Creates a 2-dimentional slice with custom strides.
    nothrow pure
    version(mir_ndslice_test) unittest
    {
        uint[8] array = [1, 2, 3, 4, 5, 6, 7, 8];
        auto slice = Slice!(uint*, 2, Universal)([2, 2], [4, 1], array.ptr);

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

    /++
    Returns: View with stripped out reference counted context.
    The lifetime of the result mustn't be longer then the lifetime of the original slice.
    +/
    auto lightScope()() return scope @property
    {
        auto ret = Slice!(LightScopeOf!Iterator, N, kind, staticMap!(LightScopeOf, Labels))
            (_structure, .lightScope(_iterator));
        foreach(i; Iota!L)
            ret._labels[i] = .lightScope(_labels[i]);
        return ret;
    }

    /// ditto
    auto lightScope()() return const scope @property
    {
        auto ret = Slice!(LightConstOf!(LightScopeOf!Iterator), N, kind, staticMap!(LightConstOfLightScopeOf, Labels))
            (_structure, .lightScope(_iterator));
        foreach(i; Iota!L)
            ret._labels[i] = .lightScope(_labels[i]);
        return ret;
    }

    /// ditto
    auto lightScope()() return immutable scope @property
    {
        auto ret =  Slice!(LightImmutableOf!(LightScopeOf!Iterator), N, kind, staticMap!(LightImmutableOfLightConstOf(Labels)))
            (_structure, .lightScope(_iterator));
        foreach(i; Iota!L)
            ret._labels[i] = .lightScope(_labels[i]);
        return ret;
    }

    /// Returns: Mutable slice over immutable data.
    Slice!(LightImmutableOf!Iterator, N, kind, staticMap!(LightImmutableOf, Labels)) lightImmutable()() return scope immutable @property
    {
        auto ret = typeof(return)(_structure, .lightImmutable(_iterator));
        foreach(i; Iota!L)
            ret._labels[i] = .lightImmutable(_labels[i]);
        return ret;
    }

    /// Returns: Mutable slice over const data.
    Slice!(LightConstOf!Iterator, N, kind, staticMap!(LightConstOf, Labels)) lightConst()() return scope const @property @trusted
    {
        auto ret = typeof(return)(_structure, .lightConst(_iterator));
        foreach(i; Iota!L)
            ret._labels[i] = .lightConst(_labels[i]);
        return ret;
    }

    /// ditto
    Slice!(LightImmutableOf!Iterator, N, kind, staticMap!(LightImmutableOf, Labels)) lightConst()() return scope immutable @property
    {
        return this.lightImmutable;
    }

    /// Label for the dimensions 'd'. By default returns the row label.
    Slice!(Labels[d])
        label(size_t d = 0)() @property
        if (d <= L)
    {
        return typeof(return)(_lengths[d], _labels[d]);
    }

    /// ditto
    void label(size_t d = 0)(Slice!(Labels[d]) rhs) @property
        if (d <= L)
    {
        import core.lifetime: move;
        assert(rhs.length == _lengths[d], "ndslice: labels dimension mismatch");
        _labels[d] = rhs._iterator.move;
    }

    /// ditto
    Slice!(LightConstOf!(Labels[d]))
        label(size_t d = 0)() @property const
        if (d <= L)
    {
        return typeof(return)(_lengths[d].lightConst, _labels[d]);
    }

    /// ditto
    Slice!(LightImmutableOf!(Labels[d]))
        label(size_t d = 0)() @property immutable
        if (d <= L)
    {
        return typeof(return)(_lengths[d].lightImmutable, _labels[d]);
    }

    /// Strips label off the DataFrame
    auto values()() @property
    {
        return Slice!(Iterator, N, kind)(_structure, _iterator);
    }

    /// ditto
    auto values()() @property const
    {
        return Slice!(LightConstOf!Iterator, N, kind)(_structure, .lightConst(_iterator));
    }

    /// ditto
    auto values()() @property immutable
    {
        return Slice!(LightImmutableOf!Iterator, N, kind)(_structure, .lightImmutable(_iterator));
    }

    /// `opIndex` overload for const slice
    auto ref opIndex(Indexes...)(Indexes indices) const @trusted
            if (isPureSlice!Indexes || isIndexedSlice!Indexes)
    {
        return lightConst.opIndex(indices);
    }
    /// `opIndex` overload for immutable slice
    auto ref opIndex(Indexes...)(Indexes indices) immutable @trusted
            if (isPureSlice!Indexes || isIndexedSlice!Indexes)
    {
        return lightImmutable.opIndex(indices);
    }

    static if (allSatisfy!(isPointer, Iterator, Labels))
    {
        private alias ConstThis = Slice!(const(Unqual!(PointerTarget!Iterator))*, N, kind);
        private alias ImmutableThis = Slice!(immutable(Unqual!(PointerTarget!Iterator))*, N, kind);

        /++
        Cast to const and immutable slices in case of underlying range is a pointer.
        +/
        auto toImmutable()() return scope immutable @trusted pure nothrow @nogc
        {
            return Slice!(ImmutableOfUnqualOfPointerTarget!Iterator, N, kind, staticMap!(ImmutableOfUnqualOfPointerTarget, Labels))
                (_structure, _iterator, _labels);
        }

        /// ditto
        auto toConst()() return scope const @trusted pure nothrow @nogc
        {
            version(LDC) pragma(inline, true);
            return Slice!(ConstOfUnqualOfPointerTarget!Iterator, N, kind, staticMap!(ConstOfUnqualOfPointerTarget, Labels))
                (_structure, _iterator, _labels);
        }

        static if (!is(Slice!(const(Unqual!(PointerTarget!Iterator))*, N, kind) == This))
        /// ditto
        alias toConst this;

        static if (doUnittest)
        ///
        version(mir_ndslice_test) unittest
        {
            static struct Foo
            {
                Slice!(int*) bar;

                int get(size_t i) immutable
                {
                    return bar[i];
                }

                int get(size_t i) const
                {
                    return bar[i];
                }

                int get(size_t i) inout
                {
                    return bar[i];
                }
            }
        }

        static if (doUnittest)
        ///
        version(mir_ndslice_test) unittest
        {
            Slice!(double*, 2, Universal) nn;
            Slice!(immutable(double)*, 2, Universal) ni;
            Slice!(const(double)*, 2, Universal) nc;

            const Slice!(double*, 2, Universal) cn;
            const Slice!(immutable(double)*, 2, Universal) ci;
            const Slice!(const(double)*, 2, Universal) cc;

            immutable Slice!(double*, 2, Universal) in_;
            immutable Slice!(immutable(double)*, 2, Universal) ii;
            immutable Slice!(const(double)*, 2, Universal) ic;

            nc = nc; nc = cn; nc = in_;
            nc = nc; nc = cc; nc = ic;
            nc = ni; nc = ci; nc = ii;

            void fun(T, size_t N)(Slice!(const(T)*, N, Universal) sl)
            {
                //...
            }

            fun(nn); fun(cn); fun(in_);
            fun(nc); fun(cc); fun(ic);
            fun(ni); fun(ci); fun(ii);

            static assert(is(typeof(cn[]) == typeof(nc)));
            static assert(is(typeof(ci[]) == typeof(ni)));
            static assert(is(typeof(cc[]) == typeof(nc)));

            static assert(is(typeof(in_[]) == typeof(ni)));
            static assert(is(typeof(ii[]) == typeof(ni)));
            static assert(is(typeof(ic[]) == typeof(ni)));

            ni = ci[];
            ni = in_[];
            ni = ii[];
            ni = ic[];
        }
    }

    /++
    Iterator
    Returns:
        Iterator (pointer) to the $(LREF .Slice.first) element.
    +/
    auto iterator()() inout return scope @property
    {
        return _iterator;
    }

    static if (kind == Contiguous && isPointer!Iterator)
        /++
        `ptr` alias is available only if the slice kind is $(LREF Contiguous) contiguous and the $(LREF .Slice.iterator) is a pointers.
        +/
        alias ptr = iterator;
    else
    {
        import mir.rc.array: mir_rci;
        static if (kind == Contiguous && is(Iterator : mir_rci!ET, ET))
        auto ptr() return scope inout @property
        {
            return _iterator._iterator;
        }
    }

    /++
    Field (array) data.
    Returns:
        Raw data slice.
    Constraints:
        Field is defined only for contiguous slices.
    +/
    auto field()() return scope @trusted @property
    {
        static assert(kind == Contiguous, "Slice.field is defined only for contiguous slices. Slice kind is " ~ kind.stringof);
        static if (is(typeof(_iterator[size_t(0) .. elementCount])))
        {
            return _iterator[size_t(0) .. elementCount];
        }
        else
        {
            import mir.ndslice.topology: flattened;
            return this.flattened;
        }
    }

    /// ditto
    auto field()() return const scope @trusted @property
    {
        return this.lightConst.field;
    }

    /// ditto
    auto field()() return immutable scope @trusted @property
    {
        return this.lightImmutable.field;
    }

    static if (doUnittest)
    ///
    @safe version(mir_ndslice_test) unittest
    {
        auto arr = [1, 2, 3, 4];
        auto sl0 = arr.sliced;
        auto sl1 = arr.slicedField;

        assert(sl0.field is arr);
        assert(sl1.field is arr);

        arr = arr[1 .. $];
        sl0 = sl0[1 .. $];
        sl1 = sl1[1 .. $];

        assert(sl0.field is arr);
        assert(sl1.field is arr);
        assert((cast(const)sl1).field is arr);
        ()@trusted{ assert((cast(immutable)sl1).field is arr); }();
    }

    /++
    Returns: static array of lengths
    See_also: $(LREF .Slice.structure)
    +/
    size_t[N] shape()() @trusted @property scope const
    {
        return _lengths[0 .. N];
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        assert(iota(3, 4, 5).shape == cast(size_t[3])[3, 4, 5]);
    }

    static if (doUnittest)
    /// Packed slice
    @safe @nogc pure nothrow
    version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : pack, iota;
        size_t[3] s = [3, 4, 5];
        assert(iota(3, 4, 5, 6, 7).pack!2.shape == s);
    }

    /++
    Returns: static array of lengths
    See_also: $(LREF .Slice.structure)
    +/
    ptrdiff_t[N] strides()() @trusted @property scope const
    {
        static if (N <= S)
            return _strides[0 .. N];
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
                ret[$ - 1] = _stride!(N - 1);
                foreach_reverse (i; Iota!(N - 1))
                    ret[i] = ret[i + 1] * _lengths[i + 1];
            }
            return ret;
        }
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow
    version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        size_t[3] s = [20, 5, 1];
        assert(iota(3, 4, 5).strides == s);
    }

    static if (doUnittest)
    /// Modified regular slice
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
    Structure!N structure()() @safe @property scope const
    {
        return typeof(return)(_lengths, strides);
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        assert(iota(3, 4, 5)
            .structure == Structure!3([3, 4, 5], [20, 5, 1]));
    }

    static if (doUnittest)
    /// Modified regular slice
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : pack, iota;
        assert(iota(3, 4, 5, 6, 7)
            .pack!2
            .structure == Structure!3([3, 4, 5], [20 * 42, 5 * 42, 1 * 42]));
    }

    /++
    Save primitive.
    +/
    auto save()() scope return inout @property
    {
        return this;
    }

    static if (doUnittest)
    /// Save range
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        auto slice = iota(2, 3).save;
    }

    static if (doUnittest)
    /// Pointer type.
    @safe pure nothrow version(mir_ndslice_test) unittest
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
    size_t length(size_t dimension = 0)() @safe @property scope const
        if (dimension < N)
    {
        return _lengths[dimension];
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
    sizediff_t _stride(size_t dimension = 0)() @safe @property scope const
        if (dimension < N)
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
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
    bool empty(size_t dimension = 0)() @safe @property scope const
        if (dimension < N)
    {
        return _lengths[dimension] == 0;
    }

    static if (N == 1)
    {
        ///ditto
        auto ref front(size_t dimension = 0)() return scope @trusted @property
            if (dimension == 0)
        {
            assert(!empty!dimension);
            return *_iterator;
        }

        ///ditto
        auto ref front(size_t dimension = 0)() return scope @trusted @property const
            if (dimension == 0)
        {
            assert(!empty!dimension);
            return *_iterator.lightScope;
        }

        ///ditto
        auto ref front(size_t dimension = 0)() return scope @trusted @property immutable
            if (dimension == 0)
        {
            assert(!empty!dimension);
            return *_iterator.lightScope;
        }
    }
    else
    {
        /// ditto
        Element!dimension front(size_t dimension = 0)() return scope @property
            if (dimension < N)
        {
            typeof(return)._Structure structure_ = typeof(return)._Structure.init;

            foreach (i; Iota!(typeof(return).N))
            {
                enum j = i >= dimension ? i + 1 : i;
                structure_[0][i] = _lengths[j];
            }

            static if (!typeof(return).S || typeof(return).S + 1 == S)
                alias s = _strides;
            else
                auto s = strides;

            foreach (i; Iota!(typeof(return).S))
            {
                enum j = i >= dimension ? i + 1 : i;
                structure_[1][i] = s[j];
            }

            return typeof(return)(structure_, _iterator);
        }

        ///ditto
        auto front(size_t dimension = 0)() return scope @trusted @property const
            if (dimension < N)
        {
            assert(!empty!dimension);
            return this.lightConst.front!dimension;
        }

        ///ditto
        auto front(size_t dimension = 0)() return scope @trusted @property immutable
            if (dimension < N)
        {
            assert(!empty!dimension);
            return this.lightImmutable.front!dimension;
        }
    }

    static if (N == 1 && isMutable!DeepElement && !hasAccessByRef)
    {
        ///ditto
        auto ref front(size_t dimension = 0, T)(T value) return scope @trusted @property
            if (dimension == 0)
        {
            // check assign safety
            static auto ref fun(ref DeepElement t, ref T v) @safe
            {
                return t = v;
            }
            assert(!empty!dimension);
            static if (__traits(compiles, *_iterator = value))
                return *_iterator = value;
            else
                return _iterator[0] = value;
        }
    }

    ///ditto
    static if (N == 1)
    auto ref Element!dimension
    back(size_t dimension = 0)() return scope @trusted @property
        if (dimension < N)
    {
        assert(!empty!dimension);
        return _iterator[backIndex];
    }
    else
    auto ref Element!dimension
    back(size_t dimension = 0)() return scope @trusted @property
        if (dimension < N)
    {
        assert(!empty!dimension);
        auto structure_ = typeof(return)._Structure.init;

        foreach (i; Iota!(typeof(return).N))
        {
            enum j = i >= dimension ? i + 1 : i;
            structure_[0][i] = _lengths[j];
        }

        static if (!typeof(return).S || typeof(return).S + 1 == S)
            alias s =_strides;
        else
            auto s = strides;

        foreach (i; Iota!(typeof(return).S))
        {
            enum j = i >= dimension ? i + 1 : i;
            structure_[1][i] = s[j];
        }

        return typeof(return)(structure_, _iterator + backIndex!dimension);
    }

    static if (N == 1 && isMutable!DeepElement && !hasAccessByRef)
    {
        ///ditto
        auto ref back(size_t dimension = 0, T)(T value) return scope @trusted @property
            if (dimension == 0)
        {
            // check assign safety
            static auto ref fun(ref DeepElement t, ref T v) @safe
            {
                return t = v;
            }
            assert(!empty!dimension);
            return _iterator[backIndex] = value;
        }
    }

    ///ditto
    void popFront(size_t dimension = 0)() @trusted
        if (dimension < N && (dimension == 0 || kind != Contiguous))
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
    void popBack(size_t dimension = 0)() @safe scope
        if (dimension < N && (dimension == 0 || kind != Contiguous))
    {
        assert(_lengths[dimension], __FUNCTION__ ~ ": length!" ~ dimension.stringof ~ " should be greater than 0.");
        --_lengths[dimension];
    }

    ///ditto
    void popFrontExactly(size_t dimension = 0)(size_t n) @trusted scope
        if (dimension < N && (dimension == 0 || kind != Contiguous))
    {
        assert(n <= _lengths[dimension],
            __FUNCTION__ ~ ": n should be less than or equal to length!" ~ dimension.stringof);
        _lengths[dimension] -= n;
        _iterator += _stride!dimension * n;
    }

    ///ditto
    void popBackExactly(size_t dimension = 0)(size_t n) @safe scope
        if (dimension < N && (dimension == 0 || kind != Contiguous))
    {
        assert(n <= _lengths[dimension],
            __FUNCTION__ ~ ": n should be less than or equal to length!" ~ dimension.stringof);
        _lengths[dimension] -= n;
    }

    ///ditto
    void popFrontN(size_t dimension = 0)(size_t n) @trusted scope
        if (dimension < N && (dimension == 0 || kind != Contiguous))
    {
        popFrontExactly!dimension(min(n, _lengths[dimension]));
    }

    ///ditto
    void popBackN(size_t dimension = 0)(size_t n) @safe scope
        if (dimension < N && (dimension == 0 || kind != Contiguous))
    {
        popBackExactly!dimension(min(n, _lengths[dimension]));
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
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

    package(mir) ptrdiff_t lastIndex()() @safe @property scope const
    {
        static if (kind == Contiguous)
        {
            return elementCount - 1;
        }
        else
        {
            auto strides = strides;
            ptrdiff_t shift = 0;
            foreach(i; Iota!N)
                shift += strides[i] * (_lengths[i] - 1);
            return shift;
        }
    }

    static if (N > 1)
    {
        /// Accesses the first deep element of the slice.
        auto ref first()() return scope @trusted @property
        {
            assert(!anyEmpty);
            return *_iterator;
        }

        static if (isMutable!DeepElement && !hasAccessByRef)
        ///ditto
        auto ref first(T)(T value) return scope @trusted @property
        {
            assert(!anyEmpty);
            static if (__traits(compiles, *_iterator = value))
                return *_iterator = value;
            else
                return _iterator[0] = value;
        }

        static if (doUnittest)
        ///
        @safe pure nothrow @nogc version(mir_ndslice_test) unittest
        {
            import mir.ndslice.topology: iota, universal, canonical;
            auto f = 5;
            assert([2, 3].iota(f).first == f);
        }

        /// Accesses the last deep element of the slice.
        auto ref last()() @trusted return scope @property
        {
            assert(!anyEmpty);
            return _iterator[lastIndex];
        }

        static if (isMutable!DeepElement && !hasAccessByRef)
        ///ditto
        auto ref last(T)(T value) @trusted return scope @property
        {
            assert(!anyEmpty);
            return _iterator[lastIndex] = value;
        }

        static if (doUnittest)
        ///
        @safe pure nothrow @nogc version(mir_ndslice_test) unittest
        {
            import mir.ndslice.topology: iota;
            auto f = 5;
            assert([2, 3].iota(f).last == f + 2 * 3 - 1);
        }

        static if (kind_ != SliceKind.contiguous)
        /// Peforms `popFrontAll` for all dimensions
        void popFrontAll()
        {
            assert(!anyEmpty);
            foreach(d; Iota!N_)
                popFront!d;
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.topology: iota, canonical;
            auto v = [2, 3].iota.canonical;
            v.popFrontAll;
            assert(v == [[4, 5]]);
        }

        static if (kind_ != SliceKind.contiguous)
        /// Peforms `popBackAll` for all dimensions
        void popBackAll()
        {
            assert(!anyEmpty);
            foreach(d; Iota!N_)
                popBack!d;
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.topology: iota, canonical;
            auto v = [2, 3].iota.canonical;
            v.popBackAll;
            assert(v == [[0, 1]]);
        }
    }
    else
    {
        alias first = front;
        alias last = back;
        alias popFrontAll = popFront;
        alias popBackAll = popBack;
    }

    /+
    Returns: `true` if for any dimension of completely unpacked slice the length equals to `0`, and `false` otherwise.
    +/
    private bool anyRUEmpty()() @trusted @property scope const
    {
        static if (isInstanceOf!(SliceIterator, Iterator))
        {
            import mir.ndslice.topology: unpack;
            return this.lightScope.unpack.anyRUEmpty;
        }
        else
            return _lengths[0 .. N].anyEmptyShape;
    }


    /++
    Returns: `true` if for any dimension the length equals to `0`, and `false` otherwise.
    +/
    bool anyEmpty()() @trusted @property scope const
    {
        return _lengths[0 .. N].anyEmptyShape;
    }

    static if (doUnittest)
    ///
    @safe pure nothrow @nogc version(mir_ndslice_test) unittest
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
    auto ref backward()(size_t[N] index) return scope
    {
        foreach (i; Iota!N)
            index[i] = _lengths[i] - index[i];
        return this[index];
    }

    /// ditto
    auto ref backward()(size_t[N] index) return scope const
    {
        return this.lightConst.backward(index);
    }

    /// ditto
    auto ref backward()(size_t[N] index) return scope const
    {
        return this.lightConst.backward(index);
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        auto s = iota(2, 3);
        assert(s[$ - 1, $ - 2] == s.backward([1, 2]));
    }

    /++
    Returns: Total number of elements in a slice
    +/
    size_t elementCount()() @safe @property scope const
    {
        size_t len = 1;
        foreach (i; Iota!N)
            len *= _lengths[i];
        return len;
    }

    static if (doUnittest)
    /// Regular slice
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        assert(iota(3, 4, 5).elementCount == 60);
    }


    static if (doUnittest)
    /// Packed slice
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : pack, evertPack, iota;
        auto slice = iota(3, 4, 5, 6, 7, 8);
        auto p = slice.pack!2;
        assert(p.elementCount == 360);
        assert(p[0, 0, 0, 0].elementCount == 56);
        assert(p.evertPack.elementCount == 56);
    }

    /++
    Slice selected dimension.
    Params:
        begin = initial index of the sub-slice (inclusive)
        end = final index of the sub-slice (noninclusive)
    Returns: ndslice with `length!dimension` equal to `end - begin`.
    +/
    auto select(size_t dimension)(size_t begin, size_t end) @trusted
    {
        static if (kind == Contiguous && dimension)
        {
            import mir.ndslice.topology: canonical;
            auto ret = this.canonical;
        }
        else
        {
            auto ret = this;
        }
        auto len = end - begin;
        assert(len <= ret._lengths[dimension]);
        ret._lengths[dimension] = len;
        ret._iterator += ret._stride!dimension * begin;
        return ret;
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        auto sl = iota(3, 4);
        assert(sl.select!1(1, 3) == sl[0 .. $, 1 .. 3]);
    }

    /++
    Select the first n elements for the dimension.
    Params:
        dimension = Dimension to slice.
        n = count of elements for the dimension
    Returns: ndslice with `length!dimension` equal to `n`.
    +/
    auto selectFront(size_t dimension)(size_t n) return scope
    {
        static if (kind == Contiguous && dimension)
        {
            import mir.ndslice.topology: canonical;
            auto ret = this.canonical;
        }
        else
        {
            auto ret = this;
        }
        assert(n <= ret._lengths[dimension]);
        ret._lengths[dimension] = n;
        return ret;
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        auto sl = iota(3, 4);
        assert(sl.selectFront!1(2) == sl[0 .. $, 0 .. 2]);
    }

    /++
    Select the last n elements for the dimension.
    Params:
        dimension = Dimension to slice.
        n = count of elements for the dimension
    Returns: ndslice with `length!dimension` equal to `n`.
    +/
    auto selectBack(size_t dimension)(size_t n) return scope
    {
        static if (kind == Contiguous && dimension)
        {
            import mir.ndslice.topology: canonical;
            auto ret = this.canonical;
        }
        else
        {
            auto ret = this;
        }
        assert(n <= ret._lengths[dimension]);
        ret._iterator += ret._stride!dimension * (ret._lengths[dimension] - n);
        ret._lengths[dimension] = n;
        return ret;
    }

    static if (doUnittest)
    ///
    @safe @nogc pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology : iota;
        auto sl = iota(3, 4);
        assert(sl.selectBack!1(2) == sl[0 .. $, $ - 2 .. $]);
    }

    ///ditto
    bool opEquals(IteratorR, SliceKind rkind)(auto ref const Slice!(IteratorR, N, rkind) rslice) @trusted scope const
    {
        static if (
               __traits(isPOD, Iterator)
            && __traits(isPOD, IteratorR)
            && __traits(compiles, this._iterator == rslice._iterator)
            )
        {
            if (this._lengths != rslice._lengths)
                return false;
            if (anyEmpty)
                return true;
            if (this._iterator == rslice._iterator)
            {
                auto ls = this.strides;
                auto rs = rslice.strides;
                foreach (i; Iota!N)
                {
                    if (this._lengths[i] != 1 && ls[i] != rs[i])
                        goto L;
                }
                return true;
            }
        }
        L:

        static if (is(Iterator == IotaIterator!UL, UL) && is(IteratorR == Iterator))
        {
            return false;
        }
        else
        {
            import mir.algorithm.iteration : equal;
            return equal(this.lightScope, rslice.lightScope);
        }
    }

    /// ditto
    bool opEquals(T)(scope const(T)[] arr) @trusted scope const
    {
        auto slice = this.lightConst;
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
    @safe pure nothrow
    version(mir_ndslice_test) unittest
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
    @safe pure nothrow version(mir_ndslice_test) unittest
    {
        import mir.ndslice.allocation: slice;
        import mir.ndslice.topology : iota;
        assert(iota(2, 3).slice[0 .. $ - 2] == iota([4, 3], 2)[0 .. $ - 4]);
    }

    /++
    `Slice!(IotaIterator!size_t)` is the basic type for `[a .. b]` syntax for all ndslice based code.
    +/
    Slice!(IotaIterator!size_t) opSlice(size_t dimension)(size_t i, size_t j) @safe scope const
        if (dimension < N)
    in
    {
        assert(i <= j,
            "Slice.opSlice!" ~ dimension.stringof ~ ": the left opSlice boundary must be less than or equal to the right bound.");
        enum errorMsg = ": right opSlice boundary must be less than or equal to the length of the given dimension.";
        assert(j <= _lengths[dimension],
              "Slice.opSlice!" ~ dimension.stringof ~ errorMsg);
    }
    do
    {
        return typeof(return)(j - i, typeof(return).Iterator(i));
    }

    /++
    $(BOLD Fully defined index)
    +/
    auto ref opIndex()(size_t[N] _indices...) return scope @trusted
    {
        return _iterator[indexStride(_indices)];
    }

    /// ditto
    auto ref opIndex()(size_t[N] _indices...) return scope const @trusted
    {
        static if (is(typeof(_iterator[indexStride(_indices)])))
            return _iterator[indexStride(_indices)];
        else
            return .lightConst(.lightScope(_iterator))[indexStride(_indices)];
    }

    /// ditto
    auto ref opIndex()(size_t[N] _indices...) return scope immutable @trusted
    {
        static if (is(typeof(_iterator[indexStride(_indices)])))
            return _iterator[indexStride(_indices)];
        else
            return .lightImmutable(.lightScope(_iterator))[indexStride(_indices)];
    }

    /++
    $(BOLD Partially defined index)
    +/
    auto opIndex(size_t I)(size_t[I] _indices...) return scope @trusted
        if (I && I < N)
    {
        enum size_t diff = N - I;
        alias Ret = Slice!(Iterator, diff, diff == 1 && kind == Canonical ? Contiguous : kind);
        static if (I < S)
            return Ret(_lengths[I .. N], _strides[I .. S], _iterator + indexStride(_indices));
        else
            return Ret(_lengths[I .. N], _iterator + indexStride(_indices));
    }

    /// ditto
    auto opIndex(size_t I)(size_t[I] _indices...) return scope const
        if (I && I < N)
    {
        return this.lightConst.opIndex(_indices);
    }

    /// ditto
    auto opIndex(size_t I)(size_t[I] _indices...) return scope immutable
        if (I && I < N)
    {
        return this.lightImmutable.opIndex(_indices);
    }

    /++
    $(BOLD Partially or fully defined slice.)
    +/
    auto opIndex(Slices...)(Slices slices) return scope @trusted
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
            alias Ret = Slice!(Iterator, N - F, K);
            auto structure_ = Ret._Structure.init;

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
                        stride += slice._iterator._index;
                        structure_[0][j!i] = slice._lengths[0];
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
                        stride += _strides[i] * slice._iterator._index;
                        structure_[0][j!i] = slice._lengths[0];
                        structure_[1][j!i] = _strides[i];
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
                        stride += ball * slice._iterator._index;
                        structure_[0][j!i] = slice._lengths[0];
                        static if (j!i < Ret.S)
                            structure_[1][j!i] = ball;
                    }
                    static if (i)
                        ball *= _lengths[i];
                }
            }
            foreach (i; Iota!(Slices.length, N))
                structure_[0][i - F] = _lengths[i];
            foreach (i; Iota!(Slices.length, N))
                static if (Ret.S > i - F)
                    structure_[1][i - F] = _strides[i];

            return Ret(structure_, _iterator + stride);
        }
        else
        {
            return this;
        }
    }

    static if (doUnittest)
    ///
    pure nothrow version(mir_ndslice_test) unittest
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
    auto opIndex(Slices...)(return scope Slices slices) return scope
        if (isIndexedSlice!Slices)
    {
        import mir.ndslice.topology: indexed, cartesian;
        static if (Slices.length == 1)
            alias index = slices[0];
        else
            auto index = slices.cartesian;
        return this.indexed(index);
    }

    static if (doUnittest)
    ///
    @safe pure nothrow version(mir_ndslice_test) unittest
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
        sli[idx] = 1;

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

    static if (doUnittest)
    ///
    @safe pure nothrow version(mir_ndslice_test) unittest
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

        minor[] = iota!int([3, 3], 1);

        assert(sli == [
        //   ↓     ↓        ↓︎
            [1, 0, 0, 2, 0, 3], // <---
            [0, 0, 0, 0, 0, 0],
            [4, 0, 0, 5, 0, 6], // <---
            [0, 0, 0, 0, 0, 0],
            [7, 0, 0, 8, 0, 9], // <---
            ]);
    }

    /++
    Element-wise binary operator overloading.
    Returns:
        lazy slice of the same kind and the same structure
    Note:
        Does not allocate neither new slice nor a closure.
    +/
    auto opUnary(string op)() return scope
        if (op == "*" || op == "~" || op == "-" || op == "+")
    {
        import mir.ndslice.topology: map;
        static if (op == "+")
            return this;
        else
            return this.map!(op ~ "a");
    }

    static if (doUnittest)
    ///
    version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology;

        auto payload = [1, 2, 3, 4];
        auto s = iota([payload.length], payload.ptr); // slice of references;
        assert(s[1] == payload.ptr + 1);

        auto c = *s; // the same as s.map!"*a"
        assert(c[1] == *s[1]);

        *s[1] = 3;
        assert(c[1] == *s[1]);
    }

    /++
    Element-wise operator overloading for scalars.
    Params:
        value = a scalar
    Returns:
        lazy slice of the same kind and the same structure
    Note:
        Does not allocate neither new slice nor a closure.
    +/
    auto opBinary(string op, T)(scope return T value) return scope
        if(!isSlice!T)
    {
        import mir.ndslice.topology: vmap;
        return this.vmap(LeftOp!(op, ImplicitlyUnqual!T)(value));
    }

    /// ditto
    auto opBinaryRight(string op, T)(scope return T value) return scope
        if(!isSlice!T)
    {
        import mir.ndslice.topology: vmap;
        return this.vmap(RightOp!(op, ImplicitlyUnqual!T)(value));
    }

    static if (doUnittest)
    ///
    @safe pure nothrow @nogc version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology;

        // 0 1 2 3
        auto s = iota([4]);
        // 0 1 2 0
        assert(s % 3 == iota([4]).map!"a % 3");
        // 0 2 4 6
        assert(2 * s == iota([4], 0, 2));
    }

    static if (doUnittest)
    ///
    @safe pure nothrow @nogc version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology;

        // 0 1 2 3
        auto s = iota([4]);
        // 0 1 4 9
        assert(s ^^ 2.0 == iota([4]).map!"a ^^ 2.0");
    }

    /++
    Element-wise operator overloading for slices.
    Params:
        rhs = a slice of the same shape.
    Returns:
        lazy slice the same shape that has $(LREF Contiguous) kind
    Note:
        Binary operator overloading is allowed if both slices are contiguous or one-dimensional.
        $(BR)
        Does not allocate neither new slice nor a closure.
    +/
    auto opBinary(string op, RIterator, size_t RN, SliceKind rkind)
        (scope return Slice!(RIterator, RN, rkind) rhs) return scope
        if(N == RN && (kind == Contiguous && rkind == Contiguous || N == 1) && op != "~")
    {
        import mir.ndslice.topology: zip, map;
        return zip(this, rhs).map!("a " ~ op ~ " b");
    }

    static if (doUnittest)
    ///
    @safe pure nothrow @nogc version(mir_ndslice_test) unittest
    {
        import mir.ndslice.topology: iota, map, zip;

        auto s = iota([2, 3]);
        auto c = iota([2, 3], 5, 8);
        assert(s * s + c == s.map!"a * a".zip(c).map!"a + b");
    }

    /++
    Duplicates slice.
    Returns: GC-allocated Contiguous mutable slice.
    See_also: $(LREF .Slice.idup)
    +/
    Slice!(Unqual!DeepElement*, N)
    dup()() scope @property
    {
        if (__ctfe)
        {
            import mir.ndslice.topology: flattened;
            import mir.array.allocation: array;
            return this.flattened.array.dup.sliced(this.shape);
        }
        else
        {
            import mir.ndslice.allocation: uninitSlice;
            import mir.conv: emplaceRef;
            alias E = this.DeepElement;

            auto result = (() @trusted => this.shape.uninitSlice!(Unqual!E))();

            import mir.algorithm.iteration: each;
            each!(emplaceRef!(Unqual!E))(result, this);

            return result;
        }
    }

    /// ditto
    Slice!(immutable(DeepElement)*, N)
    dup()() scope const @property
    {
        this.lightScope.dup;
    }

    /// ditto
    Slice!(immutable(DeepElement)*, N)
    dup()() scope immutable @property
    {
        this.lightScope.dup;
    }

    static if (doUnittest)
    ///
    @safe pure version(mir_ndslice_test) unittest
    {
        import mir.ndslice;
        auto x = 3.iota!int;
        Slice!(immutable(int)*) imm = x.idup;
        Slice!(int*) mut = imm.dup;
        assert(imm == x);
        assert(mut == x);
    }

    /++
    Duplicates slice.
    Returns: GC-allocated Contiguous immutable slice.
    See_also: $(LREF .Slice.dup)
    +/
    Slice!(immutable(DeepElement)*, N)
    idup()() scope @property
    {
        if (__ctfe)
        {
            import mir.ndslice.topology: flattened;
            import mir.array.allocation: array;
            return this.flattened.array.idup.sliced(this.shape);
        }
        else
        {
            import mir.ndslice.allocation: uninitSlice;
            import mir.conv: emplaceRef;
            alias E = this.DeepElement;

            auto result = (() @trusted => this.shape.uninitSlice!(Unqual!E))();

            import mir.algorithm.iteration: each;
            each!(emplaceRef!(immutable E))(result, this);
            alias R = typeof(return);
            return (() @trusted => cast(R) result)();
        }
    }

    /// ditto
    Slice!(immutable(DeepElement)*, N)
    idup()() scope const @property
    {
        this.lightScope.idup;
    }

    /// ditto
    Slice!(immutable(DeepElement)*, N)
    idup()() scope immutable @property
    {
        this.lightScope.idup;
    }

    static if (doUnittest)
    ///
    @safe pure version(mir_ndslice_test) unittest
    {
        import mir.ndslice;
        auto x = 3.iota!int;
        Slice!(int*) mut = x.dup;
        Slice!(immutable(int)*) imm = mut.idup;
        assert(imm == x);
        assert(mut == x);
    }

    /++
    Provides the index location of a slice, taking into account
    `Slice._strides`. Similar to `Slice.indexStride`, except the slice is
    indexed by a value. Called by `Slice.accessFlat`.

    Params:
        n = location in slice
    Returns:
        location in slice, adjusted for `Slice._strides`
    See_also:
        $(SUBREF topology, flattened),
        $(LREF .Slice.indexStride),
        $(LREF .Slice.accessFlat)
    +/
    private
    ptrdiff_t indexStrideValue(ptrdiff_t n) @safe scope const
    {
        assert(n < elementCount, "indexStrideValue: n must be less than elementCount");
        assert(n >= 0, "indexStrideValue: n must be greater than or equal to zero");

        static if (kind == Contiguous) {
            return n;
        } else {
            ptrdiff_t _shift;
            foreach_reverse (i; Iota!(1, N))
            {
                immutable v = n / ptrdiff_t(_lengths[i]);
                n %= ptrdiff_t(_lengths[i]);
                static if (i == S)
                    _shift += n;
                else
                    _shift += n * _strides[i];
                n = v;
            }
            _shift += n * _strides[0];
            return _shift;
        }
    }

    /++
    Provides access to a slice as if it were `flattened`.

    Params:
        index = location in slice
    Returns:
        value of flattened slice at `index`
    See_also: $(SUBREF topology, flattened)
    +/
    auto ref accessFlat(size_t index) return scope @trusted
    {
        return _iterator[indexStrideValue(index)];
    }

    ///
    version(mir_ndslice_test)
    @safe pure @nogc nothrow
    unittest
    {
        import mir.ndslice.topology: iota, flattened;

        auto x = iota(2, 3, 4);
        assert(x.accessFlat(9) == x.flattened[9]);
    }

    static if (isMutable!DeepElement)
    {
        private void opIndexOpAssignImplSlice(string op, RIterator, size_t RN, SliceKind rkind)
            (Slice!(RIterator, RN, rkind) value) scope
        {
            static if (N > 1 && RN == N && kind == Contiguous && rkind == Contiguous)
            {
                import mir.ndslice.topology : flattened;
                this.flattened.opIndexOpAssignImplSlice!op(value.flattened);
            }
            else
            {
                auto ls = this;
                do
                {
                    static if (N > RN)
                    {
                        ls.front.opIndexOpAssignImplSlice!op(value);
                    }
                    else
                    {
                        static if (ls.N == 1)
                        {
                            static if (isInstanceOf!(SliceIterator, Iterator))
                            {
                                static if (isSlice!(typeof(value.front)))
                                    ls.front.opIndexOpAssignImplSlice!op(value.front);
                                else
                                static if (isDynamicArray!(typeof(value.front)))
                                    ls.front.opIndexOpAssignImplSlice!op(value.front);
                                else
                                    ls.front.opIndexOpAssignImplValue!op(value.front);
                            }
                            else
                            static if (op == "^^" && isFloatingPoint!(typeof(ls.front)) && isFloatingPoint!(typeof(value.front)))
                            {
                                import mir.math.common: pow;
                                ls.front = pow(ls.front, value.front);
                            }
                            else
                                mixin("ls.front " ~ op ~ "= value.front;");
                        }
                        else
                        static if (RN == 1)
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
        void opIndexAssign(RIterator, size_t RN, SliceKind rkind, Slices...)
            (Slice!(RIterator, RN, rkind) value, Slices slices) return scope
            if (isFullPureSlice!Slices || isIndexedSlice!Slices)
        {
            auto sl = this.lightScope.opIndex(slices);
            assert(_checkAssignLengths(sl, value));
            if(!sl.anyRUEmpty)
                sl.opIndexOpAssignImplSlice!""(value);
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
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
        @safe pure nothrow version(mir_ndslice_test) unittest
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
        @safe pure nothrow version(mir_ndslice_test) unittest
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

        void opIndexOpAssignImplArray(string op, T, Slices...)(T[] value) scope
        {
            auto ls = this;
            assert(ls.length == value.length, __FUNCTION__ ~ ": argument must have the same length.");
            static if (N == 1)
            {
                do
                {
                    static if (ls.N == 1)
                    {
                        static if (isInstanceOf!(SliceIterator, Iterator))
                        {
                            static if (isSlice!(typeof(value[0])))
                                ls.front.opIndexOpAssignImplSlice!op(value[0]);
                            else
                            static if (isDynamicArray!(typeof(value[0])))
                                ls.front.opIndexOpAssignImplSlice!op(value[0]);
                            else
                                ls.front.opIndexOpAssignImplValue!op(value[0]);
                        }
                        else
                        static if (op == "^^" && isFloatingPoint!(typeof(ls.front)) && isFloatingPoint!(typeof(value[0])))
                        {
                            import mir.math.common: pow;
                            ls.front = pow(ls.front, value[0]);
                        }
                        else
                            mixin("ls.front " ~ op ~ "= value[0];");
                    }
                    else
                        mixin("ls.front[] " ~ op ~ "= value[0];");
                    value = value[1 .. $];
                    ls.popFront;
                }
                while (ls.length);
            }
            else
            static if (N == DynamicArrayDimensionsCount!(T[]))
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
        void opIndexAssign(T, Slices...)(T[] value, Slices slices) return scope
            if ((isFullPureSlice!Slices || isIndexedSlice!Slices)
                && (!isDynamicArray!DeepElement || isDynamicArray!T)
                && DynamicArrayDimensionsCount!(T[]) - DynamicArrayDimensionsCount!DeepElement <= typeof(this.opIndex(slices)).N)
        {
            auto sl = this.lightScope.opIndex(slices);
            sl.opIndexOpAssignImplArray!""(value);
        }

        static if (doUnittest)
        ///
        pure nothrow version(mir_ndslice_test) unittest
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
        pure nothrow version(mir_ndslice_test) unittest
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


        private void opIndexOpAssignImplConcatenation(string op, T)(T value) scope
        {
            auto sl = this;
            static if (concatenationDimension!T)
            {
                if (!sl.empty) do
                {
                    static if (op == "")
                        sl.front.opIndexAssign(value.front);
                    else
                        sl.front.opIndexOpAssign!op(value.front);
                    value.popFront;
                    sl.popFront;
                }
                while(!sl.empty);
            }
            else
            {
                foreach (ref slice; value._slices)
                {
                    static if (op == "")
                        sl[0 .. slice.length].opIndexAssign(slice);
                    else
                        sl[0 .. slice.length].opIndexOpAssign!op(slice);

                    sl = sl[slice.length .. $];
                }
                assert(sl.empty);
            }
        }

        ///
        void opIndexAssign(T, Slices...)(T concatenation, Slices slices) return scope
            if ((isFullPureSlice!Slices || isIndexedSlice!Slices) && isConcatenation!T)
        {
            auto sl = this.lightScope.opIndex(slices);
            static assert(typeof(sl).N == T.N, "incompatible dimension count");
            sl.opIndexOpAssignImplConcatenation!""(concatenation);
        }

        static if (!isNumeric!DeepElement)
        /++
        Assignment of a value (e.g. a number) to a $(B fully defined slice).
        +/
        void opIndexAssign(T, Slices...)(T value, Slices slices) scope
            if ((isFullPureSlice!Slices || isIndexedSlice!Slices)
                && (!isDynamicArray!T || isDynamicArray!DeepElement)
                && DynamicArrayDimensionsCount!T == DynamicArrayDimensionsCount!DeepElement
                && !isSlice!T
                && !isConcatenation!T)
        {
            auto sl = this.lightScope.opIndex(slices);
            if(!sl.anyRUEmpty)
                sl.opIndexOpAssignImplValue!""(value);
        }
        else
        void opIndexAssign(Slices...)(DeepElement value, Slices slices) scope
            if (isFullPureSlice!Slices || isIndexedSlice!Slices)
        {
            auto sl = this.lightScope.opIndex(slices);
            if(!sl.anyRUEmpty)
                sl.opIndexOpAssignImplValue!""(value);
        }

        static if (doUnittest)
        ///
        @safe pure nothrow
        version(mir_ndslice_test) unittest
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
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.allocation;
            import mir.ndslice.topology : pack;
            auto a = slice!int(2, 3).pack!1;

            a[] = 9;
            //assert(a == [[9, 9, 9], [9, 9, 9]]);
        }

        /++
        Assignment of a value (e.g. a number) to a $(B fully defined index).
        +/
        auto ref opIndexAssign(T)(T value, size_t[N] _indices...) return scope @trusted
        {
            // check assign safety
            static auto ref fun(ref DeepElement t, ref T v) @safe
            {
                return t = v;
            }
            return _iterator[indexStride(_indices)] = value;
        }
        ///ditto
        auto ref opIndexAssign()(DeepElement value, size_t[N] _indices...) return scope @trusted
        {
            import mir.functional: forward;
            // check assign safety
            static auto ref fun(ref DeepElement t, ref DeepElement v) @safe
            {
                return t = v;
            }
            return _iterator[indexStride(_indices)] = forward!value;
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            a[1, 2] = 3;
            assert(a[1, 2] == 3);
        }

        static if (doUnittest)
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            auto a = new int[6].sliced(2, 3);

            a[[1, 2]] = 3;
            assert(a[[1, 2]] == 3);
        }

        /++
        Op Assignment `op=` of a value (e.g. a number) to a $(B fully defined index).
        +/
        auto ref opIndexOpAssign(string op, T)(T value, size_t[N] _indices...) return scope @trusted
        {
            // check op safety
            static auto ref fun(ref DeepElement t, ref T v) @safe
            {
                return mixin(`t` ~ op ~ `= v`);
            }
            auto str = indexStride(_indices);
            static if (op == "^^" && isFloatingPoint!DeepElement && isFloatingPoint!(typeof(value)))
            {
                import mir.math.common: pow;
                _iterator[str] = pow(_iterator[str], value);
            }
            else
                return mixin (`_iterator[str] ` ~ op ~ `= value`);
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            a[1, 2] += 3;
            assert(a[1, 2] == 3);
        }

        static if (doUnittest)
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            auto a = new int[6].sliced(2, 3);

            a[[1, 2]] += 3;
            assert(a[[1, 2]] == 3);
        }

        /++
        Op Assignment `op=` of a value of `Slice` type to a $(B fully defined slice).
        +/
        void opIndexOpAssign(string op, RIterator, SliceKind rkind, size_t RN, Slices...)
            (Slice!(RIterator, RN, rkind) value, Slices slices) return scope
            if (isFullPureSlice!Slices || isIndexedSlice!Slices)
        {
            auto sl = this.lightScope.opIndex(slices);
            assert(_checkAssignLengths(sl, value));
            if(!sl.anyRUEmpty)
                sl.opIndexOpAssignImplSlice!op(value);
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
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
        @safe pure nothrow version(mir_ndslice_test) unittest
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
        @safe pure nothrow version(mir_ndslice_test) unittest
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
        void opIndexOpAssign(string op, T, Slices...)(T[] value, Slices slices) return scope
            if (isFullPureSlice!Slices
                && (!isDynamicArray!DeepElement || isDynamicArray!T)
                && DynamicArrayDimensionsCount!(T[]) - DynamicArrayDimensionsCount!DeepElement <= typeof(this.opIndex(slices)).N)
        {
            auto sl = this.lightScope.opIndex(slices);
            sl.opIndexOpAssignImplArray!op(value);
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
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
        @safe pure nothrow
        version(mir_ndslice_test) unittest
        {
            import mir.ndslice.allocation : slice;
            import mir.ndslice.topology : blocks;
            auto a = slice!int(4, 4);
            a.blocks(2, 2)[] += [[0, 1], [2, 3]];

            assert(a ==
                    [[0, 0, 1, 1],
                     [0, 0, 1, 1],
                     [2, 2, 3, 3],
                     [2, 2, 3, 3]]);
        }

        private void opIndexOpAssignImplValue(string op, T)(T value) return scope
        {
            static if (N > 1 && kind == Contiguous)
            {
                import mir.ndslice.topology : flattened;
                this.flattened.opIndexOpAssignImplValue!op(value);
            }
            else
            {
                auto ls = this;
                do
                {
                    static if (N == 1)
                    {
                        static if (isInstanceOf!(SliceIterator, Iterator))
                            ls.front.opIndexOpAssignImplValue!op(value);
                        else
                            mixin (`ls.front ` ~ op ~ `= value;`);
                    }
                    else
                        ls.front.opIndexOpAssignImplValue!op(value);
                    ls.popFront;
                }
                while(ls._lengths[0]);
            }
        }

        /++
        Op Assignment `op=` of a value (e.g. a number) to a $(B fully defined slice).
       +/
        void opIndexOpAssign(string op, T, Slices...)(T value, Slices slices) return scope
            if ((isFullPureSlice!Slices || isIndexedSlice!Slices)
                && (!isDynamicArray!T || isDynamicArray!DeepElement)
                && DynamicArrayDimensionsCount!T == DynamicArrayDimensionsCount!DeepElement
                && !isSlice!T
                && !isConcatenation!T)
        {
            auto sl = this.lightScope.opIndex(slices);
            if(!sl.anyRUEmpty)
                sl.opIndexOpAssignImplValue!op(value);
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
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
        void opIndexOpAssign(string op,T, Slices...)(T concatenation, Slices slices) return scope
            if ((isFullPureSlice!Slices || isIndexedSlice!Slices) && isConcatenation!T)
        {
            auto sl = this.lightScope.opIndex(slices);
            static assert(typeof(sl).N == concatenation.N);
            sl.opIndexOpAssignImplConcatenation!op(concatenation);
        }

        static if (doUnittest)
        /// Packed slices have the same behavior.
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.allocation;
            import mir.ndslice.topology : pack;
            auto a = slice!int(2, 3).pack!1;

            a[] += 9;
            assert(a == [[9, 9, 9], [9, 9, 9]]);
        }


        /++
        Increment `++` and Decrement `--` operators for a $(B fully defined index).
        +/
        auto ref opIndexUnary(string op)(size_t[N] _indices...) return scope
            @trusted
            // @@@workaround@@@ for Issue 16473
            //if (op == `++` || op == `--`)
        {
            // check op safety
            static auto ref fun(DeepElement t) @safe
            {
                return mixin(op ~ `t`);
            }
            return mixin (op ~ `_iterator[indexStride(_indices)]`);
        }

        static if (doUnittest)
        ///
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.allocation;
            auto a = slice!int(2, 3);

            ++a[1, 2];
            assert(a[1, 2] == 1);
        }

        // Issue 16473
        static if (doUnittest)
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            import mir.ndslice.allocation;
            auto sl = slice!double(2, 5);
            auto d = -sl[0, 1];
        }

        static if (doUnittest)
        @safe pure nothrow version(mir_ndslice_test) unittest
        {
            auto a = new int[6].sliced(2, 3);

            ++a[[1, 2]];
            assert(a[[1, 2]] == 1);
        }

        private void opIndexUnaryImpl(string op, Slices...)(Slices slices) scope
        {
            auto ls = this;
            do
            {
                static if (N == 1)
                {
                    static if (isInstanceOf!(SliceIterator, Iterator))
                        ls.front.opIndexUnaryImpl!op;
                    else
                        mixin (op ~ `ls.front;`);
                }
                else
                    ls.front.opIndexUnaryImpl!op;
                ls.popFront;
            }
            while(ls._lengths[0]);
        }

        /++
        Increment `++` and Decrement `--` operators for a $(B fully defined slice).
        +/
        void opIndexUnary(string op, Slices...)(Slices slices) return scope
            if (isFullPureSlice!Slices && (op == `++` || op == `--`))
        {
            auto sl = this.lightScope.opIndex(slices);
            if (!sl.anyRUEmpty)
                sl.opIndexUnaryImpl!op;
        }

        static if (doUnittest)
        ///
        @safe pure nothrow
        version(mir_ndslice_test) unittest
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

/// ditto
alias Slice = mir_slice;

/++
Slicing, indexing, and arithmetic operations.
+/
pure nothrow version(mir_ndslice_test) unittest
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

    // `opIndexAssing` accepts only fully defined indices and slices.
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
pure nothrow version(mir_ndslice_test) unittest
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
version(mir_ndslice_test) unittest
{
    import mir.algorithm.iteration: filter, all;
    import mir.array.allocation;
    import mir.exception;
    import mir.functional: not;
    import mir.ndslice.allocation;
    import mir.parse;
    import mir.primitives: empty;

    import std.algorithm: map;
    import std.string: lineSplitter, split;

        // std.functional, std.string, std.range;

    Slice!(int*, 2) toMatrix(string str)
    {
        string[][] data = str.lineSplitter.filter!(not!empty).map!split.array;

        size_t rows    = data   .length.enforce!"empty input";
        size_t columns = data[0].length.enforce!"empty first row";

        data.all!(a => a.length == columns).enforce!"rows have different lengths";
        auto slice = slice!int(rows, columns);
        foreach (i, line; data)
            foreach (j, num; line)
                slice[i, j] = num.fromString!int;
        return slice;
    }

    auto input = "\r1 2  3\r\n 4 5 6\n";

    auto matrix = toMatrix(input);
    assert(matrix == [[1, 2, 3], [4, 5, 6]]);

    // back to text
    import std.format;
    auto text2 = format("%(%(%s %)\n%)\n", matrix);
    assert(text2 == "1 2 3\n4 5 6\n");
}

// Slicing
@safe @nogc pure nothrow version(mir_ndslice_test) unittest
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
pure nothrow version(mir_ndslice_test) unittest
{
    import mir.ndslice.allocation;
    import mir.ndslice.topology : iota;

    auto fun(ref sizediff_t x) { x *= 3; }

    auto tensor = iota(8, 9, 10).slice;

    ++tensor[];
    fun(tensor[0, 0, 0]);

    assert(tensor[0, 0, 0] == 3);

    tensor[0, 0, 0] *= 4;
    tensor[0, 0, 0]--;
    assert(tensor[0, 0, 0] == 11);
}

// Operator overloading. # 2
pure nothrow version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology: map, iota;
    import mir.array.allocation : array;
    //import std.bigint;

    auto matrix = 72
        .iota
        //.map!(i => BigInt(i))
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
pure nothrow version(mir_ndslice_test) unittest
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
version(mir_ndslice_test) unittest
{
    // Arrays
    foreach (T; AliasSeq!(int, const int, immutable int))
        static assert(is(typeof((T[]).init.sliced(3, 4)) == Slice!(T*, 2)));

    // Container Array
    import std.container.array;
    Array!int ar;
    ar.length = 12;
    auto arSl = ar[].slicedField(3, 4);
}

// Test for map #1
version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology: map, byDim;
    auto slice = [1, 2, 3, 4].sliced(2, 2);

    auto r = slice.byDim!0.map!(a => a.map!(a => a * 6));
    assert(r.front.front == 6);
    assert(r.front.back == 12);
    assert(r.back.front == 18);
    assert(r.back.back == 24);
    assert(r[0][0] ==  6);
    assert(r[0][1] == 12);
    assert(r[1][0] == 18);
    assert(r[1][1] == 24);

    import std.range.primitives;
    static assert(hasSlicing!(typeof(r)));
    static assert(isForwardRange!(typeof(r)));
    static assert(isRandomAccessRange!(typeof(r)));
}

// Test for map #2
version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology: map, byDim;
    import std.range.primitives;
    auto data = [1, 2, 3, 4];
    static assert(hasSlicing!(typeof(data)));
    static assert(isForwardRange!(typeof(data)));
    static assert(isRandomAccessRange!(typeof(data)));
    auto slice = data.sliced(2, 2);
    static assert(hasSlicing!(typeof(slice)));
    static assert(isForwardRange!(typeof(slice)));
    static assert(isRandomAccessRange!(typeof(slice)));
    auto r = slice.byDim!0.map!(a => a.map!(a => a * 6));
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

private enum bool isType(alias T) = false;

private enum bool isType(T) = true;

private enum isStringValue(alias T) = is(typeof(T) : string);


private bool _checkAssignLengths(
    LIterator, RIterator,
    size_t LN, size_t RN,
    SliceKind lkind, SliceKind rkind,
    )
    (Slice!(LIterator, LN, lkind) ls,
     Slice!(RIterator, RN, rkind) rs)
{
    static if (isInstanceOf!(SliceIterator, LIterator))
    {
        import mir.ndslice.topology: unpack;
        return _checkAssignLengths(ls.unpack, rs);
    }
    else
    static if (isInstanceOf!(SliceIterator, RIterator))
    {
        import mir.ndslice.topology: unpack;
        return _checkAssignLengths(ls, rs.unpack);
    }
    else
    {
        foreach (i; Iota!(0, RN))
            if (ls._lengths[i + LN - RN] != rs._lengths[i])
                return false;
        return true;
    }
}

@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology : iota;

    assert(_checkAssignLengths(iota(2, 2), iota(2, 2)));
    assert(!_checkAssignLengths(iota(2, 2), iota(2, 3)));
    assert(!_checkAssignLengths(iota(2, 2), iota(3, 2)));
    assert(!_checkAssignLengths(iota(2, 2), iota(3, 3)));
}

pure nothrow version(mir_ndslice_test) unittest
{
    auto slice = new int[15].slicedField(5, 3);

    /// Fully defined slice
    assert(slice[] == slice);
    auto sublice = slice[0..$-2, 1..$];

    /// Partially defined slice
    auto row = slice[3];
    auto col = slice[0..$, 1];
}

pure nothrow version(mir_ndslice_test) unittest
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

pure nothrow version(mir_ndslice_test) unittest
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

pure nothrow version(mir_ndslice_test) unittest
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

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[1, 2] = 3;
    assert(a[1, 2] == 3);
}

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[[1, 2]] = 3;
    assert(a[[1, 2]] == 3);
}

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[1, 2] += 3;
    assert(a[1, 2] == 3);
}

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[[1, 2]] += 3;
    assert(a[[1, 2]] == 3);
}

pure nothrow version(mir_ndslice_test) unittest
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

pure nothrow version(mir_ndslice_test) unittest
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

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    a[] += 1;
    assert(a == [[1, 1, 1], [1, 1, 1]]);

    a[0..$, 0..$-1] += 2;
    assert(a == [[3, 3, 1], [3, 3, 1]]);

    a[1, 0..$-1] += 3;
    assert(a[1] == [6, 6, 1]);
}

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    ++a[1, 2];
    assert(a[1, 2] == 1);
}

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    ++a[[1, 2]];
    assert(a[[1, 2]] == 1);
}

pure nothrow version(mir_ndslice_test) unittest
{
    auto a = new int[6].slicedField(2, 3);

    ++a[];
    assert(a == [[1, 1, 1], [1, 1, 1]]);

    --a[1, 0..$-1];
    assert(a[1] == [0, 0, 1]);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology: iota, universal;

    auto sl = iota(3, 4).universal;
    assert(sl[0 .. $] == sl);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology: canonical, iota;
    static assert(kindOf!(typeof(iota([1, 2]).canonical[1])) == Contiguous);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology: iota;
    auto s = iota(2, 3);
    assert(s.front!1 == [0, 3]);
    assert(s.back!1 == [2, 5]);
}

/++
Assignment utility for generic code that works both with scalars and with ndslices.
Params:
    op = assign operation (generic, optional)
    lside = left side
    rside = right side
Returns:
    expression value
+/
auto ndassign(string op = "", L, R)(ref L lside, auto ref R rside) @property
    if (!isSlice!L && (op.length == 0 || op[$-1] != '='))
{
    return mixin(`lside ` ~ op ~ `= rside`);
}

/// ditto
auto ndassign(string op = "", L, R)(L lside, auto ref R rside) @property
    if (isSlice!L && (op.length == 0 || op[$-1] != '='))
{
    static if (op == "")
        return lside.opIndexAssign(rside);
    else
        return lside.opIndexOpAssign!op(rside);
}

///
version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology: iota;
    import mir.ndslice.allocation: slice;
    auto scalar = 3;
    auto vector = 3.iota.slice; // [0, 1, 2]

    // scalar = 5;
    scalar.ndassign = 5;
    assert(scalar == 5);

    // vector[] = vector * 2;
    vector.ndassign = vector * 2;
    assert(vector == [0, 2, 4]);

    // vector[] += scalar;
    vector.ndassign!"+"= scalar;
    assert(vector == [5, 7, 9]);
}

version(mir_ndslice_test) pure nothrow unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: universal;

    auto df = slice!(double, int, int)(2, 3).universal;
    df.label[] = [1, 2];
    df.label!1[] = [1, 2, 3];
    auto lsdf = df.lightScope;
    assert(lsdf.label!0[0] == 1);
    assert(lsdf.label!1[1] == 2);

    auto immdf = (cast(immutable)df).lightImmutable;
    assert(immdf.label!0[0] == 1);
    assert(immdf.label!1[1] == 2);

    auto constdf = df.lightConst;
    assert(constdf.label!0[0] == 1);
    assert(constdf.label!1[1] == 2);

    auto constdf2 = df.toConst;
    assert(constdf2.label!0[0] == 1);
    assert(constdf2.label!1[1] == 2);

    auto immdf2 = (cast(immutable)df).toImmutable;
    assert(immdf2.label!0[0] == 1);
    assert(immdf2.label!1[1] == 2);
}

version(mir_ndslice_test) pure nothrow unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: universal;

    auto df = slice!(double, int, int)(2, 3).universal;
    df[] = 5;

    Slice!(double*, 2, Universal) values = df.values;
    assert(values[0][0] == 5);
    Slice!(LightConstOf!(double*), 2, Universal) constvalues = df.values;
    assert(constvalues[0][0] == 5);
    Slice!(LightImmutableOf!(double*), 2, Universal) immvalues = (cast(immutable)df).values;
    assert(immvalues[0][0] == 5);
}

version(mir_ndslice_test) @safe unittest
{
    import mir.ndslice.allocation;
    auto a = rcslice!double([2, 3], 0);
    auto b = rcslice!double([2, 3], 0);
    a[1, 2] = 3;
    b[] = a;
    assert(a == b);
}

version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened;

    auto m = iota(2, 3, 4); // Contiguous Matrix
    auto mFlat = m.flattened;

    for (size_t i = 0; i < m.elementCount; i++) {
        assert(m.accessFlat(i) == mFlat[i]);
    }
}

version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened;

    auto m = iota(3, 4); // Contiguous Matrix
    auto x = m.front; // Contiguous Vector

    for (size_t i = 0; i < x.elementCount; i++) {
        assert(x.accessFlat(i) == m[0, i]);
    }
}

version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened;

    auto m = iota(3, 4); // Contiguous Matrix
    auto x = m[0 .. $, 0 .. $ - 1]; // Canonical Matrix
    auto xFlat = x.flattened;

    for (size_t i = 0; i < x.elementCount; i++) {
        assert(x.accessFlat(i) == xFlat[i]);
    }
}


version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened;

    auto m = iota(2, 3, 4); // Contiguous Matrix
    auto x = m[0 .. $, 0 .. $, 0 .. $ - 1]; // Canonical Matrix
    auto xFlat = x.flattened;

    for (size_t i = 0; i < x.elementCount; i++) {
        assert(x.accessFlat(i) == xFlat[i]);
    }
}


version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened;
    import mir.ndslice.dynamic: transposed;

    auto m = iota(2, 3, 4); // Contiguous Matrix
    auto x = m.transposed!(2, 1, 0); // Universal Matrix
    auto xFlat = x.flattened;

    for (size_t i = 0; i < x.elementCount; i++) {
        assert(x.accessFlat(i) == xFlat[i]);
    }
}

version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened;
    import mir.ndslice.dynamic: transposed;

    auto m = iota(3, 4); // Contiguous Matrix
    auto x = m.transposed; // Universal Matrix
    auto xFlat = x.flattened;

    for (size_t i = 0; i < x.elementCount; i++) {
        assert(x.accessFlat(i) == xFlat[i]);
    }
}

version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened, diagonal;

    auto m = iota(3, 4); // Contiguous Matrix
    auto x = m.diagonal; // Universal Vector

    for (size_t i = 0; i < x.elementCount; i++) {
        assert(x.accessFlat(i) == m[i, i]);
    }
}

version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest
{
    import mir.ndslice.topology: iota, flattened;

    auto m = iota(3, 4); // Contiguous Matrix
    auto x = m.front!1; // Universal Vector

    for (size_t i = 0; i < x.elementCount; i++) {
        assert(x.accessFlat(i) == m[i, 0]);
    }
}

version(mir_ndslice_test)
@safe pure @nogc nothrow
unittest // check it can be compiled
{
    import mir.algebraic;
    alias S = Slice!(double*, 2);
    alias D = Variant!S;
}

version(mir_ndslice_test)
unittest
{
    import mir.ndslice;

    auto matrix = slice!short(3, 4);
    matrix[] = 0;
    matrix.diagonal[] = 1;

    auto row = matrix[2];
    row[3] = 6;
    assert(matrix[2, 3] == 6); // D & C index order
}
