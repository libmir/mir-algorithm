/++
This is a submodule of $(MREF mir, ndslice).

The module contains $(LREF ._concatenation) routine.
It construct $(LREF Concatenation) structure that can be
assigned to an ndslice of the same shape with `[] = ` or `[] op= `.

$(SUBREF slice, slicedNdField) can be used to construct ndslice view on top of $(LREF Concatenation).

$(SUBREF allocation, slice) has special overload for $(LREF Concatenation) that can be used to allocate new ndslice.

$(BOOKTABLE $(H2 Concatenation constructors),
$(TR $(TH Function Name) $(TH Description))
$(T2 ._concatenation, Creates a $(LREF Concatenation) view of multiple slices.)
$(T2 pad, Pads with a constant value.)
$(T2 padEdge, Pads with the edge values of slice.)
$(T2 padSymmetric, Pads with the reflection of the slice mirrored along the edge of the slice.)
$(T2 padWrap, Pads with the wrap of the slice along the axis. The first values are used to pad the end and the end values are used to pad the beginning.)
)


License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

See_also: $(SUBMODULE fuse) submodule.

Macros:
SUBMODULE = $(MREF_ALTTEXT $1, mir, ndslice, $1)
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.concatenation;

import std.traits;
import std.meta;

import mir.internal.utility;
import mir.math.common: optmath;
import mir.ndslice.internal;
import mir.ndslice.slice;
import mir.primitives;

@optmath:

private template _expose(size_t maxN, size_t dim)
{
    static @optmath auto _expose(S)(S s)
    {
        static if (s.N == maxN)
        {
            return s;
        }
        else
        {
            static assert(s.shape.length == s.N, "Cannot create concatenation for packed slice of smaller dimension.");
            import mir.ndslice.topology: repeat, unpack;
            auto r = s.repeat(1).unpack;
            static if (dim)
            {
                import mir.ndslice.dynamic: transposed;
                return r.transposed!(Iota!(1, dim + 1));
            }
            else
            {
                return r;
            }
        }
    }
}

private template _Expose(size_t maxN, size_t dim)
{
    alias _expose = ._expose!(maxN, dim);
    alias _Expose(S) = ReturnType!(_expose!S);
}


/++
Creates a $(LREF Concatenation) view of multiple slices.

Can be used in combination with itself, $(LREF until), $(SUBREF, allocation, slice),
and $(SUBREF slice, Slice) assignment.

Params:
    slices = tuple of slices and/or concatenations.

Returns: $(LREF Concatenation).
+/
auto concatenation(size_t dim = 0, Slices...)(Slices slices)
{
    import mir.algorithm.iteration: reduce;
    import mir.utility: min, max; 
    enum NOf(S) = S.N;
    enum NArray = [staticMap!(NOf, Slices)];
    enum minN = size_t.max.reduce!min(NArray);
    enum maxN = size_t.min.reduce!max(NArray);
    static if (minN == maxN)
    {
        return Concatenation!(dim, Slices)(slices);
    }
    else
    {
        static assert(minN + 1 == maxN);
        alias S = staticMap!(_Expose!(maxN, dim), Slices);
        S s;
        foreach (i, ref e; s)
            e = _expose!(maxN, dim)(slices[i]);
        return Concatenation!(dim, S)(s);
    }
}

/// Concatenation of slices with different dimmensions. 
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: repeat, iota;

    // 0 0 0
    auto vector = size_t.init.repeat([3]);

    // 1 2 3
    // 4 5 6
    auto matrix = iota([2, 3], 1);

    assert(concatenation(vector, matrix).slice == [
        [0, 0, 0],
        [1, 2, 3],
        [4, 5, 6],
    ]);

    vector.popFront;
    assert(concatenation!1(vector, matrix).slice == [
        [0, 1, 2, 3],
        [0, 4, 5, 6],
    ]);
}

/// Multidimensional
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;
    import mir.ndslice.slice : slicedNdField;

    // 0, 1, 2
    // 3, 4, 5
    auto a = iota(2, 3);
    // 0, 1
    // 2, 3
    auto b = iota(2, 2);
    // 0, 1, 2, 3, 4
    auto c = iota(1, 5);

    // 0, 1, 2,   0, 1
    // 3, 4, 5,   2, 3
    // 
    // 0, 1, 2, 3, 4
    // construction phase
    auto s = concatenation(concatenation!1(a, b), c);

    // allocation phase
    auto d = s.slice;
    assert(d == [
        [0, 1, 2, 0, 1],
        [3, 4, 5, 2, 3],
        [0, 1, 2, 3, 4],
        ]);

    // optimal fragmentation for output/writing/buffering
    auto testData = [
        [0, 1, 2], [0, 1],
        [3, 4, 5], [2, 3],
        [0, 1, 2, 3, 4],
    ];
    size_t i;
    s.forEachFragment!((fragment) {
        pragma(inline, false); //reduces template bloat
        assert(fragment == testData[i++]);
        });
    assert(i == testData.length);

    // lazy ndslice view
    assert(s.slicedNdField == d);
}

/// 1D
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;
    import mir.ndslice.slice : slicedNdField;

    size_t i;
    auto a = 3.iota;
    auto b = iota([6], a.length);
    auto s = concatenation(a, b);
    assert(s.length == a.length + b.length);
    // fast iteration with until
    s.until!((elem){ assert(elem == i++); return false; });
    // allocation with slice
    assert(s.slice == s.length.iota);
    // 1D or multidimensional assignment
    auto d = slice!double(s.length);
    d[] = s;
    assert(d == s.length.iota);
    d.opIndexOpAssign!"+"(s);
    assert(d == iota([s.length], 0, 2));

    // lazy ndslice view
    assert(s.slicedNdField == s.length.iota);
}

template frontOf(size_t N)
{
    static if (N == 0)
        enum frontOf = "";
    else
    {
        enum i = N - 1;
        enum frontOf = frontOf!i ~ "slices[" ~ i.stringof ~ "].front!d, ";
    }
}

template frontOfSt(size_t N)
{
    static if (N == 0)
        enum frontOfSt = "";
    else
    {
        enum i = N - 1;
        enum frontOfSt = frontOfSt!i ~ "st._slices[" ~ i.stringof ~ "].front!d, ";
    }
}

///
enum bool isConcatenation(T) = is(T : Concatenation!(dim, Slices), size_t dim, Slices...);
///
enum size_t concatenationDimension(T : Concatenation!(dim, Slices), size_t dim, Slices...) = dim; 

///
struct Concatenation(size_t dim, Slices...)
    if (Slices.length > 1)
{
    @optmath:

    ///
    auto lightConst()() const @property
    {
        import std.format;
        import mir.qualifier;
        import mir.ndslice.topology: iota;
        return mixin("Concatenation!(dim, staticMap!(LightConstOf, Slices))(%(_slices[%s].lightConst,%)].lightConst)".format(_slices.length.iota));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        import mir.qualifier;
        return mixin("Concatenation!(dim, staticMap!(LightImmutableOf, Slices))(%(_slices[%s].lightImmutable,%)].lightImmutable)".format(_slices.length.iota));
    }

    /// Slices and sub-concatenations
    Slices _slices;

    package enum N = typeof(Slices[0].shape).length;

    static assert(dim < N);

    alias DeepElement = CommonType!(staticMap!(DeepElementType, Slices));

    /// Length primitive
    size_t length(size_t d = 0)() const @property
    {
        static if (d == dim)
        {
            size_t length;
            foreach(ref slice; _slices)
                length += slice.length!d;
            return length;
        }
        else
        {
            return _slices[0].length!d;
        }
    }

    /// Total elements count in the concatenation.
    size_t elementsCount()() const @property
    {
        size_t count = 1;
        foreach(i; Iota!N)
            count *= length!i;
        return count;
    }

    /// Shape of the concatenation.
    size_t[N] shape()() const @property
    {
        typeof(return) ret;
        foreach(i; Iota!N)
            ret[i] = length!i;
        return ret;
    }

    /// Multidimensional input range primitives
    bool empty(size_t d = 0)() const @property
    {
        static if (d == dim)
        {
            foreach(ref slice; _slices)
                if (slice.empty!d)
                    return true;
            return false;
        }
        else
        {
            return _slices[0].empty!d;
        }
    }

    /// ditto
    void popFront(size_t d = 0)()
    {
        static if (d == dim)
        {
            foreach(i, ref slice; _slices)
            {
                static if (i != Slices.length - 1)
                    if (slice.empty!d)
                        continue;
                return slice.popFront!d;
            }
        }
        else
        {
            foreach_reverse (ref slice; _slices)
                slice.popFront!d;
        }
    }

    /// ditto
    auto front(size_t d = 0)()
    {
        static if (d == dim)
        {
            foreach(i, ref slice; _slices)
            {
                static if (i != Slices.length - 1)
                    if (slice.empty!d)
                        continue;
                return slice.front!d;
            }
        }
        else
        {
            enum elemDim = d < dim ? dim - 1 : dim;
            alias slices = _slices;
            return mixin(`concatenation!elemDim(` ~ frontOf!(Slices.length) ~ `)`);
        }
    }

    /// Simplest multidimensional random access primitive
    auto opIndex()(size_t[N] indexes...)
    {
        foreach(i, ref slice; _slices[0 .. $-1])
        {
            ptrdiff_t diff = indexes[dim] - slice.length!dim;
            if (diff < 0)
                return slice[indexes];
            indexes[dim] = diff;
        }
        assert(indexes[dim] < _slices[$-1].length!dim);
        return _slices[$-1][indexes];
    }
}


/++
Performs `fun(st.front!d)`.

This functions is useful when `st.front!d` has not a common type and fails to compile.

Can be used instead of $(LREF .Concatenation.front)
+/
auto applyFront(size_t d = 0, alias fun, size_t dim, Slices...)(Concatenation!(dim, Slices) st)
{
    static if (d == dim)
    {
        foreach(i, ref slice; st._slices)
        {
            static if (i != Slices.length - 1)
                if (slice.empty!d)
                    continue;
            return fun(slice.front!d);
        }
    }
    else
    {
        enum elemDim = d < dim ? dim - 1 : dim;
        return fun(mixin(`concatenation!elemDim(` ~ frontOfSt!(Slices.length) ~ `)`));
    }
}

/++
Pads with a constant value.

Params:
    direction = padding direction.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.
    s = $(SUBREF slice, Slice) or ndField
    value = initial value for padding
    lengths = list of lengths

Returns: $(LREF Concatenation)

See_also: $(LREF ._concatenation) examples.
+/
auto pad(string direction = "both", S, T, size_t N)(S s, T value, size_t[N] lengths...)
    if (hasShape!S && N == typeof(S.shape).length)
{
    return .pad!([Iota!N], [Repeat!(N, direction)])(s, value, lengths);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .pad(0, [2])
        .slice;

    assert(pad == [0, 0,  1, 2, 3,  0, 0]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .pad(0, [2, 1])
        .slice;

    assert(pad == [
        [0,  0, 0,  0],
        [0,  0, 0,  0],

        [0,  1, 2,  0],
        [0,  3, 4,  0],
        
        [0,  0, 0,  0],
        [0,  0, 0,  0]]);
}

/++
Pads with a constant value.

Params:
    dimensions = dimensions to pad.
    directions = padding directions.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.

Returns: $(LREF Concatenation)

See_also: $(LREF ._concatenation) examples.
+/
template pad(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @optmath:

    /++
    Params:
        s = $(SUBREF slice, Slice) or ndField
        value = initial value for padding
        lengths = list of lengths
    Returns: $(LREF Concatenation)
    See_also: $(LREF ._concatenation) examples.
    +/
    auto pad(S, T)(S s, T value, size_t[dimensions.length] lengths...)
    {
        import mir.ndslice.topology: repeat;

        enum d = dimensions[$ - 1];
        enum q = directions[$ - 1];
        enum N = typeof(S.shape).length;

        size_t[N] len;
        auto _len = s.shape;
        foreach(i; Iota!(len.length))
            static if (i != d)
                len[i] = _len[i];
            else
                len[i] = lengths[$ - 1];

        auto p = repeat(value, len);
        static if (q == "both")
            auto r = concatenation!d(p, s, p);
        else
        static if (q == "pre")
            auto r = concatenation!d(p, s);
        else
        static if (q == "post")
            auto r = concatenation!d(s, p);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);

        static if (dimensions.length == 1)
            return r;
        else
            return .pad!(dimensions[0 .. $ - 1], directions[0 .. $ - 1])(r, value, lengths[0 .. $ -1]);
    }
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .pad!([1], ["pre"])(0, [2])
        .slice;

    assert(pad == [
        [0, 0,  1, 2],
        [0, 0,  3, 4]]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .pad!([0, 1], ["both", "post"])(0, [2, 1])
        .slice;

    assert(pad == [
        [0, 0,  0],
        [0, 0,  0],

        [1, 2,  0],
        [3, 4,  0],
        
        [0, 0,  0],
        [0, 0,  0]]);
}

/++
Pads with the wrap of the slice along the axis. The first values are used to pad the end and the end values are used to pad the beginning.

Params:
    direction = padding direction.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.
    s = $(SUBREF slice, Slice)
    lengths = list of lengths for each dimension. Each length must be less or equal to the corresponding slice length.
Returns: $(LREF Concatenation)
See_also: $(LREF ._concatenation) examples.
+/
auto padWrap(string direction = "both", Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) s, size_t[N] lengths...)
{
    return .padWrap!([Iota!N], [Repeat!(N, direction)])(s, lengths);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .padWrap([2])
        .slice;

    assert(pad == [2, 3,  1, 2, 3,  1, 2]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .padWrap([2, 1])
        .slice;

    assert(pad == [
        [2,  1, 2,  1],
        [4,  3, 4,  3],

        [2,  1, 2,  1],
        [4,  3, 4,  3],

        [2,  1, 2,  1],
        [4,  3, 4,  3]]);
}

/++
Pads with the wrap of the slice along the axis. The first values are used to pad the end and the end values are used to pad the beginning.

Params:
    dimensions = dimensions to pad.
    directions = padding directions.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.

Returns: $(LREF Concatenation)

See_also: $(LREF ._concatenation) examples.
+/
template padWrap(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @optmath:

    /++
    Params:
        s = $(SUBREF slice, Slice)
        lengths = list of lengths for each dimension. Each length must be less or equal to the corresponding slice length.
    Returns: $(LREF Concatenation)
    See_also: $(LREF ._concatenation) examples.
    +/
    auto padWrap(Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) s, size_t[dimensions.length] lengths...)
    {
        enum d = dimensions[$ - 1];
        enum q = directions[$ - 1];

        static if (d == 0 || kind != Contiguous)
        {
            alias _s = s;
        }
        else
        {
            import mir.ndslice.topology: canonical;
            auto _s = s.canonical;
        }

        assert(lengths[$ - 1] <= s.length!d);

        static if (dimensions.length != 1)
            alias next = .padWrap!(dimensions[0 .. $ - 1], directions[0 .. $ - 1]);

        static if (q == "pre" || q == "both")
        {
            auto _pre = _s;
            _pre.popFrontExactly!d(s.length!d - lengths[$ - 1]);
            static if (dimensions.length == 1)
                alias pre = _pre;
            else
                auto pre = next(_pre, lengths[0 .. $ - 1]);
        }

        static if (q == "post" || q == "both")
        {
            auto _post = _s;
            _post.popBackExactly!d(s.length!d - lengths[$ - 1]);
            static if (dimensions.length == 1)
                alias post = _post;
            else
                auto post = next(_post, lengths[0 .. $ - 1]);
        }

        static if (dimensions.length == 1)
            alias r = s;
        else
            auto r = next(s, lengths[0 .. $ - 1]);

        static if (q == "both")
            return concatenation!d(pre, r, post);
        else
        static if (q == "pre")
            return concatenation!d(pre, r);
        else
        static if (q == "post")
            return concatenation!d(r, post);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);
    }
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 3], 1)
        .padWrap!([1], ["pre"])([1])
        .slice;

    assert(pad == [
        [3,  1, 2, 3],
        [6,  4, 5, 6]]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .padWrap!([0, 1], ["both", "post"])([2, 1])
        .slice;

    assert(pad == [
        [1, 2,  1],
        [3, 4,  3],

        [1, 2,  1],
        [3, 4,  3],
        
        [1, 2,  1],
        [3, 4,  3]]);
}

/++
Pads with the reflection of the slice mirrored along the edge of the slice.

Params:
    direction = padding direction.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.
    s = $(SUBREF slice, Slice)
    lengths = list of lengths for each dimension. Each length must be less or equal to the corresponding slice length.
Returns: $(LREF Concatenation)
See_also: $(LREF ._concatenation) examples.
+/
auto padSymmetric(string direction = "both", Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) s, size_t[N] lengths...)
{
    return .padSymmetric!([Iota!N], [Repeat!(N, direction)])(s, lengths);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .padSymmetric([2])
        .slice;

    assert(pad == [2, 1,  1, 2, 3,  3, 2]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .padSymmetric([2, 1])
        .slice;

    assert(pad == [
        [3,  3, 4,  4],
        [1,  1, 2,  2],

        [1,  1, 2,  2],
        [3,  3, 4,  4],

        [3,  3, 4,  4],
        [1,  1, 2,  2]]);
}

/++
Pads with the reflection of the slice mirrored along the edge of the slice.

Params:
    dimensions = dimensions to pad.
    directions = padding directions.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.

Returns: $(LREF Concatenation)

See_also: $(LREF ._concatenation) examples.
+/
template padSymmetric(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @optmath:

    /++
    Params:
        s = $(SUBREF slice, Slice)
        lengths = list of lengths for each dimension. Each length must be less or equal to the corresponding slice length.
    Returns: $(LREF Concatenation)
    See_also: $(LREF ._concatenation) examples.
    +/
    auto padSymmetric(Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) s, size_t[dimensions.length] lengths...)
    {
        enum d = dimensions[$ - 1];
        enum q = directions[$ - 1];
        import mir.ndslice.dynamic: reversed;


        static if (kind == Contiguous)
        {
            import mir.ndslice.topology: canonical;
            auto __s = s.canonical;
        }
        else
        {
            alias __s = s;
        }

        static if (kind == Universal || d != N - 1)
        {
            auto _s = __s.reversed!d;
        }
        else
        static if (N == 1)
        {
            import mir.ndslice.topology: retro;
            auto _s = s.retro;
        }
        else
        {
            import mir.ndslice.topology: retro;
            auto _s = __s.retro.reversed!(Iota!d, Iota!(d + 1, N));
        }

        assert(lengths[$ - 1] <= s.length!d);

        static if (dimensions.length != 1)
            alias next = .padSymmetric!(dimensions[0 .. $ - 1], directions[0 .. $ - 1]);

        static if (q == "pre" || q == "both")
        {
            auto _pre = _s;
            _pre.popFrontExactly!d(s.length!d - lengths[$ - 1]);
            static if (dimensions.length == 1)
                alias pre = _pre;
            else
                auto pre = next(_pre, lengths[0 .. $ - 1]);
        }

        static if (q == "post" || q == "both")
        {
            auto _post = _s;
            _post.popBackExactly!d(s.length!d - lengths[$ - 1]);
            static if (dimensions.length == 1)
                alias post = _post;
            else
                auto post = next(_post, lengths[0 .. $ - 1]);
        }

        static if (dimensions.length == 1)
            alias r = s;
        else
            auto r = next(s, lengths[0 .. $ - 1]);

        static if (q == "both")
            return concatenation!d(pre, r, post);
        else
        static if (q == "pre")
            return concatenation!d(pre, r);
        else
        static if (q == "post")
            return concatenation!d(r, post);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);
    }
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 3], 1)
        .padSymmetric!([1], ["pre"])([2])
        .slice;

    assert(pad == [
        [2, 1,  1, 2, 3],
        [5, 4,  4, 5, 6]]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .padSymmetric!([0, 1], ["both", "post"])([2, 1])
        .slice;

    assert(pad == [
        [3, 4,  4],
        [1, 2,  2],

        [1, 2,  2],
        [3, 4,  4],
        
        [3, 4,  4],
        [1, 2,  2]]);
}

/++
Pads with the edge values of slice.

Params:
    direction = padding direction.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.
    s = $(SUBREF slice, Slice)
    lengths = list of lengths for each dimension.
Returns: $(LREF Concatenation)
See_also: $(LREF ._concatenation) examples.
+/
auto padEdge(string direction = "both", Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) s, size_t[N] lengths...)
{
    return .padEdge!([Iota!N], [Repeat!(N, direction)])(s, lengths);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .padEdge([2])
        .slice;

    assert(pad == [1, 1,  1, 2, 3,  3, 3]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .padEdge([2, 1])
        .slice;

    assert(pad == [
        [1,  1, 2,  2],
        [1,  1, 2,  2],

        [1,  1, 2,  2],
        [3,  3, 4,  4],

        [3,  3, 4,  4],
        [3,  3, 4,  4]]);
}

/++
Pads with the edge values of slice.

Params:
    dimensions = dimensions to pad.
    directions = padding directions.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.

Returns: $(LREF Concatenation)

See_also: $(LREF ._concatenation) examples.
+/
template padEdge(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @optmath:

    /++
    Params:
        s = $(SUBREF slice, Slice)
        lengths = list of lengths for each dimension.
    Returns: $(LREF Concatenation)
    See_also: $(LREF ._concatenation) examples.
    +/
    auto padEdge(Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) s, size_t[dimensions.length] lengths...)
    {
        enum d = dimensions[$ - 1];
        enum q = directions[$ - 1];

        static if (kind == Universal)
        {
            alias _s = s;
        }
        else
        static if (d != N - 1)
        {
            import mir.ndslice.topology: canonical;
            auto _s = s.canonical;
        }
        else
        {
            import mir.ndslice.topology: universal;
            auto _s = s.universal;
        }

        static if (dimensions.length != 1)
            alias next = .padEdge!(dimensions[0 .. $ - 1], directions[0 .. $ - 1]);

        static if (q == "pre" || q == "both")
        {
            auto _pre = _s;
            _pre._strides[d] = 0;
            _pre._lengths[d] = lengths[$ - 1];
            static if (dimensions.length == 1)
                alias pre = _pre;
            else
                auto pre = next(_pre, lengths[0 .. $ - 1]);

        }

        static if (q == "post" || q == "both")
        {
            auto _post = _s;
            _post._iterator += _post.backIndex!d;
            _post._strides[d] = 0;
            _post._lengths[d] = lengths[$ - 1];
            static if (dimensions.length == 1)
                alias post = _post;
            else
                auto post = next(_post, lengths[0 .. $ - 1]);
        }

        static if (dimensions.length == 1)
            alias r = s;
        else
            auto r = next( s, lengths[0 .. $ - 1]);

        static if (q == "both")
            return concatenation!d(pre, r, post);
        else
        static if (q == "pre")
            return concatenation!d(pre, r);
        else
        static if (q == "post")
            return concatenation!d(r, post);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);
    }
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 3], 1)
        .padEdge!([0], ["pre"])([2])
        .slice;

    assert(pad == [
        [1, 2, 3],
        [1, 2, 3],
        
        [1, 2, 3],
        [4, 5, 6]]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([2, 2], 1)
        .padEdge!([0, 1], ["both", "post"])([2, 1])
        .slice;

    assert(pad == [
        [1, 2,  2],
        [1, 2,  2],

        [1, 2,  2],
        [3, 4,  4],

        [3, 4,  4],
        [3, 4,  4]]);
}

/++
Iterates 1D fragments in $(SUBREF slice, Slice) or $(LREF Concatenation) in optimal for buffering way.

See_also: $(LREF ._concatenation) examples.
+/
template forEachFragment(alias pred)
{
    @optmath:

    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    {
        /++
        Specialization for slices
        Params:
            sl = $(SUBREF slice, Slice)
        +/
        void forEachFragment(Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) sl)
        {
            static if (N == 1)
            {
                pred(sl);
            }
            else
            static if (kind == Contiguous)
            {
                import mir.ndslice.topology: flattened;
                pred(sl.flattened);
            }
            else
            {
                if (!sl.empty) do
                {
                    .forEachFragment!pred(sl.front);
                    sl.popFront;
                }
                while(!sl.empty);
            }
        }

        /++
        Specialization for concatenations
        Params:
            st = $(LREF Concatenation)
        +/
        void forEachFragment(size_t dim, Slices...)(Concatenation!(dim, Slices) st)
        {
            static if (dim == 0)
            {
               foreach (i, ref slice; st._slices)
                    .forEachFragment!pred(slice);
            }
            else
            {
                if (!st.empty) do
                {
                    st.applyFront!(0, .forEachFragment!pred);
                    st.popFront;
                }
                while(!st.empty);
            }
        }
    }
    else
        alias forEachFragment = .forEachFragment!(naryFun!pred);
}

/++
Iterates elements in $(SUBREF slice, Slice) or $(LREF Concatenation)
until pred returns true.

Returns: false if pred returned false for all elements and true otherwise.

See_also: $(LREF ._concatenation) examples.
+/
template until(alias pred)
{
    @optmath:

    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    {
        /++
        Specialization for slices
        Params:
            sl = $(SUBREF slice, Slice)
        +/
        bool until(Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) sl)
        {
            static if (N == 1)
            {
                pragma(inline, false);
                alias f = pred;
            }
            else
                alias f = .until!pred;
            if (!sl.empty) do
            {
                if (f(sl.front))
                    return true;
                sl.popFront;
            }
            while(!sl.empty);
            return false;
        }

        /++
        Specialization for concatenations
        Params:
            st = $(LREF Concatenation)
        +/
        bool until(size_t dim, Slices...)(Concatenation!(dim, Slices) st)
        {
            static if (dim == 0)
            {
               foreach (i, ref slice; st._slices)
               {
                    if (.until!pred(slice))
                        return true;
               }
            }
            else
            {
                if (!st.empty) do
                {
                    if (st.applyFront!(0, .until!pred))
                        return true;
                    st.popFront;
                }
                while(!st.empty);
            }
            return false;
        }
    }
    else
        alias until = .until!(naryFun!pred);
}
