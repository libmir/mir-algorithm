/++
This is a submodule of $(MREF mir, ndslice).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.stack;

import std.traits;
import std.meta;

import mir.ndslice.internal;
import mir.ndslice.slice;
import mir.internal.utility;
import mir.primitives;

@fastmath:

/++
Creates a $(LREF Stack) view of multiple slices.

Can be used in combination with itself, $(LREF until), $(SUBREF, allocation, slice),
and $(SUBREF slice, Slice) assignment.
until pred returns true.

Returns: true if an element was 

Params:
    slices = tuple of slices and stacks. All slices and stacks must have the same dimension count.

Returns: $(LREF Stack).
+/
Stack!(dim, Slices) stack(size_t dim = 0, Slices...)(Slices slices)
{
    return typeof(return)(slices);
}

/// Multidimensional
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

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
    auto s = stack(stack!1(a, b), c);

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
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    size_t i;
    auto a = 3.iota;
    auto b = iota([6], a.length);
    auto s = stack(a, b);
    assert(s.length == a.length + b.length);
    // fast iteration with until
    s.until!((elem){ assert(elem == i++); return false; });
    // allocation with slice
    assert(s.slice == s.length.iota);
    // 1D or multidimensional assignment
    auto d = slice!double(s.length);
    d[] = s;
    assert(d == s.length.iota);
    d[] += s;
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
enum bool isStack(T) = is(T : Stack!(dim, Slices), size_t dim, Slices...);
///
enum size_t stackDimension(T : Stack!(dim, Slices), size_t dim, Slices...) = dim; 

///
struct Stack(size_t dim, Slices...)
    if (Slices.length > 1)
{
    @fastmath:

    /// Slices and sub-stacks
    Slices _slices;

    package enum N = typeof(Slices[0].shape).length;

    static assert(dim < N);

    package alias DeepElemType = CommonType!(staticMap!(DeepElementType, Slices));

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

    /// Total elements count in the stack.
    size_t elementsCount()() const @property
    {
        size_t count = 1;
        foreach(i; Iota!N)
            count *= length!i;
        return count;
    }

    /// Shape of the stack.
    size_t[N] shape()() const @property
    {
        typeof(return) ret = void;
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
            return mixin(`stack!elemDim(` ~ frontOf!(Slices.length) ~ `)`);
        }
    }

    /// Simplest multidimensional random access primitive
    // auto ref
    auto opIndex(size_t[N] indexes...)
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

auto applyFront(size_t d = 0, alias fun, size_t dim, Slices...)(Stack!(dim, Slices) st)
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
        return fun(mixin(`stack!elemDim(` ~ frontOfSt!(Slices.length) ~ `)`));
    }
}

/++
Multidimensional padding view.

Params:
    direction = padding direction.
        Direction can be one of the following values: `"both"`, `"pre"`, and `"post"`.
    s = $(SUBREF slice, Slice) or ndField
    value = initial value for padding
    lengths = list of lengths

Returns: $(LREF Stack)

See_also: $(LREF stack) examples.
+/
auto pad(string direction = "both", S, T, size_t N)(S s, T value, size_t[N] lengths...)
    if (hasShape!S && N == typeof(S.shape).length)
{
    return .pad!([Iota!N], [Repeat!(N, direction)])(s, value, lengths);
}

///
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .pad(0, [2])
        .slice;

    assert(pad == [0, 0,  1, 2, 3,  0, 0]);
}

///
unittest
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

Returns: $(LREF Stack)

See_also: $(LREF stack) examples.
+/
template pad(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @fastmath:

    /++
    Params:
        s = $(SUBREF slice, Slice) or ndField
        value = initial value for padding
        lengths = list of lengths
    Returns: $(LREF Stack)
    See_also: $(LREF stack) examples.
    +/
    auto pad(S, T)(S s, T value, size_t[dimensions.length] lengths...)
    {
        import mir.ndslice.topology: repeat;

        enum d = dimensions[$ - 1];
        enum q = directions[$ - 1];
        enum N = typeof(S.shape).length;

        size_t[N] len = void;
        auto _len = s.shape;
        foreach(i; Iota!(len.length))
            static if (i != d)
                len[i] = _len[i];
            else
                len[i] = lengths[$ - 1];

        auto p = repeat(value, len);
        static if (q == "both")
            auto r = stack!d(p, s, p);
        else
        static if (q == "pre")
            auto r = stack!d(p, s);
        else
        static if (q == "post")
            auto r = stack!d(s, p);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);

        static if (dimensions.length == 1)
            return r;
        else
            return .pad!(dimensions[0 .. $ - 1], directions[0 .. $ - 1])(r, value, lengths[0 .. $ -1]);
    }
}

///
unittest
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
unittest
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
Returns: $(LREF Stack)
See_also: $(LREF stack) examples.
+/
auto padWrap(string direction = "both", SliceKind kind, size_t[] packs, Iterator, size_t N)(Slice!(kind, packs, Iterator) s, size_t[N] lengths...)
    if (N == packs[0])
{
    return .padWrap!([Iota!N], [Repeat!(N, direction)])(s, lengths);
}

///
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .padWrap([2])
        .slice;

    assert(pad == [2, 3,  1, 2, 3,  1, 2]);
}

///
unittest
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

Returns: $(LREF Stack)

See_also: $(LREF stack) examples.
+/
template padWrap(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @fastmath:

    /++
    Params:
        s = $(SUBREF slice, Slice)
        lengths = list of lengths for each dimension. Each length must be less or equal to the corresponding slice length.
    Returns: $(LREF Stack)
    See_also: $(LREF stack) examples.
    +/
    auto padWrap(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) s, size_t[dimensions.length] lengths...)
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
            return stack!d(pre, r, post);
        else
        static if (q == "pre")
            return stack!d(pre, r);
        else
        static if (q == "post")
            return stack!d(r, post);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);
    }
}

///
unittest
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
unittest
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
Returns: $(LREF Stack)
See_also: $(LREF stack) examples.
+/
auto padSymmetric(string direction = "both", SliceKind kind, size_t[] packs, Iterator, size_t N)(Slice!(kind, packs, Iterator) s, size_t[N] lengths...)
    if (N == packs[0])
{
    return .padSymmetric!([Iota!N], [Repeat!(N, direction)])(s, lengths);
}

///
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .padSymmetric([2])
        .slice;

    assert(pad == [2, 1,  1, 2, 3,  3, 2]);
}

///
unittest
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

Returns: $(LREF Stack)

See_also: $(LREF stack) examples.
+/
template padSymmetric(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @fastmath:

    /++
    Params:
        s = $(SUBREF slice, Slice)
        lengths = list of lengths for each dimension. Each length must be less or equal to the corresponding slice length.
    Returns: $(LREF Stack)
    See_also: $(LREF stack) examples.
    +/
    auto padSymmetric(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) s, size_t[dimensions.length] lengths...)
        if (packs.length == 1)
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

        static if (kind == Universal || d != packs[0] - 1 || packs.length > 1)
        {
            auto _s = __s.reversed!d;
        }
        else
        static if (packs[0] == 1)
        {
            import mir.ndslice.topology: retro;
            auto _s = s.retro;
        }
        else
        {
            import mir.ndslice.topology: retro;
            auto _s = __s.retro.reversed!(Iota!d, Iota!(d + 1, packs[0]));
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
            return stack!d(pre, r, post);
        else
        static if (q == "pre")
            return stack!d(pre, r);
        else
        static if (q == "post")
            return stack!d(r, post);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);
    }
}

///
unittest
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
unittest
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
Returns: $(LREF Stack)
See_also: $(LREF stack) examples.
+/
auto padEdge(string direction = "both", SliceKind kind, size_t[] packs, Iterator, size_t N)(Slice!(kind, packs, Iterator) s, size_t[N] lengths...)
    if (N == packs[0])
{
    return .padEdge!([Iota!N], [Repeat!(N, direction)])(s, lengths);
}

///
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    auto pad = iota([3], 1)
        .padEdge([2])
        .slice;

    assert(pad == [1, 1,  1, 2, 3,  3, 3]);
}

///
unittest
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

Returns: $(LREF Stack)

See_also: $(LREF stack) examples.
+/
template padEdge(size_t[] dimensions, string[] directions)
    if (dimensions.length && dimensions.length == directions.length)
{
    @fastmath:

    /++
    Params:
        s = $(SUBREF slice, Slice)
        lengths = list of lengths for each dimension.
    Returns: $(LREF Stack)
    See_also: $(LREF stack) examples.
    +/
    auto padEdge(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) s, size_t[dimensions.length] lengths...)
    {
        enum d = dimensions[$ - 1];
        enum q = directions[$ - 1];

        static if (kind == Universal || kind == Canonical && packs.length > 1)
        {
            alias _s = s;
        }
        else
        static if (packs.length > 1 || d != packs[0] - 1)
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
            return stack!d(pre, r, post);
        else
        static if (q == "pre")
            return stack!d(pre, r);
        else
        static if (q == "post")
            return stack!d(r, post);
        else
        static assert(0, `allowed directions are "both", "pre", and "post"`);
    }
}

///
unittest
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
unittest
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
Iterates 1D fragments in $(SUBREF slice, Slice) or $(LREF Stack) in optimal for buffering way.

See_also: $(LREF stack) examples.
+/
template forEachFragment(alias pred)
{
    @fastmath:

    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    {
        /++
        Specialization for slices
        Params:
            sl = $(SUBREF slice, Slice)
        +/
        void forEachFragment(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) sl)
        {
            static if (packs[0] == 1)
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
        Specialization for stacks
        Params:
            st = $(LREF Stack)
        +/
        void forEachFragment(size_t dim, Slices...)(Stack!(dim, Slices) st)
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
Iterates elements in $(SUBREF slice, Slice) or $(LREF Stack)
until pred returns true.

Returns: false if pred returned false for all elements and true otherwise.

See_also: $(LREF stack) examples.
+/
template until(alias pred)
{
    @fastmath:

    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    {
        /++
        Specialization for slices
        Params:
            sl = $(SUBREF slice, Slice)
        +/
        bool until(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) sl)
        {
            static if (packs[0] == 1)
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
        Specialization for stacks
        Params:
            st = $(LREF Stack)
        +/
        bool until(size_t dim, Slices...)(Stack!(dim, Slices) st)
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
