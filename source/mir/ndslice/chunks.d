/++
This is a submodule of $(MREF mir,ndslice).

The module contains $(LREF _chunks) routine.
$(LREF Chunks) structure is multidimensional random access range with slicing.

$(SUBREF slice, slicedField), $(SUBREF slice, slicedNdField) can be used to construct ndslice view on top of $(LREF Chunks).

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.chunks;

import mir.internal.utility;
import mir.math.common: optmath;
import mir.ndslice.internal;
import mir.ndslice.iterator: IotaIterator;
import mir.ndslice.slice;

import std.meta;
import std.traits;

/++
Creates $(LREF Chunks).

Params:
    Dimensions = compile time list of dimensions to chunk

See_also: $(SUBREF topology, blocks) $(SUBREF fuse, fuseCells)
+/
template chunks(Dimensions...)
    if (Dimensions.length)
{
    static if (allSatisfy!(isSize_t, Dimensions))
    /++
    Params:
        slice = Slice to chunk.
        chunkLengths = Chunk shape. It must not have a zero length.
    Returns: $(LREF Chunks).
    +/
    Chunks!([Dimensions], Iterator, N, kind == Contiguous && [Dimensions] != [0] ? Canonical : kind)
    chunks(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice, size_t[Dimensions.length] chunkLengths...)
    {
        static if (kindOf!(typeof(typeof(return).init._slice)) != kind)
        {
            import mir.ndslice.topology: canonical;
            auto p = slice.canonical;
        }
        else
        {
            alias p = slice;
        }
        auto ret = typeof(return)(chunkLengths, p);
        foreach (i; Iota!(Dimensions.length))
            ret._norm!i;
        return ret;
    }
    else
        alias chunks = .chunks!(staticMap!(toSize_t, Dimensions));
}

/// ditto
Chunks!([0], Iterator, N, kind) chunks(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice, size_t chunkLength)
{
    return .chunks!0(slice, chunkLength);
}


/// 1Dx1D
@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    import mir.ndslice.chunks: chunks, isChunks;
    import mir.ndslice.topology: iota;

    // 0 1 2 3 4 5 6 7 8 9 10
    auto sl = iota(11);
    // 0 1 2 | 3 4 5 | 6 7 8 | 9 10
    auto ch = sl.chunks(3);

    static assert(isChunks!(typeof(ch)) == [0]); // isChunks returns dimension indices

    assert(ch.length == 4);
    assert(ch.shape == cast(size_t[1])[4]);

    // 0 1 2
    assert(ch.front == iota([3], 0));
    ch.popFront;

    // 3 4 5
    assert(ch.front == iota([3], 3));
    assert(ch.length == 3);

    // 9 10
    assert(ch[$ - 1] == ch.back);
    assert(ch.back == iota([2], 9));

    ch.popBack;
    assert(ch.back == iota([3], 6));

    assert(ch[$ - 1 .. $].length == 1);
    assert(ch[$ .. $].length == 0);
    assert(ch[0 ..  0].empty);

    import std.range.primitives: isRandomAccessRange;
    static assert(isRandomAccessRange!(typeof(ch)));
}

/// 2Dx2D
@safe pure nothrow
version(mir_ndslice_test) unittest
{
    import mir.ndslice.chunks: chunks, isChunks;
    import mir.ndslice.topology: iota;

    //   0   1   2   3   4   5   6   7   8   9
    //  10  11  12  13  14  15  16  17  18  19
    //  20  21  22  23  24  25  26  27  28  29
    //  30  31  32  33  34  35  36  37  38  39
    //  40  41  42  43  44  45  46  47  48  49
    //  50  51  52  53  54  55  56  57  58  59
    //  60  61  62  63  64  65  66  67  68  69
    //  70  71  72  73  74  75  76  77  78  79
    //  80  81  82  83  84  85  86  87  88  89
    //  90  91  92  93  94  95  96  97  98  99
    // 100 101 102 103 104 105 106 107 108 109
    auto sl = iota(11, 10); // [0, 1, .. 10]

    //   ----------------   ----------------   --------
    //  |  0   1   2   3 | |  4   5   6   7 | |  8   9 |
    //  | 10  11  12  13 | | 14  15  16  17 | | 18  19 |
    //  | 20  21  22  23 | | 24  25  26  27 | | 28  29 |
    //  |----------------| |----------------| |--------|
    //  | 30  31  32  33 | | 34  35  36  37 | | 38  39 |
    //  | 40  41  42  43 | | 44  45  46  47 | | 48  49 |
    //  | 50  51  52  53 | | 54  55  56  57 | | 58  59 |
    //  |----------------| |----------------| |--------|
    //  | 60  61  62  63 | | 64  65  66  67 | | 68  69 |
    //  | 70  71  72  73 | | 74  75  76  77 | | 78  79 |
    //  | 80  81  82  83 | | 84  85  86  87 | | 88  89 |
    //  |----------------| |----------------| |--------|
    //  | 90  91  92  93 | | 94  95  96  97 | | 98  99 |
    //  |100 101 102 103 | |104 105 106 107 | |108 109 |
    //   ----------------   ----------------   --------
    // Chunk columns first, then blocks rows.
    auto ch = sl.chunks!(1, 0)(4, 3);

    assert(ch.shape == [3, 4]);
    assert(ch.slice == sl);
    assert(ch.front.slice == sl[0 .. $, 0 .. 4]);

    assert(ch.front.front == sl[0 .. 3, 0 .. 4]);

    assert(ch.front!0[1] == sl[3 .. 6, 0 .. 4]);
    assert(ch.front!1[1] == sl[0 .. 3, 4 .. 8]);

    assert (ch[$ - 1, $ - 1] == [[98, 99], [108, 109]]);

    static assert(isChunks!(typeof(ch)) == [1, 0]); // isChunks returns dimension indices

    assert(ch.length == 3);
    assert(ch.length!1 == 4);

    ch.popFront;
    assert(ch.front.front == sl[0 .. 3, 4 .. 8]);
    ch.popFront!1;
    assert(ch.front.front == sl[3 .. 6, 4 .. 8]);

    assert(ch.back.slice == sl[3 .. $, 8 .. $]);
    ch.popBack;
    assert(ch.back.slice == sl[3 .. $, 4 .. 8]);

    import std.range.primitives: isRandomAccessRange;
    static assert(isRandomAccessRange!(typeof(ch)));
}

/// 1Dx2D
version(mir_ndslice_test) unittest
{
    import mir.ndslice.chunks: chunks, isChunks;
    import mir.ndslice.topology: iota;

    //   0   1   2   3   4   5   6   7   8   9
    //  10  11  12  13  14  15  16  17  18  19
    //  20  21  22  23  24  25  26  27  28  29
    //  30  31  32  33  34  35  36  37  38  39
    auto sl = iota(4, 10); // [0, 1, .. 10]

    //   ----------------   ----------------   --------
    //  |  0   1   2   3 | |  4   5   6   7 | |  8   9 |
    //  | 10  11  12  13 | | 14  15  16  17 | | 18  19 |
    //  | 20  21  22  23 | | 24  25  26  27 | | 28  29 |
    //  | 30  31  32  33 | | 34  35  36  37 | | 38  39 |
    //   ----------------   ----------------   --------
    // Chunk columns
    auto ch = sl.chunks!1(4);

    assert(ch.slice == sl);
    assert(ch.front == sl[0 .. $, 0 .. 4]);

    assert(ch.back == sl[0 .. $, 8 .. $]);

    import std.range.primitives: isRandomAccessRange;
    static assert(isRandomAccessRange!(typeof(ch)));
}

// conversion to ndslice
version(mir_ndslice_test) unittest
{
    import mir.ndslice.slice : slicedField;
    import mir.ndslice.chunks: chunks;
    import mir.ndslice.topology: iota, map;
    import mir.math.sum: sum;

    // 0 1 2 3 4 5 6 7 8 9 10
    auto sl = iota(11);
    // 0 1 2 | 3 4 5 | 6 7 8 | 9 10
    auto ch = sl.chunks(3);
    // 3 | 12 | 21 | 19
    auto s = ch.slicedField.map!sum;
    assert(s == [3, 12, 21, 19]);
}

/++
+/
struct Chunks(size_t[] dimensions, Iterator, size_t N = 1, SliceKind kind = Contiguous)
{
@optmath:

    /++
    Chunk shape.
    +/
    size_t[dimensions.length] chunkLengths()() @property { return _chunkLengths; }
    /// ditto
    size_t[dimensions.length] _chunkLengths;

    ///
    auto lightConst()() const @property
    {
        import mir.qualifier;
        return Chunks!(dimensions, LightConstOf!Iterator, N, kind)(_chunkLengths, _slice.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        import mir.qualifier;
        return Chunks!(dimensions, LightImmutableOf!Iterator, N, kind)(_chunkLengths, _slice.lightImmutable);
    }

    alias DeepElement = Slice!(Iterator, N, kind);

    /++
    Underlying ndslice.
    It always correspond to current chunks state.
    Its shape equal to the concatenation of the all chunks.
    +/
    Slice!(Iterator, N, kind) slice()() @property { return _slice; }
    ///
    Slice!(Iterator, N, kind) _slice;

    private auto _norm(size_t dimensionIndex = 0)() @property
    {
        assert(_chunkLengths[dimensionIndex]);
        enum dimension = dimensions[dimensionIndex];
        if (_expect(_slice._lengths[dimension] < _chunkLengths[dimensionIndex], false) && _slice._lengths[dimension])
            _chunkLengths[dimensionIndex] = _slice._lengths[dimension];
    }

    private auto _wrap(size_t dimensionIndex, S)(ref S ret)
    {
        static if (dimensions.length == 1)
        {
            return ret;
        }
        else
        {
            size_t[dimensions.length - 1] rcl;
            foreach (i, j; AliasSeq!(Iota!dimensionIndex, Iota!(dimensionIndex + 1, dimensions.length)))
                rcl[i] = _chunkLengths[j];
            enum newDims = dimensions[0 .. dimensionIndex] ~ dimensions[dimensionIndex + 1 .. $];
            return .Chunks!(newDims, Iterator, N, typeof(ret).kind)(rcl, ret);
        }
    }

    private ref size_t sliceLength(size_t dimensionIndex)() @property
    {
        enum dimension = dimensions[dimensionIndex];
        return _slice._lengths[dimension];
    }

    /// ndslice-like primitives
    bool empty(size_t dimensionIndex = 0)() const @property
        if (dimensionIndex < dimensions.length)
    {
        enum dimension = dimensions[dimensionIndex];
        return _slice.empty!(dimension);
    }

    ///
    size_t[dimensions.length] shape()() const @property
    {
        typeof(return) ret;
        foreach(dimensionIndex; Iota!(ret.length))
        {
            enum dimension = dimensions[dimensionIndex];
            auto l = _slice._lengths[dimension];
            auto n = _chunkLengths[dimensionIndex];
            ret[dimensionIndex] = l / n + (l % n != 0);
        }
        return ret;
    }

    /// ditto
    size_t length(size_t dimensionIndex = 0)() const @property
        if (dimensionIndex < dimensions.length)
    {
        enum dimension = dimensions[dimensionIndex];
        auto l = _slice._lengths[dimension];
        auto n = _chunkLengths[dimensionIndex];
        return l / n + (l % n != 0);
    }

    /// ditto
    auto front(size_t dimensionIndex = 0)() @property
        if (dimensionIndex < dimensions.length)
    {
        enum dimension = dimensions[dimensionIndex];
        assert(_chunkLengths[dimensionIndex] <= _slice._lengths[dimension]);
        auto ret = _slice.selectFront!dimension(_chunkLengths[dimensionIndex]);
        return _wrap!dimensionIndex(ret);
    }

    ///
    auto back(size_t dimensionIndex = 0)() @property
        if (dimensionIndex < dimensions.length)
    {
        assert(!empty!dimensionIndex);
        enum dimension = dimensions[dimensionIndex];
        auto l = _slice._lengths[dimension];
        auto n = _chunkLengths[dimensionIndex];
        auto rshift = l % n;
        rshift = !rshift ? n : rshift;
        auto len = _slice._lengths[dimension];
        auto ret = _slice.select!dimension(len - rshift, len);
        return _wrap!dimensionIndex(ret);
    }

    /// ditto
    void popFront(size_t dimensionIndex = 0)()
        if (dimensionIndex < dimensions.length)
    {
        enum dimension = dimensions[dimensionIndex];
        assert(!empty!dimensionIndex);
        _slice.popFrontExactly!dimension(_chunkLengths[dimensionIndex]);
        _norm!dimensionIndex;
    }

    /// ditto
    void popBack(size_t dimensionIndex = 0)()
        if (dimensionIndex < dimensions.length)
    {
        assert(!empty!dimensionIndex);
        enum dimension = dimensions[dimensionIndex];
        auto l = _slice._lengths[dimension];
        auto n = _chunkLengths[dimensionIndex];
        auto rshift = l % n;
        rshift = !rshift ? n : rshift;
        _slice.popBackExactly!dimension(rshift);
        _norm!dimensionIndex;
   }

    /// ditto
    Slice!(IotaIterator!size_t) opSlice(size_t dimensionIndex)(size_t i, size_t j) const
        if (dimensionIndex < dimensions.length)
    in
    {
        assert(i <= j,
            "Chunks.opSlice!" ~ dimensionIndex.stringof ~ ": the left opSlice boundary must be less than or equal to the right bound.");
        enum errorMsg = ": the right opSlice boundary must be less than or equal to the length of the given dimensionIndex.";
        assert(j <= length!dimensionIndex,
              "Chunks.opSlice!" ~ dimensionIndex.stringof ~ errorMsg);
    }
    do
    {
        return typeof(return)(j - i, typeof(return).Iterator(i));
    }

    /// ditto
    ChunksSlice!() opSlice(size_t dimensionIndex)(size_t i, ChunksDollar!() j) const
        if (dimensionIndex < dimensions.length)
    in
    {
        assert(i <= j,
            "Chunks.opSlice!" ~ dimensionIndex.stringof ~ ": the left opSlice boundary must be less than or equal to the right bound.");
        enum errorMsg = ": the right opSlice boundary must be less than or equal to the length of the given dimensionIndex.";
        assert(j <= length!dimensionIndex,
              "Chunks.opSlice!" ~ dimensionIndex.stringof ~ errorMsg);
    }
    do
    {
        return typeof(return)(i, j);
    }

    /// ditto
    ChunksDollar!() opDollar(size_t dimensionIndex)() @property
    {
        enum dimension = dimensions[dimensionIndex];
        return ChunksDollar!()(_slice._lengths[dimension], _chunkLengths[dimensionIndex]);
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices)
        if (Slices.length <= dimensions.length)
    {
        static if (slices.length == 0)
        {
            return this;
        }
        else
        {
            alias slice = slices[0];
            alias S = Slices[0];
            static if (isIndex!S)
            {
                auto next = this.select!0(slice);
            }
            else
            static if (is_Slice!S)
            {
                auto i = slice._iterator._index;
                auto j = i + slice._lengths[0];
                auto next = this.select!0(i, j);
            }
            else
            {
                auto next = this.select!0(slice.i, slice.j);
            }
            static if (slices.length > 1)
            {
                return next[slices[1 .. $]];
            }
            else
            {
                return next;
            }
        }
    }

    /// ditto
    auto opIndex()(size_t[dimensions.length] index)
    {
        auto next = this.select!0(index[0]);
        static if (dimensions.length == 1)
        {
            return next;
        }
        else
        {
            return next[index[1 .. $]];
        }
    }

    /// ditto
    auto save()() @property
    {
        return this;
    }

    ///
    auto select(size_t dimensionIndex = 0)(size_t index) @property
        if (dimensionIndex < dimensions.length)
    {
        enum dimension = dimensions[dimensionIndex];
        auto chl = _chunkLengths[dimensionIndex];
        auto shiftL = chl * index;
        assert(shiftL <= _slice._lengths[dimension]);
        auto shiftR = shiftL + chl;
        if (_expect(shiftR > _slice._lengths[dimension], false))
        {
            shiftR = _slice._lengths[dimension];
        }
        auto ret = _slice.select!dimension(shiftL, shiftR);
        return _wrap!dimensionIndex(ret);
    }

    /// ditto
    auto select(size_t dimensionIndex = 0)(size_t i, size_t j) @property
        if (dimensionIndex < dimensions.length)
    {
        assert(i <= j);
        enum dimension = dimensions[dimensionIndex];
        auto chl = _chunkLengths[dimensionIndex];
        auto shiftL = chl * i;
        auto shiftR = chl * j;
        assert(shiftL <= _slice._lengths[dimension]);
        assert(shiftR <= _slice._lengths[dimension]);
        if (_expect(shiftR > _slice._lengths[dimension], false))
        {
            shiftR = _slice._lengths[dimension];
            if (_expect(shiftL > _slice._lengths[dimension], false))
            {
                shiftL = _slice._lengths[dimension];
            }
        }
        auto ret = _slice.select!dimension(shiftL, shiftR);
        import std.meta: aliasSeqOf;
        return ret.chunks!(aliasSeqOf!dimensions)(_chunkLengths);
    }

    // undocumented
    auto select(size_t dimensionIndex = 0)(ChunksSlice!() sl) @property
        if (dimensionIndex < dimensions.length)
    {
        assert(sl.i <= _slice._lengths[dimension]);
        assert(sl.chunkLength == _chunkLengths[dimensionIndex]);
        assert(sl.length == _slice._lengths[dimension]);

        enum dimension = dimensions[dimensionIndex];
        auto chl = _chunkLengths[dimensionIndex];
        auto len = sl.i * chl;
        assert(len <= _slice._lengths[dimension]);
        if (_expect(len > _slice._lengths[dimension], false))
            len = _slice._lengths[dimension];
        auto ret = _slice.selectBack!dimension(len);
        import std.meta: aliasSeqOf;
        return ret.chunks!(aliasSeqOf!dimensions)(_chunkLengths);
    }
}

// undocumented
struct ChunksSlice()
{
    size_t i;
    ChunksDollar!() j;
}

// undocumented
struct ChunksDollar()
{
    size_t length;
    size_t chunkLength;
    size_t value()() @property
    {
        return length / chunkLength + (length % chunkLength != 0);
    }
    alias value this;
}

/++
Checks if T is $(LREF Chunks) type.
Returns:
    array of dimension indices.
+/
template isChunks(T)
{
    static if (is(T : Chunks!(dimensions, Iterator, N, kind), size_t[] dimensions, Iterator, size_t N, SliceKind kind))
        enum isChunks = dimensions;
    else
        enum isChunks = size_t[].init;
}

///
version(mir_ndslice_test) unittest
{
    import mir.ndslice.chunks: chunks, isChunks;
    import mir.ndslice.topology: iota;

    static assert(isChunks!int == null);
    static assert(isChunks!(typeof(iota(20, 30).chunks!(1, 0)(3, 7))) == [1, 0]);
}

/++
Evaluates `popFront!dimmensionIndex` for multiple $(LREF Chunks) structures at once.
All chunks structures must have for the appropriate dimension the same chunk lengths and the same underlying slice lengths.

Params:
    dimmensionIndex = dimensionIndex
    master = the fist chunks structure
    followers = following chunks structures
+/
void popFrontTuple(size_t dimmensionIndex = 0, Master, Followers...)(ref Master master, ref Followers followers)
    if (isChunks!Master && allSatisfy!(isChunks, Followers))
in
{
    foreach (ref follower; followers)
    {
        assert(follower.sliceLength!dimmensionIndex == master.sliceLength!dimmensionIndex);
        assert(follower._chunkLengths[dimmensionIndex] == master._chunkLengths[dimmensionIndex]);
    }
}
do
{
    master._slice.popFrontExactly!(isChunks!Master[dimmensionIndex])(master._chunkLengths[dimmensionIndex]);
    foreach (i, ref follower; followers)
    {
        follower._slice.popFrontExactly!(isChunks!(Followers[i])[dimmensionIndex])(master._chunkLengths[dimmensionIndex]);
        // hint for optimizer
        follower.sliceLength!dimmensionIndex = master.sliceLength!dimmensionIndex;
    }
    if (_expect(master.sliceLength!dimmensionIndex < master._chunkLengths[dimmensionIndex], false) && master.sliceLength!dimmensionIndex)
    {
        master._chunkLengths[dimmensionIndex] = master.sliceLength!dimmensionIndex;
        foreach(ref follower; followers)
        {
            follower._chunkLengths[dimmensionIndex] = master._chunkLengths[dimmensionIndex];
        }
    }
}

///
version(mir_ndslice_test) unittest
{
    import mir.ndslice.chunks: chunks;
    import mir.ndslice.topology: iota;

    auto a = iota(10, 20).chunks!(0, 1)(3, 7);
    auto b = iota(20, 10).chunks!(1, 0)(3, 7);

    auto as = a;
    auto bs = b;

    as.popFront;
    bs.popFront;

    popFrontTuple(a, b);

    assert(as.slice == a.slice);
    assert(bs.slice == b.slice);

    assert(as.chunkLengths == a.chunkLengths);
    assert(bs.chunkLengths == b.chunkLengths);
}
