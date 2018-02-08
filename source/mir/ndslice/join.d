module mir.ndslice.join;

import mir.ndslice.slice;
import mir.primitives;

/++
Params: ndrange of cells
Returns: tensor composed of joined cells
+/
auto join(S)(S cells)
{
    if (__ctfe)
    {
        import mir.ndslice.allocation: slice;
        auto ret = cells.joinShape.slice!(DeepElementType!(DeepElementType!S));
        return ret.joinAssign!"a = b" = cells;
    }
    else
    {
        import mir.ndslice.allocation: uninitSlice;
        import std.backdoor;
        auto ret = cells.joinShape.uninitSlice!(DeepElementType!(DeepElementType!S));
        return ret.joinAssign!emplaceRef = cells;
    }
}

/// 1D
unittest
{
    import mir.ndslice.topology: iota, map;
    enum ar = [[0, 1], [], [2, 3, 4, 5], [6], [7, 8, 9]];
    // static assert ([[0, 1], [], [2, 3, 4, 5], [6], [7, 8, 9]].join == 10.iota);
    assert (ar.join == 10.iota);
}

/++

+/
auto joinAssign(alias fun = "a = b", SliceKind kind, size_t[] packs, Iterator, S)(Slice!(kind, packs, Iterator) to, S cells)
    if (packs.length == 1)
{
    assert(to.shape == cells.joinShape, "'cells.joinShape' should be equal to 'to.shape'");

    if (cells.anyEmpty)
        goto R;

    import mir.functional: naryFun;
    joinEmplaceImpl!(naryFun!fun, 0, packs[0])(to, cells);
    R: return to;
}

/++

+/
size_t[S.init.shape.length] joinShape(S)(S cells) @property
{
    typeof(return) ret;
    enum N = ret.length;
    static if (N == 1)
    {
        foreach (ref e; cells)
            ret[0] += e.length;
    }
    else
    {
        foreach (i; Iota!N)
            foreach (ref e; cells.front!i)
                ret[i] += e.length!i;
    }
    return ret;
}

private auto joinEmplaceImpl(alias fun, size_t i, size_t N, SliceKind kind, size_t[] packs, Iterator, S)(Slice!(kind, packs, Iterator) to, S cells)
    if (packs.length == 1)
{
    assert(to.shape == cells.joinShape, "'cells.joinShape' should be equal to 'to.shape'");
    do
    {
        auto from = cells.front;
        auto n = from.length;
        assert (to.length!i >= n);
        static if (i + 1 == N)
        {
            import mir.ndslice.algorithm: each;
            each!fun(to.selectFront!i(n), from);
        }
        else
        {
            .joinEmplaceImpl!(fun, i + 1, N)(to.selectFront!i(n), from);
        }
        to.popFrontExactly!i(n);
        cells.popFront;
    }
    while(!cells.empty);
    return to;
}
