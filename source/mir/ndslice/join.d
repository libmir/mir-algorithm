/++
This is a submodule of $(MREF mir,ndslice).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2018-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.join;

import mir.ndslice.slice;
import mir.primitives;
import mir.internal.utility;
import std.traits;

/++
Params: Nd-range of Nd-cells
Returns: Nd-slice composed of joined cells.
+/
auto join(S)(S cells)
{
    alias T = DeepElementType!(DeepElementType!S);
    alias UT = Unqual!T;
    if (__ctfe)
    {
        import mir.ndslice.allocation: slice;
        auto ret = cells.joinShape.slice!UT;
        ret.joinAssign!"a = b" = cells;
        static if (is(T == immutable))
            return (cast(immutable) ret)[];
        else
        static if (is(T == const))
            return (cast(const) ret)[];
        else
            return ret;
    }
    else
    {
        import mir.ndslice.allocation: uninitSlice;
        import std.backdoor;
        auto ret = cells.joinShape.uninitSlice!UT;
        ret.joinAssign!emplaceRef = cells;
        static if (is(T == immutable))
            return (cast(immutable) ret)[];
        else
        static if (is(T == const))
            return (cast(const) ret)[];
        else
            return ret;
    }
}

/// 1D
unittest
{
    import mir.ndslice.topology: iota;
    enum ar = [[0, 1], [], [2, 3, 4, 5], [6], [7, 8, 9]];
    static assert ([[0, 1], [], [2, 3, 4, 5], [6], [7, 8, 9]].join == 10.iota);
    assert (ar.join == 10.iota);
}

/// 2D
unittest
{
    import mir.ndslice.topology: iota;
    import mir.ndslice.chunks;

    auto sl = iota(11, 17);
    assert(sl.chunks!(0, 1)(3, 4).join == sl);
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
    import mir.ndslice.topology: canonical;
    static if (kind == Contiguous)
        joinEmplaceImpl!(naryFun!fun, 0, packs[0])(to.canonical, cells);
    else
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
        import mir.ndslice.topology: repeat;
        enum expr = "e" ~ ".front".repeat(N).join.field;
        foreach (i; Iota!N)
            for (auto e = cells.save; !e.empty!i; e.popFront!i)
                ret[i] += mixin(expr).length!i;
    }
    return ret;
}

private auto joinEmplaceImpl(alias fun, size_t i, size_t N, SliceKind kind, size_t[] packs, Iterator, S)(Slice!(kind, packs, Iterator) to, S cells)
    if (packs.length == 1)
{
    do
    {
        auto from = cells.front;
        static if (N == 1)
        {
            auto n = from.length!i;
        }
        else
        {
            import mir.ndslice.topology: repeat;
            enum expr = "from" ~ ".front".repeat(N - 1 - i).join.field;
            auto n = mixin(expr).length!i;
        }
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
