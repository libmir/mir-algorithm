/++
$(H2 Multidimensional mutation algorithms)

This is a submodule of $(MREF mir,ndslice).

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
$(T2 all, Checks if all elements satisfy to a predicate.)
$(T2 any, Checks if at least one element satisfy to a predicate.)
$(T2 cmp, Compares two slices.)
$(T2 count, Counts elements in a slices according to a predicate.)
$(T2 each, Iterates all elements.)
$(T2 equal, Compares two slices for equality.)
$(T2 find, Finds backward index.)
$(T2 findIndex, Finds index.)
$(T2 minmaxIndex, Finds indexes of the minimum and the maximum.)
$(T2 minmaxPos, Finds backward indexes of the minimum and the maximum.)
$(T2 minIndex, Finds index of the minimum.)
$(T2 maxIndex, Finds index of the maximum.)
$(T2 minPos, Finds backward index of the minimum.)
$(T2 maxPos, Finds backward index of the maximum.)
$(T2 reduce, Accumulates all elements.)
)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.mutation;

import mir.ndslice.slice;

/++
Transposes square matrix in place.

Params:
    matrix = square matrix
+/
void transposeInPlace(SliceKind kind, Iterator)(Slice!(kind, [2], Iterator) matrix)
in
{
    assert(matrix.length!0 == matrix.length!1);
}
body
{
    static if (kind == Contiguous)
    {
        import mir.ndslice.topology: canonical;
        .transposeInPlace(matrix.canonical);
    }
    else
    {
        if (!matrix.empty)
        do
        {
            import mir.ndslice.algorithm: eachImpl;
            import mir.utility: swap;
            eachImpl!swap(matrix.front!1, matrix.front!0);
            matrix.popFront!1;
            matrix.popFront!0;
        }
        while (matrix.length);
    }
}

///
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota, universal;
    import mir.ndslice.dynamic: transposed;

    auto m = iota(4, 4).slice;

    m.transposeInPlace;

    assert(m == iota(4, 4).universal.transposed);
}
