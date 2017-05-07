/++
$(H2 Multidimensional mutation algorithms)

This is a submodule of $(MREF mir,ndslice).

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
$(T2 transposeInPlace, Transposes square matrix in place.)
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
