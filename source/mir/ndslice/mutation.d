/++
$(H2 Multidimensional mutation algorithms)

This is a submodule of $(MREF mir,ndslice).

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2020-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.mutation;

import mir.ndslice.slice: Slice, SliceKind;

/++
Copies n-dimensional minor.
+/
void copyMinor(size_t N, IteratorFrom, SliceKind KindFrom, IteratorTo, SliceKind KindTo, IndexIterator)(
    Slice!(IteratorFrom, N, KindFrom) from,
    Slice!(IteratorTo, N, KindTo) to,
    Slice!IndexIterator[N] indexes...
)
in {
    import mir.internal.utility: Iota;
    static foreach (i; Iota!N)
        assert(indexes[i].length == to.length!i);
}
do {
    static if (N == 1)
        to[] = from[indexes[0]];
    else
    foreach (i; 0 .. indexes[0].length)
    {
        copyMinor!(N - 1)(from[indexes[0][i]], to[i], indexes[1 .. N]);
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice;
    //  0  1  2  3
    //  4  5  6  7
    //  8  9 10 11
    auto a = iota!int(3, 4);
    auto b = slice!int(2, 2);
    copyMinor(a, b, [2, 1].sliced, [0, 3].sliced);
    assert(b == [[8, 11], [4, 7]]);
}

/++
Reverses data in the 1D slice.
+/
void reverseInPlace(Iterator)(Slice!Iterator slice)
{
    import mir.utility : swap;
    foreach (i; 0 .. slice.length / 2)
        swap(slice[i], slice[$ - (i + 1)]);
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice;
    auto s = 5.iota.slice;
    s.reverseInPlace;
    assert([4, 3, 2, 1, 0]);
}
