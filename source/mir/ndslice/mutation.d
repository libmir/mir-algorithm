/++
$(H2 Multidimensional mutation algorithms)

This is a submodule of $(MREF mir,ndslice).

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilya Yaroshenko

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
    Slice!IndexIterator[N] indices...
)
in {
    import mir.internal.utility: Iota;
    static foreach (i; Iota!N)
        assert(indices[i].length == to.length!i);
}
do {
    static if (N == 1)
        to[] = from[indices[0]];
    else
    foreach (i; 0 .. indices[0].length)
    {
        copyMinor!(N - 1)(from[indices[0][i]], to[i], indices[1 .. N]);
    }
}

///
version(mir_ndslice_test)
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
version(mir_ndslice_test)
@safe pure nothrow
unittest
{
    import mir.ndslice;
    auto s = 5.iota.slice;
    s.reverseInPlace;
    assert([4, 3, 2, 1, 0]);
}
