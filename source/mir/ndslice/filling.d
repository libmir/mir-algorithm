/++
This is a submodule of $(MREF mir,ndslice).

Initialisation routines.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: 2019 Symmetry Investments Group and Kaleidic Associates Advisory Limited.
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.filling;

import mir.ndslice.slice: Slice, SliceKind;

/++
Fills a matrix with the terms of a geometric progression in each row.
Params:
    matrix = `m × n` matrix to fill
    vec = vector of progression coefficients length of `m`
See_also: $(LINK2 https://en.wikipedia.org/wiki/Vandermonde_matrix, Vandermonde matrix)
+/
void fillVandermonde(F, SliceKind matrixKind, SliceKind kind)(Slice!(F*, 2, matrixKind) matrix, Slice!(const(F)*, 1, kind) vec)
in {
    assert(matrix.length == vec.length);
}
do {
    import mir.conv: to;

    foreach (v; matrix)
    {
        F a = vec.front;
        vec.popFront;
        F x = to!F(1);
        foreach (ref e; v)
        {
            e = x;
            x *= a;
        }
    }
}

///
@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: uninitSlice;
    auto x = [1.0, 2, 3, 4, 5].sliced;
    auto v = uninitSlice!double(x.length, x.length);
    v.fillVandermonde(x);
    assert(v ==
        [[  1.0,   1,   1,   1,   1],
         [  1.0,   2,   4,   8,  16],
         [  1.0,   3,   9,  27,  81],
         [  1.0,   4,  16,  64, 256],
         [  1.0,   5,  25, 125, 625]]);
}
