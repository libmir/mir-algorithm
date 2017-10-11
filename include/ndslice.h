/**
 ************ Mir-Algorithm ************

The module provides wrappers for $(SUBREF slice, Slice) that
can be used as arguments for C++ functions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
*/

/* * * * EXAMPLE * * *

#include <ndslice.h>

typedef ndslice::CppSlice<Contiguous, 1, double*> Vec;
typedef ndslice::CppSlice<Contiguous, 2, double*> Mat;

int main()
{
    double data[] = {
        3.0, 4.0, 5.0,
        3.5, 4.5, 5.5,
    };
    Mat mat;
    mat._lengths[0] = 2;
    mat._lengths[1] = 3;
    //mat._strides[..] -- no strides for contiguous ndslices
    mat._iterator = data;
    return 0;
}

*/

#include <cstddef>
#include <cassert>

// It is out of ndslice namespace because of a DMD mangling bug.
enum SliceKind
{
    Universal,
    Canonical,
    Contiguous,
};

namespace ndslice {

template <SliceKind kind, int N, typename Iterator>
struct CppSlice
{
    size_t _lengths[N];
    ptrdiff_t _strides[kind == Universal ? N : kind == Canonical ? N - 1 : 0];
    Iterator _iterator;
};

} //namespace mir
