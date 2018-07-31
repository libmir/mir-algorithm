/**
 ************ Mir-Algorithm ************

The module provides wrappers for $(SUBREF slice, Slice) that
can be used as arguments for C++ functions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
*/
#include <cstddef>

// It is out of ndslice namespace because of a DMD mangling bug.
enum class mir_slice_kind : int
{
    universal = 0,
    canonical = 1,
    contiguous = 2
};

template <
    typename Iterator,
    size_t N = 1,
    mir_slice_kind kind = mir_slice_kind::contiguous
>
struct mir_slice
{
    size_t _lengths[N];
    ptrdiff_t _strides[kind == mir_slice_kind::universal ? N : kind == mir_slice_kind::canonical ? N - 1 : 0];
    Iterator _iterator;
};
