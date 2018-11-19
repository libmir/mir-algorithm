#ifndef MIR_SERIES

#define MIR_SERIES

#include "mir/ndslice.h"

template  <
    typename Index,
    typename Data
>
struct mir_observation
{
    Index _index;
    Data _data;
}

template <
    typename IndexIterator,
    typename Iterator,
    mir_size_t N = 1,
    mir_slice_kind kind = mir_slice_kind::contiguous
>
struct mir_series
{
    mir_slice<Iterator, N, kind> _data;
    IndexIterator _index;
};

#endif
