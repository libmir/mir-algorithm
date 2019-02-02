#ifndef MIR_SERIES

#define MIR_SERIES

#include  <type_traits>
#include "mir/ndslice.h"

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

    /// Index / Key / Time type aliases
    using Index = typename std::remove_reference<decltype(_index[0])>::type;
    /// ditto
    using Key = Index;
    /// ditto
    using Time = Index;
    /// Data / Value type aliases
    using Data = typename std::remove_reference<decltype(_data._iterator[0])>::type;
    /// ditto
    using Value = Data;

    using Observation = std::pair<Index, Data>;
    // using ConstObservation = std::pair<const Index, const Data>;

    mir_slice<Iterator, N, kind> data() noexcept
    {
        return _data;
    }

    mir_slice<IndexIterator> index() noexcept
    {
        return {{_data._lengths[0]}, _index};
    }

    size_t size() const noexcept
    {
        return _data.size();
    }

    size_t empty() const noexcept
    {
        return _data.empty();
    }

    Observation at(mir_size_t index) const noexcept
    {
        return {_index[index], _data[index]};
    }

    Observation operator[](mir_size_t index) const noexcept
    {
        return {_index[index], _data[index]};
    }

    struct ThisIterator
    {
        mir_size_t _index = 0;
        mir_series _series;
        ThisIterator& operator++() noexcept { ++_index; return *this;}
        ThisIterator operator++(int) noexcept {ThisIterator retval = *this; ++(*this); return retval; }
        bool operator==(const ThisIterator& rhs) const noexcept { return _index == rhs._index; }
        bool operator!=(const ThisIterator& rhs) const noexcept { return !(*this == rhs); }
        bool operator<(const ThisIterator& rhs) const { return _index < rhs._index; }
        bool operator>(const ThisIterator& rhs) const { return _index > rhs._index; }
        bool operator>=(const ThisIterator& rhs) const { return _index >= rhs._index; }
        bool operator<=(const ThisIterator& rhs) const { return _index <= rhs._index; }

        Observation operator*() noexcept
        {
            static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
            return _series[_index];
        }
    };

    ThisIterator begin() noexcept { return {0, *this}; }
    ThisIterator end() noexcept { return {_data.size(), *this}; }
};

// don't sort
template <
    typename IndexIterator,
    typename Iterator,
    mir_size_t N = 1,
    mir_slice_kind kind = mir_slice_kind::contiguous
>
mir_series<IndexIterator, Iterator, N, kind>
    mir_make_series(mir_slice<IndexIterator> index, mir_slice<Iterator, N, kind> data)
{
    assert(data._lengths[0] == index._lengths[0]);
    return { data, index._iterator };
}

#endif
