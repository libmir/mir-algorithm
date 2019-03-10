#ifndef MIR_SERIES

#define MIR_SERIES

#include <map>
#include "mir/ndslice.h"
#include "mir/rcarray.h"

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

    bool empty() const noexcept
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

    template <class T>
    size_t transition_index_less(const T& val) const
    {
        size_t first = 0, count = size();
        while (count > 0)
        {
            size_t step = count / 2, it = first + step;
            if (_index[it] < val)
            {
                first = it + 1;
                count -= step + 1;
            }
            else
            {
                count = step;
            }
        }
        return first;
    }

    template <class T>
    size_t transition_index_less_or_equal(const T& val) const
    {
        size_t first = 0, count = size();
        while (count > 0)
        {
            size_t step = count / 2, it = first + step;
            if (_index[it] <= val)
            {
                first = it + 1;
                count -= step + 1;
            }
            else
            {
                count = step;
            }
        }
        return first;
    }

    template <class T>
    bool contains(const T& key) const
    {
        size_t idx = transition_index_less(key);
        return idx < _data._lengths[0] && _index[idx] == key;
    }

    template <class T, class Value>
    bool try_get(const T& key, Value& val) const
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0] && _index[idx] == key;
        if (cond)
            val = _data[idx];
        return cond;
    }

    template <class T, class Value>
    bool try_get_next(const T& key, Value& val) const
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0];
        if (cond)
            val = _data[idx];
        return cond;
    }

    template <class T, class Value>
    bool try_get_next_update_key(T& key, Value& val) const
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0];
        if (cond)
        {
            key = _index[idx];
            val = _data[idx];
        }
        return cond;
    }

    template <class T, class Value>
    bool try_get_prev(const T& key, Value& val) const
    {
        size_t idx = transition_index_less_or_equal(key) - 1;
        auto cond = 0 <= (ptrdiff_t) idx;
        if (cond)
            val = _data[idx];
        return cond;
    }

    template <class T, class Value>
    bool try_get_prev_update_key(T& key, Value& val) const
    {
        size_t idx = transition_index_less_or_equal(key) - 1;
        auto cond = 0 <= (ptrdiff_t) idx;
        if (cond)
        {
            key = _index[idx];
            val = _data[idx];
        }
        return cond;
    }

    template <class T, class Value>
    bool try_get_first(const T& lowerBound, const T& upperBound, Value& val) const
    {
        size_t idx = transition_index_less(lowerBound);
        auto cond = idx < _data._lengths[0] && _index[idx] <= upperBound;
        if (cond)
            val = _data[idx];
        return cond;
    }

    template <class T, class Value>
    bool try_get_first_update_lower(T& lowerBound, const T& upperBound, Value& val) const
    {
        size_t idx = transition_index_less(lowerBound);
        auto cond = idx < _data._lengths[0] && _index[idx] <= upperBound;
        if (cond)
        {
            lowerBound = _index[idx];
            val = _data[idx];
        }
        return cond;
    }

    template <class T, class Value>
    bool try_get_last(const T& lowerBound, const T& upperBound, Value& val) const
    {
        size_t idx = transition_index_less_or_equal(upperBound) - 1;
        auto cond = 0 <= (ptrdiff_t) idx && lowerBound <= _index[idx];
        if (cond)
            val = _data[idx];
        return cond;
    }

    template <class T, class Value>
    bool try_get_last_update_upper(const T& lowerBound, T& upperBound, Value& val) const
    {
        size_t idx = transition_index_less_or_equal(upperBound) - 1;
        auto cond = 0 <= (ptrdiff_t) idx && lowerBound <= _index[idx];
        if (cond)
        {
            upperBound = _index[idx];
            val = _data[idx];
        }
        return cond;
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

template<
    class Key,
    class Value,
    class Allocator
>
mir_series<mir_rci<Key>,mir_rci<Value>>
    mir_make_series(const std::map<Key, Value, std::less<Key>, Allocator>& map)
{
    auto index = mir_rcarray<Key>(map.size()).asSlice();
    auto data = mir_rcarray<Value>(map.size()).asSlice();
    size_t i = 0;
    for (const auto&[key, value] : map)
    {
        index[i] = key;
        data[i] = value;
        i++;
    }
    return mir_make_series(index, data);
}

#endif
