#ifndef MIR_SERIES

#define MIR_SERIES

#include <iterator>
#include <map>
#include <stdexcept>
#include "mir/ndslice.h"
#include "mir/rcarray.h"

template <
    typename Index,
    typename Data
>
struct mir_observation
{
    Index index;
    Data data;
};

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
    /// Data / Value type aliases
    using Data = typename std::remove_reference<decltype(_data._iterator[0])>::type;
    
    using UnqualIndex = typename std::remove_const<Index>::type;
    using UnqualData = typename std::remove_const<Data>::type;

    using Observation = std::pair<Index, Data>;
    // using ConstObservation = std::pair<const Index, const Data>;

    mir_slice<Iterator, N, kind> data() noexcept
    {
        return _data;
    }

    auto data() const noexcept
    {
        return mir::light_const(_data);
    }

    mir_slice<IndexIterator> index() noexcept
    {
        return {{_data._lengths[0]}, _index};
    }

    auto index() const noexcept
    {
        return mir_slice<decltype(mir::light_const(_index))> {{_data._lengths[0]}, mir::light_const(_index)};
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

    Observation backward(mir_size_t index) const noexcept
    {
        return {_index[size() - 1 - index], _data[size() - 1 - index]};
    }

    Observation operator[](mir_size_t index) const noexcept
    {
        return {_index[index], _data[index]};
    }

    mir_series slice(mir_size_t a, mir_size_t b)
    {
        if (a > b)
            throw std::out_of_range("series::slice: a > b");
        if (b > size())
            throw std::out_of_range("series::slice: b > size()");
        auto newIndex = _index;
        newIndex += a;
        return { {{b - a}, _data._iterator}, std::move(newIndex) };
    }

    size_t transition_index_less(const Index& val) const
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

    size_t transition_index_less_or_equal(const Index& val) const
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

    bool contains(const Index& key) const
    {
        size_t idx = transition_index_less(key);
        return idx < _data._lengths[0] && _index[idx] == key;
    }

    bool try_get(const Index& key, UnqualData& val) const
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0] && _index[idx] == key;
        if (cond)
            val = _data[idx];
        return cond;
    }

    const Data* try_get_ptr(const Index& key) const
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0] && _index[idx] == key;
        if (cond)
            return &_data[idx];
        return nullptr;
    }

    auto&& get(const Index& key)
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0] && _index[idx] == key;
        if (cond)
            return _data[idx];
        throw std::out_of_range("series::get:  key not found");
    }

    auto&& get(const Index& key) const
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0] && _index[idx] == key;
        if (cond)
            return _data[idx];
        throw std::out_of_range("series::get:  key not found");
    }

    bool try_get_next(const Index& key, UnqualData& val) const
    {
        size_t idx = transition_index_less(key);
        auto cond = idx < _data._lengths[0];
        if (cond)
            val = _data[idx];
        return cond;
    }

    bool try_get_next_update_key(UnqualIndex& key, UnqualData& val) const
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

    bool try_get_prev(const Index& key, UnqualData& val) const
    {
        size_t idx = transition_index_less_or_equal(key) - 1;
        auto cond = 0 <= (ptrdiff_t) idx;
        if (cond)
            val = _data[idx];
        return cond;
    }

    bool try_get_prev_update_key(UnqualIndex& key, UnqualData& val) const
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

    bool try_get_first(const Index& lowerBound, const Index& upperBound, UnqualData& val) const
    {
        size_t idx = transition_index_less(lowerBound);
        auto cond = idx < _data._lengths[0] && _index[idx] <= upperBound;
        if (cond)
            val = _data[idx];
        return cond;
    }

    bool try_get_first_update_lower(UnqualIndex& lowerBound, const Index& upperBound, UnqualData& val) const
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

    bool try_get_last(const Index& lowerBound, const Index& upperBound, UnqualData& val) const
    {
        size_t idx = transition_index_less_or_equal(upperBound) - 1;
        auto cond = 0 <= (ptrdiff_t) idx && lowerBound <= _index[idx];
        if (cond)
            val = _data[idx];
        return cond;
    }

    bool try_get_last_update_upper(const Index& lowerBound, UnqualIndex& upperBound, UnqualData& val) const
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
        using value_type = Data;
        using difference_type = mir_ptrdiff_t;
        using reference = Observation;
        using pointer = void;
        using iterator_category = std::input_iterator_tag;

        mir_size_t _index = 0;
        mir_series _series;
        ThisIterator& operator++() noexcept { ++_index; return *this;}
        ThisIterator operator++(int) noexcept {ThisIterator retval = *this; ++(*this); return retval; }
        bool operator==(const ThisIterator& rhs) const noexcept { return _index == rhs._index; }
        bool operator!=(const ThisIterator& rhs) const noexcept { return !(*this == rhs); }
        bool operator<(const ThisIterator& rhs) const noexcept { return _index < rhs._index; }
        bool operator>(const ThisIterator& rhs) const noexcept { return _index > rhs._index; }
        bool operator>=(const ThisIterator& rhs) const noexcept { return _index >= rhs._index; }
        bool operator<=(const ThisIterator& rhs) const noexcept { return _index <= rhs._index; }

        reference operator*() noexcept
        {
            static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
            return _series[_index];
        }
    };

    ThisIterator begin() noexcept { return {0, *this}; }
    ThisIterator end() noexcept { return {_data.size(), *this}; }

    ThisIterator begin() const noexcept { return {0, *this}; }
    ThisIterator end() const noexcept { return {_data.size(), *this}; }

    ThisIterator cbegin() const noexcept { return {0, *this}; }
    ThisIterator cend() const noexcept { return {_data.size(), *this}; }
};

namespace mir
{
    // don't sort
    template <
        typename IndexIterator,
        typename Iterator,
        mir_size_t N = 1,
        mir_slice_kind kind = mir_slice_kind::contiguous
    >
    mir_series<IndexIterator, Iterator, N, kind>
        make_series(mir_slice<IndexIterator> index, mir_slice<Iterator, N, kind> data)
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
        make_series(const std::map<Key, Value, std::less<Key>, Allocator>& map)
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
        return make_series(index, data);
    }

    template <
        typename I,
        typename T,
        mir_size_t N,
        mir_slice_kind kind
    >
    mir_series<const I*, const T*, N, kind> light_const(const mir_series<I*, T*, N, kind> s) { return *(mir_series<const I*, const T*, N, kind>*)&s; }

    template <
        typename I,
        typename T,
        mir_size_t N,
        mir_slice_kind kind
    >
    mir_series<mir_rci<const I>, mir_rci<const T>, N, kind> light_const(const mir_series<mir_rci<I>, mir_rci<T>, N, kind> s) { return *(mir_series<mir_rci<const I>, mir_rci<const T>, N, kind>*)&s; }
}

#endif
