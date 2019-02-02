/**
 ************ Mir-Algorithm ************

The module provides wrappers for $(SUBREF slice, Slice) that
can be used as arguments for C++ functions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
*/

#ifndef MIR_NDSLICE

#define MIR_NDSLICE

#include <cstddef>
#include <cstdint>

#if INTPTR_MAX == INT32_MAX
    #define mir_size_t unsigned int
    #define mir_ptrdiff_t int
#elif INTPTR_MAX == INT64_MAX
    #ifdef _WIN32
        #define mir_size_t unsigned long long
        #define mir_ptrdiff_t long long
    #else
        #define mir_size_t unsigned long
        #define mir_ptrdiff_t long
    #endif
#else
    #error "Environment not 32 or 64-bit."
#endif

// It is out of ndslice namespace because of a DMD mangling bug.
enum class mir_slice_kind : int
{
    universal = 0,
    canonical = 1,
    contiguous = 2
};

template <
    typename Iterator,
    mir_size_t N = 1,
    mir_slice_kind kind = mir_slice_kind::contiguous
>
struct mir_slice
{
    mir_size_t _lengths[0] = {};
    mir_ptrdiff_t  _strides[kind == mir_slice_kind::universal ? N : N - 1] = {};
    Iterator _iterator = {};

    template <unsigned int d = 0>
    size_t size() const noexcept
    {
        return _lengths[d];
    }

    template <unsigned int d = 0>
    bool empty() const noexcept
    {
        return _lengths[d] == 0;
    }
};

template <
    typename Iterator,
    mir_size_t N
>
struct mir_slice<Iterator, N, mir_slice_kind::contiguous>
{
    mir_size_t _lengths[N] = {};
    static const mir_ptrdiff_t _strides[0];
    Iterator _iterator = {};

    template <unsigned int d = 0>
    size_t size() const noexcept
    {
        return _lengths[d];
    }

    template <unsigned int d = 0>
    bool empty() const noexcept
    {
        return _lengths[d] == 0;
    }
};

template <
    typename Iterator
>
struct mir_slice<Iterator, 1, mir_slice_kind::contiguous>
{
    mir_size_t _lengths[1] = {};
    static const mir_ptrdiff_t _strides[0];
    Iterator _iterator = {};

    template <unsigned int d = 0>
    size_t size() const noexcept
    {
        return _lengths[d];
    }

    template <unsigned int d = 0>
    bool empty() const noexcept
    {
        return _lengths[d] == 0;
    }

    auto&& at(mir_size_t index) noexcept
    {

        assert(index < this->size());
        return _iterator[index];
    }

    auto&& at(mir_size_t index) const noexcept
    {
        assert(index < this->size());
        return _iterator[index];
    }

    auto&& operator[](mir_size_t index) noexcept
    {
        return at(index);
    }

    auto&& operator[](mir_size_t index) const noexcept
    {
        return at(index);
    }

    Iterator begin() noexcept
    {
        return _iterator;
    }

    auto cbegin() const noexcept
    {
        return _iterator;
    }

    Iterator end() noexcept
    {
        return _iterator + _lengths[0];
    }

    auto cend() const noexcept
    {
        return _iterator + _lengths[0];
    }
};

template <
    typename Iterator
>
struct mir_slice<Iterator, 1, mir_slice_kind::universal>
{
    mir_size_t _lengths[1] = {};
    mir_ptrdiff_t _strides[1] = {};
    Iterator _iterator = {};

    template <unsigned int d = 0>
    size_t size() const noexcept
    {
        return _lengths[d];
    }

    template <unsigned int d = 0>
    bool empty() const noexcept
    {
        return _lengths[d] == 0;
    }

    auto&& at(mir_size_t index) noexcept
    {

        assert(index < this->size());
        return _iterator[index * _strides[0]];
    }

    auto&& at(mir_size_t index) const noexcept
    {
        assert(index < this->size());
        return _iterator[index * _strides[0]];
    }

    auto&& operator[](mir_size_t index) noexcept
    {
        return at(index);
    }

    auto&& operator[](mir_size_t index) const noexcept
    {
        return at(index);
    }
};

#endif
