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
    mir_size_t _lengths[N] = {};
    mir_ptrdiff_t _strides[kind == mir_slice_kind::universal ? N : kind == mir_slice_kind::canonical ? N - 1 : 0] = {};
    Iterator _iterator;

    size_t size() const noexcept
    {
        return _lengths[0];
    }

    size_t empty() const noexcept
    {
        return _lengths[0] == 0;
    }

    auto&& at(mir_size_t index) noexcept
    {
        static_assert(N == 1, "The method is defined only for 1-dimensional slice.");
        assert(index < this->size());
        auto strides = (const mir_ptrdiff_t*)_strides;
        return _iterator[sizeof(_strides) == 0 ? index : index * strides[0]];
    }

    auto&& at(mir_size_t index) const noexcept
    {
        static_assert(N == 1, "The method is defined only for 1-dimensional slice.");
        assert(index < this->size());
        auto strides = (const mir_ptrdiff_t*)_strides;
        return _iterator[sizeof(_strides) == 0 ? index : index * strides[0]];
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
        static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
        return _iterator;
    }

    auto begin() const noexcept
    {
        static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
        return _iterator;
    }

    auto cbegin() const noexcept
    {
        static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
        return _iterator;
    }

    Iterator end() noexcept
    {
        static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
        return _iterator + _lengths[0];
    }

    auto end() const noexcept
    {
        static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
        return _iterator + _lengths[0];
    }

    auto cend() const noexcept
    {
        static_assert(kind == mir_slice_kind::contiguous && N == 1, "The method is defined only for 1-dimensional slice.");
        return _iterator + _lengths[0];
    }
};

#endif
