#ifndef MIR_RCARRAY

#define MIR_RCARRAY

#include <cassert>
#include <initializer_list>
#include <stdexcept>
#include <type_traits>
#include <vector>
#include <iterator>
#include "mir/ndslice.h"

template <typename T>
struct mir_rci;

template <typename T>
struct mir_rcarray
{
private:

    void* _context;

public:

    ~mir_rcarray();
    mir_rcarray(typename std::conditional<std::is_const<T>::value, const mir_rcarray, mir_rcarray>::type& rhs);
    bool initialize(size_t length, unsigned int alignment, bool deallocate, bool initialize);

    mir_slice<mir_rci<T>> asSlice();

    inline mir_rcarray(size_t length, unsigned int alignment = alignof(T), bool deallocate = true, bool initialize = true)
    {
        if (!this->initialize(length, alignment, deallocate, initialize))
        {
            throw std::runtime_error("mir_rcarray: out of memory error.");
        }
    }

    template <class RAIter> 
    inline mir_rcarray(RAIter ibegin, RAIter iend) : mir_rcarray(iend - ibegin)
    {
        if (_context == NULL)
            return; // zero length
        auto p = (T*)((char*)_context + sizeof(void*) * 4);
        do
        {
            *p = *ibegin;
            ++ibegin;
            ++p;
        }
        while(ibegin != iend);
    }

    inline mir_rcarray(std::initializer_list<T> list) : mir_rcarray(list.begin(), list.end()) {}

    template<class E, class Allocator>
    inline mir_rcarray(const std::vector<E, Allocator>& vector) : mir_rcarray(vector.begin(), vector.end()) {}

    inline size_t size() const noexcept
    {
        return _context ? *(size_t*)((char*)_context + sizeof(void*)) : 0;
    }

    inline size_t empty() const noexcept
    {
        return _context ? *(size_t*)((char*)_context + sizeof(void*)) == 0 : true;
    }

    inline T& at(size_t index)
    {
        assert(index < this->size());
        return ((T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    inline const T& at(size_t index) const
    {
        assert(index < this->size());
        return ((const T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    inline T& operator[](size_t index)
    {
        assert(index < this->size());
        return ((T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    inline const T& operator[](size_t index) const
    {
        assert(index < this->size());
        return ((const T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    inline T* data() noexcept
    {
        return _context ? (T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    inline const T* data() const noexcept
    {
        return _context ? (const T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    inline T* begin() noexcept
    {
        return _context ? (T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    inline const T* begin() const noexcept
    {
        return _context ? (T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    inline const T* cbegin() const noexcept
    {
        return _context ? (const T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    inline T* end() noexcept
    {
        return this->begin() + this->size();
    }

    inline const T* end() const noexcept
    {
        return this->begin() + this->size();
    }

    inline const T* cend() const noexcept
    {
        return this->cbegin() + this->size();
    }
};


template <typename T>
struct mir_rci
{
public:

    T* _iterator;
    mir_rcarray<T> _array;

    ~mir_rci() = default;
    mir_rci(mir_rci& rhs) = default;
};

#endif
