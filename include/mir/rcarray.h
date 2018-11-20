#ifndef MIR_RCARRAY

#define MIR_RCARRAY

#include <assert.h> 
#include <stdexcept>
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
    mir_rcarray(mir_rcarray& rhs);
    bool initialize(size_t length, unsigned int alignment, bool deallocate, bool initialize);

    mir_slice<mir_rci<T>> asSlice();

    inline mir_rcarray(size_t length, unsigned int alignment = alignof(T), bool deallocate = true, bool initialize = true)
    {
        if (!this->initialize(length, alignment, deallocate, initialize))
        {
            throw std::runtime_error("mir_rcarray: out of memory arror.");
        }
    }

    size_t size() noexcept
    {
        return _context ? *(size_t*)(_context + sizeof(void*)) : 0;
    }

    T& at(size_t index)
    {
        assert(index < this->size());
        return ((T*)(_context + sizeof(void*) * 4))[index];
    }

    const T& at(size_t index) const
    {
        assert(index < this->size());
        return ((const T*)(_context + sizeof(void*) * 4))[index];
    }

    T& operator[](size_t index)
    {
        assert(index < this->size());
        return ((T*)(_context + sizeof(void*) * 4))[index];
    }

    const T& operator[](size_t index) const
    {
        assert(index < this->size());
        return ((const T*)(_context + sizeof(void*) * 4))[index];
    }

    T* data() noexcept
    {
        return _context ? (T*)(_context + sizeof(void*) * 4) : NULL;
    }

    T* begin() noexcept
    {
        return _context ? (T*)(_context + sizeof(void*) * 4) : NULL;
    }

    const T* cbegin() const noexcept
    {
        return _context ? (const T*)(_context + sizeof(void*) * 4) : NULL;
    }

    T* end() noexcept
    {
        return this->begin() + this->size();
    }

    const T* cend() const noexcept
    {
        return this->cbegin() + this->size();
    }
};


template <typename T>
struct mir_rci
{
    T* _iterator;
    mir_rcarray<T> _array;

public:

    ~mir_rci() = default;
    mir_rci(mir_rci& rhs) = default;
};

#endif
