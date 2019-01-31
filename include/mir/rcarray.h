#ifndef MIR_RCARRAY

#define MIR_RCARRAY

#include <utility>
#include <cassert>
#include <initializer_list>
#include <stdexcept>
#include <type_traits>
#include <vector>
#include <iterator>
#include "mir/ndslice.h"

template <typename T>
struct mir_rci;

template <typename T, bool cppSupport = true>
struct mir_rcarray
{
private:

    void* _context = NULL;

public:

    ~mir_rcarray();
    mir_rcarray(typename std::conditional<std::is_const<T>::value, const mir_rcarray, mir_rcarray>::type& rhs);
    // mir_rcarray& operator=(typename std::conditional<std::is_const<T>::value, const mir_rcarray, mir_rcarray>::type rhs);
    mir_rcarray& operator=(typename std::conditional<std::is_const<T>::value, const mir_rcarray, mir_rcarray>::type& rhs);
    bool initialize(size_t length, unsigned int alignment, bool deallocate, bool initialize);

    mir_slice<mir_rci<T>> asSlice();

    mir_rcarray() : _context(NULL) {}

    mir_rcarray(size_t length, unsigned int alignment = alignof(T), bool deallocate = true, bool initialize = true)
    {
        if (!this->initialize(length, alignment, deallocate, initialize))
        {
            throw std::runtime_error("mir_rcarray: out of memory error.");
        }
    }

    template <class RAIter> 
    mir_rcarray(RAIter ibegin, RAIter iend) : mir_rcarray(iend - ibegin)
    {
        if (_context == NULL)
            return; // zero length
        auto p = (typename std::remove_const<T>::type*)((char*)_context + sizeof(void*) * 4);
        do
        {    
            *p = *ibegin;
            ++ibegin;
            ++p;
        }
        while(ibegin != iend);
    }

    mir_rcarray(std::initializer_list<T> list) : mir_rcarray(list.begin(), list.end()) {}

    template<class E, class Allocator>
    mir_rcarray(const std::vector<E, Allocator>& vector) : mir_rcarray(vector.begin(), vector.end()) {}

    size_t size() const noexcept
    {
        return _context ? *(size_t*)((char*)_context + sizeof(void*)) : 0;
    }

    size_t empty() const noexcept
    {
        return _context ? *(size_t*)((char*)_context + sizeof(void*)) == 0 : true;
    }

    T& at(size_t index) noexcept
    {
        assert(index < this->size());
        return ((T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    const T& at(size_t index) const noexcept
    {
        assert(index < this->size());
        return ((const T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    T& operator[](size_t index) noexcept
    {
        assert(index < this->size());
        return ((T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    const T& operator[](size_t index) const noexcept
    {
        assert(index < this->size());
        return ((const T*)((char*)_context + sizeof(void*) * 4))[index];
    }

    T* data() noexcept
    {
        return _context ? (T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    const T* data() const noexcept
    {
        return _context ? (const T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    T* begin() noexcept
    {
        return _context ? (T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    const T* begin() const noexcept
    {
        return _context ? (T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    const T* cbegin() const noexcept
    {
        return _context ? (const T*)((char*)_context + sizeof(void*) * 4) : NULL;
    }

    T* end() noexcept
    {
        return this->begin() + this->size();
    }

    const T* end() const noexcept
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
public:

    using Iterator = T*;
    using Array = mir_rcarray<T>;

    Iterator _iterator;
    mir_rcarray<T> _array;

private:
    mir_rci(T* iterator, mir_rcarray<T>& array) : _iterator(iterator), _array(array) {}

public:

    ~mir_rci() = default;
    mir_rci(mir_rci& rhs) = default;

    T* operator->()
    {
        assert(_array.cbegin() <= _iterator && _iterator < _array.cend());
        return _iterator;
    }

    const T* operator->() const
    {
        assert(_array.cbegin() <= _iterator && _iterator < _array.cend());
        return _iterator;
    }

    T& operator*()
    {
        assert(_array.cbegin() <= _iterator && _iterator < _array.cend());
        return *_iterator;
    }

    const T& operator*() const
    {
        assert(_array.cbegin() <= _iterator && _iterator < _array.cend());
        return *_iterator;
    }

    mir_rci& operator++()
    {
        ++_iterator;
        return *this;
    }

    mir_rci& operator--()
    {
        --_iterator;
        return *this;
    }

    mir_rci& operator+=(mir_ptrdiff_t shift)
    {
        _iterator += shift;
        return *this;
    }

    mir_rci& operator-=(mir_ptrdiff_t shift)
    {
        _iterator -= shift;
        return *this;
    }

    mir_rci operator++(int)
    {
        auto ret = *this;
        ++_iterator;
        return ret;
    }

    mir_rci operator--(int)
    {
        auto ret = *this;
        --_iterator;
        return ret;
    }

    T& operator[](mir_size_t index)
    {
        auto ptr = _iterator + index;
        assert(_array.cbegin() <= ptr && ptr < _array.cend());
        return _iterator[index];
    }

    const T& operator[](mir_size_t index) const
    {
        auto ptr = _iterator + index;
        assert(_array.cbegin() <= ptr && ptr < _array.cend());
        return _iterator[index];
    }

    mir_rci operator+(mir_ptrdiff_t index)
    {
        return mir_rci(_iterator + index, _array);
    }

    mir_rci operator-(mir_ptrdiff_t index) const
    {
        return mir_rci(_iterator + index, _array);
    }

    bool operator==(const mir_rci& rhs) const { return _iterator == rhs._iterator; }
    bool operator!=(const mir_rci& rhs) const { return _iterator != rhs._iterator; }
    bool operator<(const mir_rci& rhs) const { return _iterator < rhs._iterator; }
    bool operator>(const mir_rci& rhs) const { return _iterator > rhs._iterator; }
    bool operator>=(const mir_rci& rhs) const { return _iterator >= rhs._iterator; }
    bool operator<=(const mir_rci& rhs) const { return _iterator <= rhs._iterator; }
};

#endif
