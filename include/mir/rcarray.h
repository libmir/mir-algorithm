#ifndef MIR_RCARRAY

#define MIR_RCARRAY

#include <utility>
#include <cassert>
#include <initializer_list>
#include <stdexcept>
#include <vector>
#include <iterator>
#include "mir/ndslice.h"
#include "mir/shared_ptr.h"


template <typename T>
struct mir_rci;

template <typename T, bool _unused_ = true>
struct mir_rcarray
{
private:

    T* _payload = nullptr;
    void _cpp_copy_constructor(const mir_rcarray& rhs) noexcept;
    mir_rcarray& _cpp_assign(const mir_rcarray& rhs) noexcept;

    mir_rcarray_context* _context() noexcept { return (mir_rcarray_context*)_payload - 1; }
    const mir_rcarray_context* _context() const noexcept { return (const mir_rcarray_context*)_payload - 1; }

    bool __initialize(mir_size_t length, bool deallocate, bool initialize) noexcept;

public:

    mir_slice<mir_rci<T>> asSlice();

    mir_rcarray() noexcept {}
    mir_rcarray(std::nullptr_t) noexcept {}
    ~mir_rcarray() noexcept { if (_payload) mir_rcarray_decrease_counter(_context()); }
    mir_rcarray(const mir_rcarray& rhs) noexcept : _payload(rhs._payload) { if (_payload) mir_rcarray_increase_counter(_context()); }
    mir_rcarray(mir_rcarray&& rhs) noexcept : _payload(rhs._payload) { rhs._payload = nullptr; }
    mir_rcarray& operator=(const mir_rcarray& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            if (_payload) mir_rcarray_decrease_counter(_context());
            _payload = (T*) rhs._payload;
            if (_payload) mir_rcarray_increase_counter(_context());;
        }
        return *this;
    }

    mir_rcarray(size_t length, bool deallocate = true, bool initialize = true)
    {
        if (!this->__initialize(length, deallocate, initialize))
        {
            throw std::runtime_error("mir_rcarray: out of memory error.");
        }
    }

    template <class RAIter> 
    mir_rcarray(RAIter ibegin, RAIter iend) : mir_rcarray(iend - ibegin)
    {
        if (_payload == nullptr)
            return; // zero length
        auto p = (typename std::remove_const<T>::type*)(_payload);
        do
        {    
            *p = *ibegin;
            ++ibegin;
            ++p;
        }
        while(ibegin != iend);
    }

    void __reset() { _payload = nullptr; }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_rcarray& operator=(const mir_rcarray<Q>& rhs) noexcept
    {
        if (_payload != rhs.get())
        {
            if (_payload) mir_rcarray_decrease_counter(_context());
            _payload = (T*) rhs.get();
            if (_payload) mir_rcarray_increase_counter(_context());;
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_rcarray(const mir_rcarray<Q>& rhs) noexcept : _payload(rhs.get())
    {
        if (_payload) mir_rcarray_increase_counter(_context());
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_rcarray(mir_rcarray<Q>&& rhs) noexcept : _payload(rhs.get())
    {
        rhs.__reset();
    }

    mir_rcarray<const T>& light_const() noexcept { return *(mir_rcarray<const T>*)this; }
    mir_rcarray(std::initializer_list<T> list) : mir_rcarray(list.begin(), list.end()) {}
    template<class E, class Allocator> mir_rcarray(const std::vector<E, Allocator>& vector) : mir_rcarray(vector.begin(), vector.end()) {}
    mir_rcarray& operator=(std::nullptr_t) noexcept { if (_payload) mir_rcarray_decrease_counter(_context()); _payload = nullptr; return *this; }
    size_t size() const noexcept { return _payload ? _context()->length : 0; }
    size_t empty() const noexcept { return size() == 0; }
    T& at(size_t index) noexcept { assert(index < this->size()); return _payload[index]; }
    const T& at(size_t index) const noexcept { assert(index < this->size()); return _payload[index]; }
    T& operator[](size_t index) noexcept { assert(index < this->size()); return _payload[index]; }
    const T& operator[](size_t index) const noexcept { assert(index < this->size()); return _payload[index]; }
    T* data() noexcept { return _payload; }
    const T* data() const noexcept { return _payload; }
    T* begin() noexcept { return _payload; }
    const T* begin() const noexcept { return _payload; }
    const T* cbegin() const noexcept { return _payload; }
    T* end() noexcept { return this->begin() + this->size(); }
    const T* end() const noexcept { return this->begin() + this->size(); }
    const T* cend() const noexcept { return this->cbegin() + this->size(); }
};


template <typename T>
struct mir_rci
{
public:

    using Iterator = T*;
    using Array = mir_rcarray<T>;

    Iterator _iterator = nullptr;
    mir_rcarray<T> _array;

private:
    mir_rci(T* iterator, mir_rcarray<T>& array) : _iterator(iterator), _array(array) {}

public:

    mir_rci() {}
    mir_rci(std::nullptr_t) {}

    mir_rci<const T>& light_const() { return *(mir_rci<const T>*)this; }

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

    T& operator[](size_t index)
    {
        auto ptr = _iterator + index;
        assert(_array.cbegin() <= ptr && ptr < _array.cend());
        return _iterator[index];
    }

    const T& operator[](size_t index) const
    {
        auto ptr = _iterator + index;
        assert(_array.cbegin() <= ptr && ptr < _array.cend());
        return _iterator[index];
    }

    mir_rci operator+(ptrdiff_t index)
    {
        return mir_rci(_iterator + index, _array);
    }

    mir_rci operator-(ptrdiff_t index) const
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

template <
    typename T,
    mir_size_t N,
    mir_slice_kind kind
>
mir_slice<mir_rci<const T>, N, kind> mir_light_const(const mir_slice<mir_rci<T>, N, kind>& s) { return *(mir_slice<mir_rci<const T>, N, kind>*)&s; }

#endif
