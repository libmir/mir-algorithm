#ifndef MIR_RCARRAY

#define MIR_RCARRAY

#include "mir/ndslice.h"
#include "mir/rcptr.h"
#include <cassert>
#include <cstring>
#include <initializer_list>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <string_view>
#include <string>
#include <utility>
#include <vector>

template <typename T>
struct mir_rci;

template <typename T>
struct mir_rcarray
{
private:

    T* _payload = nullptr;
    static constexpr mir_type_info typeInfoT = {nullptr, sizeof(T)};

    void _cpp_copy_constructor(const mir_rcarray& rhs) noexcept;
    mir_rcarray& _cpp_assign(const mir_rcarray& rhs) noexcept;

    mir_rc_context* _context() noexcept { return (mir_rc_context*)_payload - 1; }
    const mir_rc_context* _context() const noexcept { return (const mir_rc_context*)_payload - 1; }

    mir_rcarray(size_t length, const void* _unused_, bool deallocate = true)
    {
        if (length == 0)
            return;
        auto context = mir_rc_create(&typeInfoT, length, nullptr, false, deallocate);
        if (context == nullptr)
            throw std::bad_alloc();
        _payload = (T*)(context + 1);
    }

public:

    mir_slice<mir_rci<T>> asSlice()
    {
        return {{size()}, mir_rci<T>(*this)};
    }

    mir_rcarray() noexcept {}
    mir_rcarray(std::nullptr_t) noexcept {}
    ~mir_rcarray() noexcept { if (_payload) mir_rc_decrease_counter(_context()); }
    mir_rcarray(const mir_rcarray& rhs) noexcept : _payload(rhs._payload) { if (_payload) mir_rc_increase_counter(_context()); }
    mir_rcarray(mir_rcarray&& rhs) noexcept : _payload(rhs._payload) { rhs._payload = nullptr; }
    mir_rcarray& operator=(const mir_rcarray& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            if (_payload) mir_rc_decrease_counter(_context());
            _payload = (T*) rhs._payload;
            if (_payload) mir_rc_increase_counter(_context());;
        }
        return *this;
    }

    mir_rcarray(size_t length, bool initialize = true, bool deallocate = true)
        : mir_rcarray(length, nullptr, deallocate)
    {
        if (initialize)
        {
            for(size_t i = 0; i < length; i++)
            {
                using U = typename std::remove_const<T>::type;
                ::new((U*)_payload + i) U();
            }
        }
    }

    template <class RAIter> 
    mir_rcarray(RAIter ibegin, RAIter iend) : mir_rcarray((size_t)(iend - ibegin), nullptr)
    {
        if (_payload == nullptr)
            return; // zero length
        auto p = (typename std::remove_const<T>::type*)(_payload);
        do
        {    
            using U = typename std::remove_const<T>::type;
            ::new((U*)p) U(*ibegin);
            ++ibegin;
            ++p;
        }
        while(ibegin != iend);
    }

    void __reset() { _payload = nullptr; }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_rcarray& operator=(const mir_rcarray<Q>& rhs) noexcept
    {
        if (_payload != rhs.data())
        {
            if (_payload) mir_rc_decrease_counter(_context());
            _payload = (T*) rhs.data();
            if (_payload) mir_rc_increase_counter(_context());;
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_rcarray(const mir_rcarray<Q>& rhs) noexcept : _payload(rhs.data())
    {
        if (_payload) mir_rc_increase_counter(_context());
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_rcarray(mir_rcarray<Q>&& rhs) noexcept : _payload(rhs.data())
    {
        rhs.__reset();
    }

    mir_rcarray<const T> light_const() const noexcept { return *(mir_rcarray<const T>*)this; }
    mir_rcarray(std::initializer_list<T> list) : mir_rcarray(list.begin(), list.end()) {}
    template<class E, class Allocator> mir_rcarray(const std::vector<E, Allocator>& vector) : mir_rcarray(vector.begin(), vector.end()) {}
    mir_rcarray& operator=(std::nullptr_t) noexcept { if (_payload) mir_rc_decrease_counter(_context()); _payload = nullptr; return *this; }
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
    using Iterator = T*;
    using Array = mir_rcarray<T>;

    Iterator _iterator = nullptr;
    mir_rcarray<T> _array;

    mir_rci(T* iterator, mir_rcarray<T> array) : _iterator(iterator), _array(std::move(array)) {}
    mir_rci(mir_rcarray<T> array) : _iterator(array.data())
    {
        _array = std::move(array);
    }

    mir_rci() {}
    mir_rci(std::nullptr_t) {}

    mir_rci<const T> light_const() const noexcept { return *(mir_rci<const T>*)this; }

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

template<
    class CharT, 
    class Traits
>
mir_rcarray<CharT> mir_rcarray_from_string(std::basic_string_view<CharT, Traits> str)
{
    mir_rcarray<CharT> ret;
    size_t length = str.size();
    if (length != 0)
    {
        ret = mir_rcarray<CharT>(length, true, false);
        std::memcpy(ret.data(), str.data(), length);
    }
    return ret;
}

template<
    class CharT
>
mir_rcarray<CharT> mir_rcarray_from_string(const CharT* str)
{
    return mir_rcarray_from_string(std::basic_string_view<CharT>(str));
}

template<
    class CharT, 
    class Traits,
    class Allocator
>
mir_rcarray<CharT> mir_rcarray_from_string(const std::basic_string<CharT, Traits, Allocator>& str)
{
    return mir_rcarray_from_string((std::basic_string_view<CharT, Traits>)str);
}

template<
    class CharT
>
std::basic_string_view<CharT> mir_get_string_view(mir_rcarray<CharT> str)
{
    return std::basic_string_view<CharT>(str.data(), str.size());
}

template<
    class CharT
>
std::basic_string_view<CharT> mir_get_string_view(mir_rcarray<const CharT> str)
{
    return std::basic_string_view<CharT>(str.data(), str.size());
}

#endif
