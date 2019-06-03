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
#include <stdexcept>

template <typename T>
struct mir_rci;

template <typename T>
struct mir_rcarray
{
private:

    T* _payload = nullptr;
    using U = typename std::remove_all_extents<T>::type;
    static constexpr void (*destr)(U&) = std::is_destructible<T>::value ? &mir::Destructor<U>::destroy : nullptr;
    static constexpr mir::type_info_g<U> typeInfoT = {destr, sizeof(T)};

    void _cpp_copy_constructor(const mir_rcarray& rhs) noexcept;
    mir_rcarray& _cpp_assign(const mir_rcarray& rhs) noexcept;

    mir_rc_context* _context() noexcept { return (mir_rc_context*)_payload - 1; }
    const mir_rc_context* _context() const noexcept { return (const mir_rc_context*)_payload - 1; }

    mir_rcarray(size_t length, const void* _unused_, bool deallocate = true)
    {
        if (length == 0)
            return;
        auto context = mir_rc_create((const mir_type_info*)&typeInfoT, length, nullptr, false, deallocate);
        if (context == nullptr)
            throw std::bad_alloc();
        _payload = (T*)(context + 1);
    }

public:

    using iterator = T*;
    using const_iterator = const T*;
    using value_type = T;
    using reverse_iterator = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;

    size_t __counter() const noexcept
    {
        return _payload == nullptr ? 0 : _context()->counter;
    }

    mir_slice<mir_rci<T>> asSlice()
    {
        return {{size()}, mir_rci<T>(*this)};
    }

    mir_slice<mir_rci<T>, 2> asSlice(size_t length0, size_t length1)
    {
        if (length0 * length1 != size())
            throw std::out_of_range("mir_rcarray:asSlice(l1, l2): length product does not match the array length");
        return {{length0, length1}, mir_rci<T>(*this)};
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
    mir_rcarray(RAIter ibegin, RAIter iend) : mir_rcarray(ibegin, iend, (size_t)(iend - ibegin))
    {
    }

    template <class RAIter> 
    mir_rcarray(RAIter ibegin, RAIter iend, size_t length) : mir_rcarray(length, nullptr)
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

    template<class CharT, class Traits, class = typename std::enable_if<std::is_same<const CharT, const T>::value>::type>
    operator std::basic_string_view<CharT, Traits>() const noexcept
    {
        return std::basic_string_view<CharT>(data(), size());
    }

    mir_rcarray<const T> light_const() const noexcept { return *(mir_rcarray<const T>*)this; }
    mir_rcarray(std::initializer_list<T> list) : mir_rcarray(list.begin(), list.end()) {}
    template<class E, class Allocator> mir_rcarray(const std::vector<E, Allocator>& vector) : mir_rcarray(vector.begin(), vector.end()) {}
    mir_rcarray& operator=(std::nullptr_t) noexcept { if (_payload) mir_rc_decrease_counter(_context()); _payload = nullptr; return *this; }
    size_t size() const noexcept { return _payload ? _context()->length : 0; }
    size_t empty() const noexcept { return size() == 0; }
    T& at(size_t index) { if (index >= this->size()) throw std::out_of_range("mir_rcarray: out of range"); return _payload[index]; }
    const T& at(size_t index) const { if (index >= this->size()) throw std::out_of_range("mir_rcarray: out of range"); return _payload[index]; }
    T& operator[](size_t index) { if (index >= this->size()) throw std::out_of_range("mir_rcarray: out of range"); return _payload[index]; }
    const T& operator[](size_t index) const { if (index >= this->size()) throw std::out_of_range("mir_rcarray: out of range"); return _payload[index]; }
    T* data() noexcept { return _payload; }
    const T* data() const noexcept { return _payload; }

    iterator begin() noexcept { return _payload; }
    const_iterator begin() const noexcept { return _payload; }
    const_iterator cbegin() const noexcept { return _payload; }
    iterator end() noexcept { return this->begin() + this->size(); }
    const_iterator end() const noexcept { return this->begin() + this->size(); }
    const_iterator cend() const noexcept { return this->cbegin() + this->size(); }

    reverse_iterator rbegin() noexcept { return reverse_iterator(this->begin()); }
    const_reverse_iterator rbegin() const noexcept { return const_reverse_iterator(this->begin()); }
    const_reverse_iterator crbegin() const noexcept { return const_reverse_iterator(this->begin()); }
    reverse_iterator rend() noexcept { return reverse_iterator(this->end()); }
    const_reverse_iterator rend() const noexcept { return const_reverse_iterator(this->end()); }
    const_reverse_iterator crend() const noexcept { return const_reverse_iterator(this->end()); }
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

    mir_rci operator-(ptrdiff_t index)
    {
        return mir_rci(_iterator - index, _array);
    }

    mir_rci<const T> operator+(ptrdiff_t index) const
    {
        return mir_rci<const T>(_iterator + index, _array);
    }

    mir_rci<const T> operator-(ptrdiff_t index) const
    {
        return mir_rci<const T>(_iterator - index, _array);
    }

    bool operator==(const mir_rci& rhs) const { return _iterator == rhs._iterator; }
    bool operator!=(const mir_rci& rhs) const { return _iterator != rhs._iterator; }
    bool operator<(const mir_rci& rhs) const { return _iterator < rhs._iterator; }
    bool operator>(const mir_rci& rhs) const { return _iterator > rhs._iterator; }
    bool operator>=(const mir_rci& rhs) const { return _iterator >= rhs._iterator; }
    bool operator<=(const mir_rci& rhs) const { return _iterator <= rhs._iterator; }
};

namespace mir
{
    template <
        typename T,
        mir_size_t N,
        mir_slice_kind kind
    >
    mir_slice<mir_rci<const T>, N, kind> light_const(const mir_slice<mir_rci<T>, N, kind>& s) { return *(mir_slice<mir_rci<const T>, N, kind>*)&s; }

    template<
        class CharT, 
        class Traits
    >
    mir_rcarray<CharT> rcarray_from_string(std::basic_string_view<CharT, Traits> str)
    {
        mir_rcarray<CharT> ret;
        size_t length = str.size();
        if (length != 0)
        {
            ret = mir_rcarray<CharT>(length, false);
            std::memcpy(ret.data(), str.data(), length);
        }
        return ret;
    }

    template<
        class CharT
    >
    mir_rcarray<CharT> rcarray_from_string(const CharT* str)
    {
        return rcarray_from_string(std::basic_string_view<CharT>(str));
    }

    template<
        class CharT, 
        class Traits,
        class Allocator
    >
    mir_rcarray<CharT> rcarray_from_string(const std::basic_string<CharT, Traits, Allocator>& str)
    {
        return rcarray_from_string((std::basic_string_view<CharT, Traits>)str);
    }

    template<
        class CharT
    >
    std::basic_string_view<CharT> get_string_view(const mir_rcarray<CharT>& str)
    {
        return std::basic_string_view<CharT>(str.data(), str.size());
    }

    template<
        class CharT
    >
    std::basic_string_view<CharT> get_string_view(const mir_rcarray<const CharT>& str)
    {
        return std::basic_string_view<CharT>(str.data(), str.size());
    }
}

#endif
