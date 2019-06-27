#ifndef MIR_SLIM_RCPTR

#define MIR_SLIM_RCPTR

#include "rcptr.h"

// Does not support allocators for now
template <typename T>
struct mir_slim_rcptr
{
private:

    T* _payload = nullptr;
    using U = typename std::remove_all_extents<T>::type;
    static constexpr void (*destr)(U&) = std::is_destructible<T>::value ? &mir::Destructor<U>::destroy : nullptr;
    static constexpr mir::type_info_g<U> typeInfoT = {destr, sizeof(T)};

public:

    using element_type = T;

    mir_slim_rcptr() noexcept {}
    mir_slim_rcptr(std::nullptr_t) noexcept {}
    mir_slim_rcptr(const mir_rc_context* context) noexcept : _payload(nullptr)
    {
        if (context)
        {
            mir_rc_increase_counter((mir_rc_context*)context);
            _payload = (T*)(context + 1);
        }
    }
    ~mir_slim_rcptr() noexcept { if (_payload) mir_rc_decrease_counter(getContext()); }
    mir_slim_rcptr(const mir_slim_rcptr& rhs) noexcept : _payload(rhs._payload)  { if (_payload) mir_rc_increase_counter(getContext()); }
    mir_slim_rcptr(mir_slim_rcptr&& rhs) noexcept : _payload(rhs._payload) { rhs.__reset(); }
    mir_slim_rcptr& operator=(const mir_slim_rcptr& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            if (_payload) mir_rc_decrease_counter(getContext());
            _payload = (T*) rhs._payload;
            if (_payload) mir_rc_increase_counter(getContext());;
        }
        return *this;
    }

    template<class ...Args> 
    static mir_slim_rcptr make_shared(Args&& ...args)
    {
        using U = typename std::remove_const<T>::type;
        static_assert( std::is_constructible<U, Args...>::value, "Can't construct object in mir_slim_rcptr constructor" );
        mir_slim_rcptr ret;
        auto context = mir_rc_create((const mir_type_info*)&typeInfoT, 1);
        if (context == nullptr)
            throw std::bad_alloc();
        ret._payload = (T*)(context + 1);
        ::new((U*)ret._payload) U(std::forward<Args>(args)...);
        return ret;
    }

    void __reset() { _payload = nullptr; }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_slim_rcptr& operator=(const mir_slim_rcptr<Q>& rhs) noexcept
    {
        auto rhsv = rhs.template get<T>();
        if (_payload != rhsv)
        {
            if (_payload) mir_rc_decrease_counter(getContext());
            _payload = rhsv;
            if (_payload) mir_rc_increase_counter(getContext());
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_slim_rcptr(const mir_slim_rcptr<Q>& rhs) noexcept : _payload(rhs.template get<T>())
    {
        if (_payload) mir_rc_increase_counter(getContext());
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_slim_rcptr(mir_slim_rcptr<Q>&& rhs) noexcept : _payload(rhs.template get<T>())
    {
        rhs.__reset();
    }

    mir_slim_rcptr<const T> light_const() const noexcept { return *(mir_slim_rcptr<const T>*)this; }

    template<class Q>
    Q* get()
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = static_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    template<class Q>
    Q* get() const
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = static_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    mir_rc_context* getContext() noexcept { return _payload ? (mir_rc_context*)_payload - 1 : nullptr; }
    mir_slim_rcptr& operator=(std::nullptr_t) noexcept { if (_payload) mir_rc_decrease_counter(getContext()); __reset(); return *this; }
    T& operator*() noexcept { assert(_payload != nullptr); return *_payload; }
    T* operator->() noexcept { assert(_payload != nullptr); return _payload; }
    T* get() noexcept { return _payload; }
    const T* get() const noexcept { return _payload; }
    const mir_rc_context* getContext() const noexcept  { return _payload ? (const mir_rc_context*)_payload - 1 : nullptr; }
    const T& operator*() const noexcept { assert(_payload != nullptr); return *_payload; }
    const T* operator->() const noexcept { assert(_payload != nullptr); return _payload; }
    template<class Y> bool operator==(const mir_slim_rcptr<Y>& rhs) const noexcept { return _payload == rhs._payload; }
    template<class Y> bool operator!=(const mir_slim_rcptr<Y>& rhs) const noexcept { return _payload != rhs._payload; }
    template<class Y> bool operator<=(const mir_slim_rcptr<Y>& rhs) const noexcept { return _payload <= rhs._payload; }
    template<class Y> bool operator>=(const mir_slim_rcptr<Y>& rhs) const noexcept { return _payload >= rhs._payload; }
    template<class Y> bool operator<(const mir_slim_rcptr<Y>& rhs) const noexcept { return _payload < rhs._payload; }
    template<class Y> bool operator>(const mir_slim_rcptr<Y>& rhs) const noexcept { return _payload > rhs._payload; }
    explicit operator bool() const noexcept { return _payload != nullptr; }
};

namespace mir
{
    template<class T, class ...Args> 
    mir_slim_rcptr<T> make_slim_shared(Args&& ...args)
    {
        return mir_slim_rcptr<T>::make_shared(std::forward<Args>(args)...);
    }

    template< class T, class U > 
    mir_slim_rcptr<T> static_pointer_cast( const mir_slim_rcptr<U>& r ) noexcept
    {
        auto p = static_cast<typename mir_slim_rcptr<T>::element_type*>(r.get());
        return mir_slim_rcptr<T>(r.getContext());
    }

    template< class T, class U > 
    mir_slim_rcptr<T> const_pointer_cast( const mir_slim_rcptr<U>& r ) noexcept
    {
        auto p = const_cast<typename mir_slim_rcptr<T>::element_type*>(r.get());
        return mir_slim_rcptr<T>(r.getContext());
    }
}

namespace std
{
    template <class T>
    struct hash<mir_slim_rcptr<T> >
    {
        typedef mir_slim_rcptr<T> argument_type;
        typedef size_t result_type;

        result_type operator()(const argument_type& ptr) const noexcept
        {
            return (result_type)(ptr.get());
        }
    };
}


#endif
