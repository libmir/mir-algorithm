#ifndef MIR_RCPTR

#define MIR_RCPTR

#include <utility>
#include <cassert>
#include <stdexcept>
#include <memory>
#include <cstdlib>
#include <type_traits>

struct mir_type_info
{
    void (*destructor)(void*);
    int size;
};

struct mir_rc_context
{
    void* allocator;
    const mir_type_info* typeInfo;
    size_t counter;
    size_t length;
};

extern "C"
{
    void mir_rc_increase_counter(mir_rc_context* payload);
    
    void mir_rc_decrease_counter(mir_rc_context* payload);
    
    mir_rc_context* mir_rc_create(
        const mir_type_info* typeInfo,
        size_t length,
        const void* payload = nullptr,
        bool initialize = true,
        bool deallocate = true
    );
}
namespace mir
{
    template<class T>
    struct type_info_g
    {
        void (*destructor)(T&);
        int size;
    };

    template<class T, bool dest = std::is_destructible<T>::value>
    struct Destructor
    {
    };

    template<class T>
    struct Destructor<T, false>
    {
        static void destroy(T& val)
        {
        }
    };

    template<class T>
    struct Destructor<T, true>
    {
        static void destroy(T& val)
        {
            val.~T();
        }
    };

        // template<class = typename std::enable_if<!std::is_destructible<T>::value>::type>

        // template<class = typename std::enable_if<std::is_destructible<T>::value>::type>

    template<class U>
    static const mir_type_info* typeInfoT_()
    {
        static constexpr void (*destr)(U&) = std::is_destructible<U>::value ? &Destructor<U>::destroy : nullptr;
        static constexpr type_info_g<U> value = {destr, sizeof(U)};
        return (const mir_type_info*)&value;
    }
}

// Does not support allocators for now
template <typename T>
struct mir_rcptr
{
private:

    T* _payload = nullptr;
    mir_rc_context* _context = nullptr;
    using U = typename std::remove_const<T>::type;

public:

    using element_type = T;

    mir_rcptr() noexcept {}
    mir_rcptr(std::nullptr_t) noexcept {}
    mir_rcptr(const mir_rc_context* context, T* payload) noexcept : _payload(payload), _context((mir_rc_context*)context) { if (_context) mir_rc_increase_counter(_context); }
    ~mir_rcptr() noexcept { if (_context) mir_rc_decrease_counter(_context); }
    mir_rcptr(const mir_rcptr& rhs) noexcept : _payload(rhs._payload), _context((mir_rc_context*)rhs.getContext())  { if (_context) mir_rc_increase_counter(_context); }
    mir_rcptr(mir_rcptr&& rhs) noexcept : _payload(rhs._payload), _context(rhs.getContext()) { rhs.__reset(); }
    mir_rcptr& operator=(const mir_rcptr& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            if (_context) mir_rc_decrease_counter(_context);
            _payload = (T*) rhs._payload;
            _context = (mir_rc_context*) rhs.getContext();
            if (_context) mir_rc_increase_counter(_context);;
        }
        return *this;
    }

    template<class ...Args> 
    static mir_rcptr make_shared(Args&& ...args)
    {
        using U = typename std::remove_const<T>::type;
        static_assert( std::is_constructible<U, Args...>::value, "Can't construct object in mir_rcptr constructor" );
        mir_rcptr ret;
        ret._context = mir_rc_create(mir::typeInfoT_<U>(), 1);
        if (ret._context == nullptr)
            throw std::bad_alloc();
        ret._payload = (T*)(ret._context + 1);
        ::new((U*)ret._payload) U(std::forward<Args>(args)...);
        return ret;
    }

    void __reset() { _payload = nullptr; _context = nullptr; }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr& operator=(const mir_rcptr<Q>& rhs) noexcept
    {
        auto rhsv = rhs.template get<T>();
        if (_payload != rhsv)
        {
            if (_context) mir_rc_decrease_counter(_context);
            _payload = rhsv;
            _context = (mir_rc_context*) rhs.getContext();
            if (_context) mir_rc_increase_counter(_context);
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr(const mir_rcptr<Q>& rhs) noexcept : _payload(rhs.template get<T>()), _context((mir_rc_context*)rhs.getContext())
    {
        if (_context) mir_rc_increase_counter(_context);
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr(mir_rcptr<Q>&& rhs) noexcept : _payload(rhs.template get<T>()), _context(rhs.getContext())
    {
        rhs.__reset();
    }

    mir_rcptr<const T> light_const() const noexcept { return *(mir_rcptr<const T>*)this; }

    template<class Q>
    Q* get()
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = dynamic_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    template<class Q>
    Q* get() const
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = dynamic_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    mir_rc_context* getContext() noexcept { return _context; }
    mir_rcptr& operator=(std::nullptr_t) noexcept { if (_context) mir_rc_decrease_counter(_context); __reset(); return *this; }
    T& operator*() noexcept { assert(_payload != nullptr); return *_payload; }
    T* operator->() noexcept { assert(_payload != nullptr); return _payload; }
    T* get() noexcept { return _payload; }
    const T* get() const noexcept { return _payload; }
    const mir_rc_context* getContext() const noexcept { return _context; }
    const T& operator*() const noexcept { assert(_payload != nullptr); return *_payload; }
    const T* operator->() const noexcept { assert(_payload != nullptr); return _payload; }
    template<class Y> bool operator==(const mir_rcptr<Y>& rhs) const noexcept { return _payload == rhs._payload; }
    template<class Y> bool operator!=(const mir_rcptr<Y>& rhs) const noexcept { return _payload != rhs._payload; }
    template<class Y> bool operator<=(const mir_rcptr<Y>& rhs) const noexcept { return _payload <= rhs._payload; }
    template<class Y> bool operator>=(const mir_rcptr<Y>& rhs) const noexcept { return _payload >= rhs._payload; }
    template<class Y> bool operator<(const mir_rcptr<Y>& rhs) const noexcept { return _payload < rhs._payload; }
    template<class Y> bool operator>(const mir_rcptr<Y>& rhs) const noexcept { return _payload > rhs._payload; }
    explicit operator bool() const noexcept { return _payload != nullptr; }
};

// Does not support allocators for now
template <typename T>
struct mir_rcptr<T* const>
{
private:

    T* _payload = nullptr;
    mir_rc_context* _context = nullptr;
    using U = typename std::remove_const<T>::type;
    static constexpr void (*destr)(U&) = std::is_destructible<T>::value ? &mir::Destructor<U>::destroy : nullptr;
    static constexpr mir::type_info_g<U> typeInfoT = {destr, sizeof(T)};

public:

    using element_type = T;

    mir_rcptr() noexcept {}
    mir_rcptr(std::nullptr_t) noexcept {}
    mir_rcptr(const mir_rc_context* context, T* payload) noexcept : _payload(payload), _context((mir_rc_context*)context) { if (_context) mir_rc_increase_counter(_context); }
    ~mir_rcptr() noexcept { if (_context) mir_rc_decrease_counter(_context); }
    mir_rcptr(const mir_rcptr& rhs) noexcept : _payload(rhs._payload), _context((mir_rc_context*)rhs.getContext())  { if (_context) mir_rc_increase_counter(_context); }
    mir_rcptr(mir_rcptr&& rhs) noexcept : _payload(rhs._payload), _context(rhs.getContext()) { rhs.__reset(); }
    mir_rcptr& operator=(const mir_rcptr& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            if (_context) mir_rc_decrease_counter(_context);
            _payload = (T*) rhs._payload;
            _context = (mir_rc_context*) rhs.getContext();
            if (_context) mir_rc_increase_counter(_context);;
        }
        return *this;
    }

    template<class ...Args> 
    static mir_rcptr make_shared(Args&& ...args)
    {
        using U = typename std::remove_const<T>::type;
        static_assert( std::is_constructible<U, Args...>::value, "Can't construct object in mir_rcptr constructor" );
        mir_rcptr ret;
        ret._context = mir_rc_create((const mir_type_info*)&typeInfoT, 1);
        if (ret._context == nullptr)
            throw std::bad_alloc();
        ret._payload = (T*)(ret._context + 1);
        ::new((U*)ret._payload) U(std::forward<Args>(args)...);
        return ret;
    }

    void __reset() { _payload = nullptr; _context = nullptr; }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr& operator=(const mir_rcptr<Q>& rhs) noexcept
    {
        auto rhsv = rhs.template get<T>();
        if (_payload != rhsv)
        {
            if (_context) mir_rc_decrease_counter(_context);
            _payload = rhsv;
            _context = (mir_rc_context*) rhs.getContext();
            if (_context) mir_rc_increase_counter(_context);
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr(const mir_rcptr<Q>& rhs) noexcept : _payload(rhs.template get<T>()), _context((mir_rc_context*)rhs.getContext())
    {
        if (_context) mir_rc_increase_counter(_context);
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr(mir_rcptr<Q>&& rhs) noexcept : _payload(rhs.template get<T>()), _context(rhs.getContext())
    {
        rhs.__reset();
    }

    mir_rcptr<const T> light_const() const noexcept { return *(mir_rcptr<const T>*)this; }

    template<class Q>
    Q* get()
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = dynamic_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    template<class Q>
    Q* get() const
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = dynamic_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    mir_rc_context* getContext() noexcept { return _context; }
    mir_rcptr& operator=(std::nullptr_t) noexcept { if (_context) mir_rc_decrease_counter(_context); __reset(); return *this; }
    T& operator*() noexcept { assert(_payload != nullptr); return *_payload; }
    T* operator->() noexcept { assert(_payload != nullptr); return _payload; }
    T* get() noexcept { return _payload; }
    const T* get() const noexcept { return _payload; }
    const mir_rc_context* getContext() const noexcept { return _context; }
    const T& operator*() const noexcept { assert(_payload != nullptr); return *_payload; }
    const T* operator->() const noexcept { assert(_payload != nullptr); return _payload; }
    template<class Y> bool operator==(const mir_rcptr<Y>& rhs) const noexcept { return _payload == rhs._payload; }
    template<class Y> bool operator!=(const mir_rcptr<Y>& rhs) const noexcept { return _payload != rhs._payload; }
    template<class Y> bool operator<=(const mir_rcptr<Y>& rhs) const noexcept { return _payload <= rhs._payload; }
    template<class Y> bool operator>=(const mir_rcptr<Y>& rhs) const noexcept { return _payload >= rhs._payload; }
    template<class Y> bool operator<(const mir_rcptr<Y>& rhs) const noexcept { return _payload < rhs._payload; }
    template<class Y> bool operator>(const mir_rcptr<Y>& rhs) const noexcept { return _payload > rhs._payload; }
    explicit operator bool() const noexcept { return _payload != nullptr; }
};

template <typename T>
struct mir_rcptr<T*>
{
private:

    T* _payload = nullptr;
    mir_rc_context* _context = nullptr;
    using U = typename std::remove_const<T>::type;
    static constexpr void (*destr)(U&) = std::is_destructible<T>::value ? &mir::Destructor<U>::destroy : nullptr;
    static constexpr mir::type_info_g<U> typeInfoT = {destr, sizeof(T)};

public:

    using element_type = T;

    mir_rcptr() noexcept {}
    mir_rcptr(std::nullptr_t) noexcept {}
    mir_rcptr(const mir_rc_context* context, T* payload) noexcept : _payload(payload), _context((mir_rc_context*)context) { if (_context) mir_rc_increase_counter(_context); }
    ~mir_rcptr() noexcept { if (_context) mir_rc_decrease_counter(_context); }
    mir_rcptr(const mir_rcptr& rhs) noexcept : _payload(rhs._payload), _context((mir_rc_context*)rhs.getContext())  { if (_context) mir_rc_increase_counter(_context); }
    mir_rcptr(mir_rcptr&& rhs) noexcept : _payload(rhs._payload), _context(rhs.getContext()) { rhs.__reset(); }
    mir_rcptr& operator=(const mir_rcptr& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            if (_context) mir_rc_decrease_counter(_context);
            _payload = (T*) rhs._payload;
            _context = (mir_rc_context*) rhs.getContext();
            if (_context) mir_rc_increase_counter(_context);;
        }
        return *this;
    }

    template<class ...Args> 
    static mir_rcptr make_shared(Args&& ...args)
    {
        using U = typename std::remove_const<T>::type;
        static_assert( std::is_constructible<U, Args...>::value, "Can't construct object in mir_rcptr constructor" );
        mir_rcptr ret;
        ret._context = mir_rc_create((const mir_type_info*)&typeInfoT, 1);
        if (ret._context == nullptr)
            throw std::bad_alloc();
        ret._payload = (T*)(ret._context + 1);
        ::new((U*)ret._payload) U(std::forward<Args>(args)...);
        return ret;
    }

    void __reset() { _payload = nullptr; _context = nullptr; }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr& operator=(const mir_rcptr<Q>& rhs) noexcept
    {
        auto rhsv = rhs.template get<T>();
        if (_payload != rhsv)
        {
            if (_context) mir_rc_decrease_counter(_context);
            _payload = rhsv;
            _context = (mir_rc_context*) rhs.getContext();
            if (_context) mir_rc_increase_counter(_context);
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr(const mir_rcptr<Q>& rhs) noexcept : _payload(rhs.template get<T>()), _context((mir_rc_context*)rhs.getContext())
    {
        if (_context) mir_rc_increase_counter(_context);
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr(mir_rcptr<Q>&& rhs) noexcept : _payload(rhs.template get<T>()), _context(rhs.getContext())
    {
        rhs.__reset();
    }

    mir_rcptr<const T> light_const() const noexcept { return *(mir_rcptr<const T>*)this; }

    template<class Q>
    Q* get()
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = dynamic_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    template<class Q>
    Q* get() const
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = dynamic_cast<Q*>(_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    mir_rc_context* getContext() noexcept { return _context; }
    mir_rcptr& operator=(std::nullptr_t) noexcept { if (_context) mir_rc_decrease_counter(_context); __reset(); return *this; }
    T& operator*() noexcept { assert(_payload != nullptr); return *_payload; }
    T* operator->() noexcept { assert(_payload != nullptr); return _payload; }
    T* get() noexcept { return _payload; }
    const T* get() const noexcept { return _payload; }
    const mir_rc_context* getContext() const noexcept { return _context; }
    const T& operator*() const noexcept { assert(_payload != nullptr); return *_payload; }
    const T* operator->() const noexcept { assert(_payload != nullptr); return _payload; }
    template<class Y> bool operator==(const mir_rcptr<Y>& rhs) const noexcept { return _payload == rhs._payload; }
    template<class Y> bool operator!=(const mir_rcptr<Y>& rhs) const noexcept { return _payload != rhs._payload; }
    template<class Y> bool operator<=(const mir_rcptr<Y>& rhs) const noexcept { return _payload <= rhs._payload; }
    template<class Y> bool operator>=(const mir_rcptr<Y>& rhs) const noexcept { return _payload >= rhs._payload; }
    template<class Y> bool operator<(const mir_rcptr<Y>& rhs) const noexcept { return _payload < rhs._payload; }
    template<class Y> bool operator>(const mir_rcptr<Y>& rhs) const noexcept { return _payload > rhs._payload; }
    explicit operator bool() const noexcept { return _payload != nullptr; }
};

namespace mir
{
    template<class T, class ...Args> 
    mir_rcptr<T> make_shared(Args&& ...args)
    {
        return mir_rcptr<T>::make_shared(std::forward<Args>(args)...);
    }

    template< class T, class U > 
    mir_rcptr<T> static_pointer_cast( const mir_rcptr<U>& r ) noexcept
    {
        auto p = static_cast<typename mir_rcptr<T>::element_type*>(r.get());
        return mir_rcptr<T>(r.getContext(), p);
    }

    template< class T, class U > 
    mir_rcptr<T> dynamic_pointer_cast( const mir_rcptr<U>& r ) noexcept
    {
        if (auto p = dynamic_cast<typename mir_rcptr<T>::element_type*>(r.get())) {
            return mir_rcptr<T>(r.getContext(), p);
        } else {
            return mir_rcptr<T>();
        }
    }

    template< class T, class U > 
    mir_rcptr<T> const_pointer_cast( const mir_rcptr<U>& r ) noexcept
    {
        auto p = const_cast<typename mir_rcptr<T>::element_type*>(r.get());
        return mir_rcptr<T>(r.getContext(), p);
    }

    template< class T, class U > 
    mir_rcptr<T> reinterpret_pointer_cast( const mir_rcptr<U>& r ) noexcept
    {
        auto p = reinterpret_cast<typename mir_rcptr<T>::element_type*>(r.get());
        return mir_rcptr<T>(r.getContext(), p);
    }
}

namespace std
{
    template <class T>
    struct hash<mir_rcptr<T> >
    {
        typedef mir_rcptr<T> argument_type;
        typedef size_t result_type;

        result_type operator()(const argument_type& ptr) const noexcept
        {
            return (result_type)(ptr.get());
        }
    };
}


#endif
