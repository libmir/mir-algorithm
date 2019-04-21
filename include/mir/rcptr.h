#ifndef MIR_RCPTR

#define MIR_RCPTR

#include <utility>
#include <cassert>
#include <stdexcept>
#include <memory>
#include <cstdlib>
#include <type_traits>

struct mir_rcarray_context
{
    void* allocator;
    int (*destroyAndDeallocate)(void* allocator, mir_rcarray_context* payload);
    size_t counter;
    size_t length;
};

extern "C"
{
    void mir_rc_increase_counter(mir_rcarray_context* payload);
    void mir_rc_decrease_counter(mir_rcarray_context* payload);
}

// Does not support allocators for now
template <typename T>
struct mir_rcptr
{
private:

    T* _payload = nullptr;
    mir_rcarray_context* _context = nullptr;

public:

    mir_rcptr() noexcept {}
    mir_rcptr(std::nullptr_t) noexcept {}
    ~mir_rcptr() noexcept { if (_context) mir_rc_decrease_counter(_context); }
    mir_rcptr(const mir_rcptr& rhs) noexcept : _payload(rhs._payload), _context((mir_rcarray_context*)rhs._context)  { if (_context) mir_rc_increase_counter(_context); }
    mir_rcptr(mir_rcptr&& rhs) noexcept : _payload(rhs._payload), _context(rhs._context) { rhs.__reset(); }
    mir_rcptr& operator=(const mir_rcptr& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            if (_context) mir_rc_decrease_counter(_context);
            _payload = (T*) rhs._payload;
            _context = (mir_rcarray_context*) rhs._context;
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
        ret.__initialize(true, true);
        ::new(ret.get<U>()) U(std::forward<Args>(args)...);
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
            _context = (mir_rcarray_context*) rhs._context;
            if (_context) mir_rc_increase_counter(_context);
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value>::type>
    mir_rcptr(const mir_rcptr<Q>& rhs) noexcept : _payload(rhs.template get<T>()), _context((mir_rcarray_context*)rhs.getContext())
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
    Q* get() const
    {
        if (_payload == nullptr)
            return nullptr;
        auto ret = dynamic_cast<Q*>((T*)_payload);
        if (ret != nullptr)
            return ret;
        throw std::bad_cast();
    }

    mir_rcarray_context* getContext() noexcept { return _context; }
    mir_rcptr& operator=(std::nullptr_t) noexcept { if (_context) mir_rc_decrease_counter(_context); __reset(); return *this; }
    T& operator*() noexcept { assert(_payload != nullptr); return *_payload; }
    T* operator->() noexcept { assert(_payload != nullptr); return _payload; }
    const mir_rcarray_context* getContext() const noexcept { return _context; }
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

template<class T, class ...Args> 
mir_rcptr<T> mir_make_shared(Args&& ...args)
{
    return mir_rcptr<T>::make_shared(std::forward<Args>(args)...);
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
