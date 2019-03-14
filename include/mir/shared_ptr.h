#ifndef MIR_RCPTR

#define MIR_RCPTR

#include <atomic>
#include <utility>
#include <cassert>
#include <stdexcept>
#include <memory>
#include <cstdlib>
#include <type_traits>

// Does not support allocators for now
template <typename T, bool _unused_ = true>
struct mir_shared_ptr
{
private:

    T* _payload = nullptr;

    struct Context
    {
        void* _delegateContext;
        void* _function;
        std::atomic_size_t counter;
    };

    Context* _context() noexcept { return (Context*)_payload - 1; }
    const Context* _context() const noexcept { return (const Context*)_payload - 1; }

    bool __initialize(bool deallocate, bool initialize) noexcept;
    void __decreaseCounterImpl() noexcept;

public:

    void _increase_counter() noexcept { if (_payload && _context()->counter) _context()->counter++; }
    void _decrease_counter() noexcept { if (_payload) __decreaseCounterImpl(); }
    mir_shared_ptr() noexcept {}
    mir_shared_ptr(std::nullptr_t) noexcept {}
    ~mir_shared_ptr() noexcept { _decrease_counter(); }
    mir_shared_ptr(const mir_shared_ptr& rhs) noexcept : _payload(rhs._payload) { _increase_counter(); }
    mir_shared_ptr(mir_shared_ptr&& rhs) noexcept : _payload(rhs._payload) { rhs._payload = nullptr; }
    mir_shared_ptr& operator=(const mir_shared_ptr& rhs) noexcept
    {
        if (_payload != rhs._payload)
        {
            _decrease_counter();
            _payload = (T*) rhs._payload;
            _increase_counter();;
        }
        return *this;
    }

    template<class ...Args> 
    static mir_shared_ptr make_shared(Args&& ...args)
    {
        using U = typename std::remove_const<T>::type;
        static_assert( std::is_constructible<U, Args...>::value, "Can't construct object in mir_shared_ptr constructor" );
        mir_shared_ptr ret;
        ret.__initialize(true, true);
        ::new((U*)ret.get()) U(std::forward<Args>(args)...);
        return ret;
    }

    void __reset() { _payload = nullptr; }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_shared_ptr& operator=(const mir_shared_ptr<Q>& rhs) noexcept
    {
        if (_payload != rhs.get())
        {
            _decrease_counter();
            _payload = (T*) rhs.get();
            _increase_counter();;
        }
        return *this;
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_shared_ptr(const mir_shared_ptr<Q>& rhs) noexcept : _payload(rhs.get())
    {
        _increase_counter();
    }

    template<class Q, class = typename std::enable_if<!std::is_same<Q, T>::value && std::is_same<const Q, T>::value>::type>
    mir_shared_ptr(mir_shared_ptr<Q>&& rhs) noexcept : _payload(rhs.get())
    {
        rhs.__reset();
    }

    mir_shared_ptr<const T>& light_const() noexcept { return *(mir_shared_ptr<const T>*)this; }

    T* get() noexcept { return _payload; }
    mir_shared_ptr& operator=(std::nullptr_t) noexcept { _decrease_counter(); _payload = nullptr; return *this; }
    T& operator*() noexcept { assert(_payload != nullptr); return *_payload; }
    T* operator->() noexcept { assert(_payload != nullptr); return _payload; }
    const T* get() const noexcept { return _payload; }
    const T& operator*() const noexcept { assert(_payload != nullptr); return *_payload; }
    const T* operator->() const noexcept { assert(_payload != nullptr); return _payload; }
    template<class Y> bool operator==(const mir_shared_ptr<Y>& rhs) const noexcept { return _payload == rhs._payload; }
    template<class Y> bool operator!=(const mir_shared_ptr<Y>& rhs) const noexcept { return _payload != rhs._payload; }
    template<class Y> bool operator<=(const mir_shared_ptr<Y>& rhs) const noexcept { return _payload <= rhs._payload; }
    template<class Y> bool operator>=(const mir_shared_ptr<Y>& rhs) const noexcept { return _payload >= rhs._payload; }
    template<class Y> bool operator<(const mir_shared_ptr<Y>& rhs) const noexcept { return _payload < rhs._payload; }
    template<class Y> bool operator>(const mir_shared_ptr<Y>& rhs) const noexcept { return _payload > rhs._payload; }
    explicit operator bool() const noexcept { return _payload != nullptr; }
};

template<class T, class ...Args> 
mir_shared_ptr<T> mir_make_shared(Args&& ...args)
{
    return mir_shared_ptr<T>::make_shared(std::forward<Args>(args)...);
}

namespace std
{
    template <class T>
    struct hash<mir_shared_ptr<T> >
    {
        typedef mir_shared_ptr<T> argument_type;
        typedef size_t result_type;

        result_type operator()(const argument_type& ptr) const noexcept
        {
            return (result_type)(ptr.get());
        }
    };
}


#endif
