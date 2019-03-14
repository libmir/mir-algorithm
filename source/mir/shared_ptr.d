/++
$(H1 Thread-safe reference-counted shared pointers).
+/
module mir.shared_ptr;

private static immutable allocationExcMsg = "mir_shared_ptr: out of memory error.";
private static immutable getExcMsg = "mir_shared_ptr: trying to use null value.";

version (D_Exceptions)
{
    import core.exception: OutOfMemoryError, InvalidMemoryOperationError;
    private static immutable allocationError = new OutOfMemoryError(allocationExcMsg);
    private static immutable getError = new InvalidMemoryOperationError(allocationExcMsg);
}

private template StripPointers(T)
{
    static if (is(T : U*, U))
        alias StripPointers = .StripPointers!U;
    else
        alias StripPointers = T;
}

private enum isImmutableOrShared(T) = is(T == immutable) || is(T == shared);

package template cppSupport(T) {

    static if (__VERSION__ < 2082)
        enum cppSupport = false;
    else
    {
        alias S = StripPointers!T;
        static if (isImmutableOrShared!S)
            enum cppSupport = false;
        else
        static if (is(T == class) || is(T == struct) || is(T == union) || is(T == interface))
            enum cppSupport = __traits(getLinkage, T) == "C++";
        else
            enum cppSupport = __traits(isScalar, T);
    }
}

/++
Thread safe reference counting array.

`__xdtor` if any is used to destruct objects.

The implementation never adds roots into the GC.
+/
struct mir_shared_ptr(T, bool cppSupport = .cppSupport!T)
    if (!is(T == class) && !is(T == interface))
{
    import std.traits;
    import mir.ndslice.slice: Slice, SliceKind, Contiguous;

    private struct Context
    {
        void* _delegateContext;
        union
        {
            pure nothrow @nogc bool function(void[]) _function;
            pure nothrow @nogc bool function(void* ctx, void[]) _delegate;
        }
        shared size_t counter;
    }

    static assert(Context.sizeof % 8 == 0);

    ///
    private T* _payload;
    private inout(Context)* _context() inout scope return pure nothrow @nogc @trusted @property
    {
        return cast(inout(Context)*)_payload - 1;
    }

    pragma(inline, false)
    private void __decreaseCounterImplImpl()() scope nothrow @nogc @safe
    {
        import core.atomic: atomicOp;
        with(*_context)
        {
            if (counter)
            {
                if (counter.atomicOp!"-="(1) == 0)
                {
                    Unqual!T* p;
                    ()@trusted { p = cast(Unqual!T*)_payload; }();
                    static if ((is(T == struct) || is(T == union)) && __traits(hasMember, Unqual!T, "__xdtor"))
                    static if (__traits(isSame, Unqual!T, __traits(parent, (*p).__xdtor)))
                        (*p).__xdtor();
                    () @trusted {
                        auto p = cast(void*) _context;
                        with(*_context)
                        {
                            if (_delegateContext !is null)
                            {
                                size_t size = T.sizeof + Context.sizeof;
                                _delegate(_delegateContext, p[0 .. size]);
                            }
                            else
                            if (_function !is null)
                            {
                                size_t size = T.sizeof + Context.sizeof;
                                _function(p[0 .. size]);
                            }
                            else
                            {
                                import mir.internal.memory: free;
                                free(p);
                            }
                        }
                    }();
                }
            }
        }
    }

    static if (cppSupport)
    {
    extern(C++):

        pragma(inline, false)
        private void __decreaseCounterImpl() scope @safe nothrow @nogc
        {
            __decreaseCounterImplImpl();
        }

        pragma(inline, false)
        private bool __initialize(bool deallocate, bool initialize) scope @system nothrow @nogc
        {
            return __initializeImpl(deallocate, initialize);
        }
    }
    else
    {
        pragma(inline, false)
        private void __decreaseCounterImpl() scope @safe nothrow @nogc
        {
            __decreaseCounterImplImpl();
        }

        pragma(inline, false)
        private bool __initialize(bool deallocate, bool initialize) scope @system nothrow @nogc
        {
            return __initializeImpl(deallocate, initialize);
        }
    }

    ///
    this(this) scope @trusted pure nothrow @nogc
    {
        import core.atomic: atomicOp;
        if (_payload !is null) with(*_context)
        {
            if (counter)
            {
                counter.atomicOp!"+="(1);
            }
        }
    }

    ///
    ~this() nothrow @nogc @safe
    {
        if (_payload !is null)
            __decreaseCounterImpl();
    }

    ///
    ref opAssign(typeof(null)) scope return pure nothrow @nogc @trusted
    {
        pragma(inline, true);
        this.__xdtor;
        _payload = null;
        return this;
    }

    static if (is(T == const) || is(T == immutable))
    {
        ///
        ref opAssign(Q)(return scope const mir_shared_ptr!Q rhs) scope pure nothrow @nogc @trusted
            if (isImplicitlyConvertible!(T*, Q*))
        {
            auto lhs_payload = this._payload;
            this._payload = rhs._payload;
            rhs._payload = lhs_payload;
            return this;
        }

        /// ditto
        ref opAssign(Q)(ref return scope const mir_shared_ptr!Q rhs) scope pure nothrow @nogc @trusted
            if (isImplicitlyConvertible!(T*, Q*))
        {
            if (_payload != rhs._payload)
            {
                this.__xdtor;
                _payload = cast(T*) rhs._payload;
                this.__xpostblit;
            }
            return this;
        }
    }
    else
    {
        ///
        ref opAssign(Q)(return scope mir_shared_ptr!Q rhs) scope pure nothrow @nogc @trusted
            if (isImplicitlyConvertible!(T*, Q*))
        {
            auto lhs_payload = this._payload;
            this._payload = rhs._payload;
            rhs._payload = lhs_payload;
            return this;
        }

        /// ditto
        ref opAssign(Q)(ref return scope mir_shared_ptr!Q rhs) scope pure nothrow @nogc @trusted
            if (isImplicitlyConvertible!(T*, Q*))
        {
            if (_payload != rhs._payload)
            {
                this.__xdtor;
                _payload = cast(T*) rhs._payload;
                this.__xpostblit;
            }
            return this;
        }
    }

    private this(Args...)(auto ref Args args) @trusted @nogc
    {
        if (!this.__initialize(true, true))
        {
            version(D_Exceptions)
                throw allocationError;
            else
                assert(0, allocationExcMsg);
        }
        import mir.conv: emplace;
        import mir.functional: forward;
        emplace!T(_payload, forward!args);
    }

    ///
    this(typeof(null))
    {
        pragma(inline, true);
        _payload = null;
    }

    static if (isImplicitlyConvertible!(const T, T))
        static if (isImplicitlyConvertible!(const Unqual!T, T))
            private alias V = const Unqual!T;
        else
            private alias V = const T;
    else
        private alias V = T;

    private bool __initializeImpl()(bool deallocate, bool initialize) scope @trusted nothrow @nogc
    {
        import mir.internal.memory: malloc, alignedAllocate;
        if (T.alignof <= 8)
        {
            _payload = cast(T*) (malloc(T.sizeof + Context.sizeof) + Context.sizeof);
            if (_payload is null)
                return false;
            *_context = Context.init;
        }
        else 
        {
            _payload = cast(T*) (alignedAllocate(T.sizeof + Context.sizeof, T.alignof) + Context.sizeof);
            if (_payload is null)
                return false;
            *_context = Context.init;
            version(Posix) {} // common free
            else
            {
                import mir.internal.memory: alignedFree;
                static bool freeFun(void[] p)
                {
                    alignedFree(p.ptr);
                    return true;
                }
                _context._function = &freeFun;
            }
        }

        _context.counter = deallocate;
        // hasElaborateDestructor is required for safe destruction in case of exceptions
        if (initialize || hasElaborateDestructor!T)
        {
            import mir.conv: emplaceInitializer;
            emplaceInitializer(*cast(Unqual!T*)_payload);
        }
        return true;
    }

    ///
    pragma(inline, true)
    size_t _counter() @trusted scope pure nothrow @nogc const @property
    {
        return _payload !is null ? _context.counter : 0;
    }

    ///
    bool opCast(C : bool)() const
    {
        return _payload !is null;
    }

    ///
    mir_shared_ptr!Q opCast(C : mir_shared_ptr!Q, Q)() pure nothrow @nogc
        if (isImplicitlyConvertible!(T*, Q*))
    {
        mir_shared_ptr!Q ret;
        ret._payload = _payload;
        ret.__xpostblit;
        return ret;
    }

    /// ditto
    mir_shared_ptr!Q opCast(C : mir_shared_ptr!Q, Q)() pure nothrow @nogc const
        if (isImplicitlyConvertible!(const(T)*, Q*))
    {
        mir_shared_ptr!Q ret;
        ret._payload = _payload;
        ret.__xpostblit;
        return ret;
    }

    /// ditto
    mir_shared_ptr!Q opCast(C : mir_shared_ptr!Q, Q)() pure nothrow @nogc immutable
        if (isImplicitlyConvertible!(immutable(T)*, Q*))
    {
        mir_shared_ptr!Q ret;
        ret._payload = _payload;
        ret.__xpostblit;
        return ret;
    }

    ///
    pragma(inline, true)
    bool opEquals(typeof(null)) @safe scope pure nothrow @nogc @property
    {
        return _payload is null;
    }

    /// ditto
    bool opEquals(Y)(auto ref scope const mir_shared_ptr!Y rhs) @safe scope pure nothrow @nogc @property
    {
        return _payload is _rhs._payload;
    }

    /// ditto
    bool opEquals(Y)(scope const Y* rhs) @safe scope pure nothrow @nogc @property
    {
        return _payload is _rhs;
    }

    ///
    sizediff_t opCmp(Y)(auto ref scope const mir_shared_ptr!Y rhs) @safe scope pure nothrow @nogc @property
    {
        return cast(sizediff_t)(_payload - _rhs._payload);
    }

    /// ditto
    sizediff_t opCmp(Y)(scope const Y* rhs) @safe scope pure nothrow @nogc @property
    {
        return cast(sizediff_t)(_payload - _rhs);
    }

    ///
    pragma(inline, true)
    ref inout(T) _get_value() inout
    {
        version(D_Exceptions)
        {
            if (_payload is null)
                throw getError;
        }
        else
        {
            assert(_payload !is null, getError);
        }
        return *_payload;
    }

    /// ditto
    alias opUnary(string op : "*") = _get_value;

    /// ditto
    alias _get_value this;

    ///
    mir_shared_ptr!(const T) lightConst()() scope return const @nogc nothrow @trusted @property
    { return cast(typeof(return)) this; }

    /// ditto
    mir_shared_ptr!(immutable T) lightImmutable()() scope return immutable @nogc nothrow @trusted @property
    { return cast(typeof(return)) this; }
}

/// ditto
alias SharedPtr = mir_shared_ptr;

/// ditto
template shared_ptr(T)
{
    mir_shared_ptr!T shared_ptr(Args...)(auto ref Args args)
    {
        import mir.functional: forward;
        return mir_shared_ptr!T(forward!args);
    }
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    auto a = shared_ptr!double(10);
    auto b = a;
    assert(*b == 10);
    *b = 100;
    assert(*a == 100);
}
