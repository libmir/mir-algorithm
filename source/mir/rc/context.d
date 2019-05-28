/++
$(H1 Thread-safe reference-counted context implementation).
+/
module mir.rc.context;

import mir.type_info;

/++
+/
struct mir_rc_context
{
    ///
    void* allocator;
    ///
    immutable(mir_type_info)* typeInfo;
    ///
    shared size_t counter;
    ///
    size_t length;
}

/++
Increase counter by 1.

Params:
    context = shared_ptr context (not null)
+/
export extern(C)
void mir_rc_increase_counter(ref mir_rc_context context) @system nothrow @nogc pure
{
    import core.atomic: atomicOp;
    with(context)
    {
        if (counter)
        {
            counter.atomicOp!"+="(1);
        }
    }
}

/++
Decrease counter by 1.
Destroys data if counter decreased from 1 to 0.

Params:
    context = shared_ptr context (not null)
+/
export extern(C)
void mir_rc_decrease_counter(ref mir_rc_context context) @system nothrow @nogc pure
{
    pragma(inline, false);
    import core.atomic: atomicOp;
    with(context)
    {
        if (counter)
        {
            if (counter.atomicOp!"-="(1) == 0)
            {
                mir_rc_delete(context);
            }
        }
    }
}

/++
+/
export extern(C)
void mir_rc_delete(ref mir_rc_context context)
    @system nothrow @nogc pure
{
    with(context)
    {
        with(typeInfo)
        {
            if (destructor)
            {
                auto ptr = cast(void*)(&context + 1);
                foreach(i; 0 .. length)
                {
                    destructor(ptr);
                    ptr += size;
                }
            }
        }
    }
    import mir.internal.memory: free;
    free(&context);
}

/++
+/
export extern(C)
mir_rc_context* mir_rc_create(
    ref immutable(mir_type_info) typeInfo,
    size_t length,
    scope const void* payload = null,
    bool initialise = true,
    bool deallocate = true,
    ) @system nothrow @nogc pure
{
    import mir.internal.memory: malloc;
    import core.stdc.string: memset, memcpy;

    assert(length);
    auto size = length * typeInfo.size;
    if (auto context = cast(mir_rc_context*)malloc(mir_rc_context.sizeof + size))
    {
        context.allocator = null;
        context.typeInfo = &typeInfo;
        context.counter = deallocate;
        context.length = length;

        if (initialise)
        {
            auto ptr = cast(void*)(context + 1);
            if (payload)
            {
                switch(typeInfo.size)
                {
                    case 1:
                        memset(ptr, *cast(ubyte*)payload, size);
                        break;
                    case 2:
                        (cast(ushort*)ptr)[0 .. length] = *cast(ushort*)payload;
                        break;
                    case 4:
                        (cast(uint*)ptr)[0 .. length] = *cast(uint*)payload;
                        break;
                    case 8:
                        (cast(ulong*)ptr)[0 .. length] = *cast(ulong*)payload;
                        break;
                    static if (is(ucent))
                    {
                    case 16:
                        (cast(ucent*)ptr)[0 .. length] = *cast(ucent*)payload;
                        break;
                    }
                    default:
                        foreach(i; 0 .. length)
                        {
                            memcpy(ptr, payload, typeInfo.size);
                            ptr += typeInfo.size;
                        }
                }
            }
            else
            {
                memset(ptr, 0, size);
            }
        }
        return context;
    }
    return null;
}

///
package mixin template CommonRCImpl()
{
    ///
    this(typeof(null))
    {
    }

    ///
    ~this() nothrow
    {
        static if (hasDestructor!T)
        {
            if (false) // break @safe and pure attributes
            {
                Unqual!T* object;
                (*object).__xdtor();
            }
        }
        if (this)
        {
            (() @trusted { mir_rc_decrease_counter(context); })();
            debug _reset;
        }
    }

    ///
    this(this) scope @trusted pure nothrow @nogc
    {
        if (this)
        {
            mir_rc_increase_counter(context);
        }
    }

    ///
    ref opAssign(typeof(null)) scope return
    {
        this = typeof(this).init;
    }

    ///
    ref opAssign(return typeof(this) rhs) scope return @trusted
    {
        this.proxySwap(rhs);
        return this;
    }

    ///
    ref opAssign(Q)(return ThisTemplate!Q rhs) scope return pure nothrow @nogc @trusted
        if (isImplicitlyConvertible!(Q*, T*))
    {
        this.proxySwap(*cast(typeof(this)*)&rhs);
        return this;
    }

    ///
    ThisTemplate!(const T) lightConst()() scope return const @nogc nothrow @trusted @property
    { return *cast(typeof(return)*) &this; }

    /// ditto
    ThisTemplate!(immutable T) lightImmutable()() scope return immutable @nogc nothrow @trusted @property
    { return *cast(typeof(return)*) &this; }

    ///
    pragma(inline, true)
    size_t _counter() @trusted scope pure nothrow @nogc const @property
    {
        return cast(bool)this ? context.counter : 0;
    }

    ///
    bool opCast(C : bool)() const
    {
        return _thisPtr !is null;
    }

    ///
    ref C opCast(C : ThisTemplate!Q, Q)() pure nothrow @nogc @trusted
        if (isImplicitlyConvertible!(T*, Q*))
    {
        return *cast(typeof(return)*)&this;
    }

    /// ditto
    C opCast(C : ThisTemplate!Q, Q)() pure nothrow @nogc const @trusted
        if (isImplicitlyConvertible!(const(T)*, Q*))
    {
        return *cast(typeof(return)*)&this;
    }

    /// ditto
    C opCast(C : ThisTemplate!Q, Q)() pure nothrow @nogc immutable @trusted
        if (isImplicitlyConvertible!(immutable(T)*, Q*))
    {
        return *cast(typeof(return)*)&this;
    }

    ///
    pragma(inline, true)
    bool opEquals(typeof(null)) @safe scope pure nothrow @nogc @property
    {
        return !this;
    }

    /// ditto
    bool opEquals(Y)(auto ref scope const ThisTemplate!Y rhs) @safe scope pure nothrow @nogc @property
    {
        return _thisPtr == _rhs._thisPtr;
    }

    ///
    sizediff_t opCmp(Y)(auto ref scope const ThisTemplate!Y rhs) @trusted scope pure nothrow @nogc @property
    {
        return cast(void*)_thisPtr - cast(void*)_rhs._thisPtr;
    }

    size_t toHash() @trusted scope pure nothrow @nogc @property
    {
        return cast(size_t) _thisPtr;
    }
}
