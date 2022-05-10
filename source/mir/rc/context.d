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
    extern (C) void function(mir_rc_context*) @system nothrow @nogc pure deallocator;
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
    pragma(inline, true);
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
        // else
        // {
        //     assert(0);
        // }
    }
}

/++
+/
export extern(C)
void mir_rc_delete(ref mir_rc_context context)
    @system nothrow @nogc pure
{
    assert(context.deallocator);
    with(context)
    {
        with(typeInfo)
        {
            if (destructor)
            {
                auto ptr = cast(void*)(&context + 1);
                auto i = length;
                assert(i);
                do
                {
                    destructor(ptr);
                    ptr += size;
                }
                while(--i);
            }
        }
    }
    if (context.counter)
        assert(0);
    version (mir_secure_memory)
    {
        (cast(ubyte*)(&context + 1))[0 .. context.length * context.typeInfo.size] = 0;
    }
    context.deallocator(&context);
}

/++
+/
export extern(C)
mir_rc_context* mir_rc_create(
    ref immutable(mir_type_info) typeInfo,
    size_t length,
    scope const void* payload = null,
    bool initialize = true,
    bool deallocate = true,
    ) @system nothrow @nogc pure
{
    import mir.internal.memory: malloc, free;
    import core.stdc.string: memset, memcpy;

    assert(length);
    auto size = length * typeInfo.size;
    auto fullSize = mir_rc_context.sizeof + size;
    if (auto p = malloc(fullSize))
    {
        version (mir_secure_memory)
        {
            (cast(ubyte*)p)[0 .. fullSize] = 0;
        }
        auto context = cast(mir_rc_context*)p;
        context.deallocator = &free;
        context.typeInfo = &typeInfo;
        context.counter = deallocate;
        context.length = length;

        if (initialize)
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
    ThisTemplate!(const T) lightConst()() return scope const @nogc nothrow @trusted @property
    { return *cast(typeof(return)*) &this; }

    /// ditto
    ThisTemplate!(immutable T) lightImmutable()() return scope immutable @nogc nothrow @trusted @property
    { return *cast(typeof(return)*) &this; }

    ///
    ThisTemplate!(const Unqual!T) moveToConst()() return scope @nogc nothrow @trusted @property
    {
        import core.lifetime: move;
        return move(*cast(typeof(return)*) &this);
    }

    ///
    pragma(inline, true)
    size_t _counter() @trusted scope pure nothrow @nogc const @property
    {
        return cast(bool)this ? context.counter : 0;
    }

    ///
    C opCast(C)() const
        if (is(Unqual!C == bool))
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

    /// ditto
    C opCast(C : ThisTemplate!Q, Q)() pure nothrow @nogc const @system
        if (isImplicitlyConvertible!(immutable(T)*, Q*) && !isImplicitlyConvertible!(const(T)*, Q*))
    {
        return *cast(typeof(return)*)&this;
    }
}
