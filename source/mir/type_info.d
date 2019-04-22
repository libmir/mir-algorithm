/++
$(H1 Type Information)

Type Information implementation compatible with BetterC mode.

Copyright: Copyright © 2019, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
NDSLICE = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.type_info;

import std.traits: Unqual;

/++
+/
struct mir_type_info
{
    ///
    extern(C)
    void function(scope void*) @safe pure nothrow @nogc destructor;
    /++
    Note: Negative values are used for classes to indicate that 
    +/
    int size;
}

/++
+/
ref immutable(mir_type_info) mir_get_type_info(T)()
{
    static if (is(T == class))
        enum sizeof = __traits(classInstanceSize, T);
    else
        enum sizeof = T.sizeof;

    static if (!is(T == Unqual!T))
    {
        return mir_get_type_info!(Unqual!T);
    }
    else
    static if (hasDestructor!T)
    {
        extern(C)
        static void destroy_impl(void* ptr) @safe pure nothrow @nogc
        {
            static if (is(T == class))
                T inst() return @trusted
                {
                    return cast(T)ptr;
                }
            else
                ref T inst() return @trusted
                {
                    return *cast(T*)ptr;
                }
            version(assert)
                destroy!true(inst());
            else
                destroy!false(inst());
        }

        static immutable ti = mir_type_info(&destroy_impl, sizeof);
        return ti;
    }
    else
    {
        return .mir_get_type_info!sizeof;
    }
}

/++
+/
ref immutable(mir_type_info) mir_get_type_info(uint sizeof)()
{
    static immutable ti = mir_type_info(null, sizeof);
    return ti;
}

package template hasDestructor(T)
{
    static if (is(T == struct))
    {
        static if (__traits(hasMember, Unqual!T, "__xdtor"))
            enum hasDestructor = __traits(isSame, Unqual!T, __traits(parent, T.init.__xdtor));
        else
            enum hasDestructor = false;
    }
    else
    static if (is(T == class))
    {
        enum hasDestructor = __traits(hasMember, Unqual!T, "__xdtor");
    }
    else
    {
        enum hasDestructor = false;
    }
}

package const(void)* mir_get_payload_ptr(T)()
{
    static if (!is(T == Unqual!T))
    {
        return mir_get_payload_ptr!(Unqual!T);
    }
    else
    static if (is(T == class))
    {
        return typeid(T).initializer.ptr;
    }
    else
    static if (__traits(isZeroInit, T) || __traits(isFloating, T))
    {
        return null;
    }
    else
    {
        static immutable payload = T.init;
        return &payload;
    }
}
