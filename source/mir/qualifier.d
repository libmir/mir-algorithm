/++

Copyright: Ilya Yaroshenko 2018-.
License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors:   Ilya Yaroshenko

Macros:
NDSLICE = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
+/
module mir.qualifier;

import std.traits;
import mir.ndslice.slice: SliceKind, Slice, isSlice;

/++
+/
template LightConstOf(T)
{
    static if (isPointer!T)
    {
        alias LightConstOf = const(PointerTarget!T)*;
    }
    else
    {
        alias LightConstOf = typeof(const(T).init.lightConst());
    }
}

/// ditto
template LightImmutableOf(T)
{
    static if (isPointer!T)
    {
        alias LightImmutableOf = immutable(PointerTarget!T)*;
    }
    else
    {
        alias LightImmutableOf = typeof(immutable(T).init.lightImmutable());
    }
}

///
auto lightConst(SliceKind kind, size_t[] packs, Iterator)(const Slice!(kind, packs, Iterator) e)
{
    return Slice!(kind, packs, LightConstOf!Iterator)(e._lengths, e._strides, e._iterator.lightConst);
}

/// ditto
auto lightConst(SliceKind kind, size_t[] packs, Iterator)(immutable Slice!(kind, packs, Iterator) e)
{
    return e.lightImmutable;
}

/// ditto
auto lightImmutable(SliceKind kind, size_t[] packs, Iterator)(immutable Slice!(kind, packs, Iterator) e)
{
    return Slice!(kind, packs, LightImmutableOf!Iterator)(e._lengths, e._strides, e._iterator.lightImmutable);
}

/// ditto
auto lightConst(T)(auto ref const T e)
    if (isImplicitlyConvertible!(const T, T) && !isSlice!T)
{
    return e;
}

/// ditto
auto lightConst(T)(auto ref immutable T e)
    if (isImplicitlyConvertible!(immutable T, T) && !isSlice!T)
{
    return e;
}

/// ditto
auto lightImmutable(T)(auto ref immutable T e)
    if (isImplicitlyConvertible!(immutable T, T) && !isSlice!T)
{
    return e;
}

/// ditto
auto lightConst(T)(const(T)[] e)
{
    return e;
}

/// ditto
auto lightConst(T)(immutable(T)[] e)
{
    return e;
}

/// ditto
auto lightImmutable(T)(immutable(T)[] e)
{
    return e;
}

/// ditto
auto lightConst(T)(const(T)* e)
{
    return e;
}

/// ditto
auto lightConst(T)(immutable(T)* e)
{
    return e;
}

/// ditto
auto lightImmutable(T)(immutable(T)* e)
{
    return e;
}
