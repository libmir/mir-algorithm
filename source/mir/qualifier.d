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

///
version(mir_test) unittest
{
    import mir.math.common;
    import mir.ndslice; //includes Mir's zip
    import mir.qualifier;

    //////////////// Native ///////////////

    auto a = slice!double(5, 5);
    auto b = iota([5, 5]).as!double.slice.lightConst;
    auto c = magic(5).as!double.slice.trustedImmutable;

    static assert(is(typeof(a) == ContiguousMatrix!double));
    static assert(is(typeof(b) == ContiguousMatrix!(const double)));
    static assert(is(typeof(c) == ContiguousMatrix!(immutable double)));

    auto ac = (cast(const) a)[]; //[] calls lightConst
    auto ai = (cast(immutable) a)[]; //[] calls lightImmutable

    static assert(is(typeof(ac) == ContiguousMatrix!(const double)));
    static assert(is(typeof(ai) == ContiguousMatrix!(immutable double)));


    //////////// Incapsulation ////////////

    // zip, map, vmap, zip, indexed, pairwise, slide
    // and all other functons from ndslice.topology support
    // constant propogation
    auto abc0 = zip(a, b, c);
    const abc1 = abc0;
    auto abc2 = abc1[]; //[] calls lightConst

    static assert(is(typeof(abc0) == Slice!(cast(SliceKind)2, [2LU], ZipIterator!(
                double*,  const(double)*, immutable(double)*))));
    static assert(is(typeof(abc2) == Slice!(cast(SliceKind)2, [2LU], ZipIterator!(
        const(double)*, const(double)*, immutable(double)*))));
}

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

@property:

///
auto lightConst(SliceKind kind, size_t[] packs, Iterator)(const Slice!(kind, packs, Iterator) e)
{
    static if (isPointer!Iterator)
        return Slice!(kind, packs, LightConstOf!Iterator)(e._lengths, e._strides, lightConst(e._iterator));
    else
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
    static if (isPointer!Iterator)
        return Slice!(kind, packs, LightImmutableOf!Iterator)(e._lengths, e._strides, lightImmutable(e._iterator));
    else
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

/// ditto
auto trustedImmutable(T)(auto ref const T e) @trusted
{
    return (cast(immutable) e).lightImmutable;
}
