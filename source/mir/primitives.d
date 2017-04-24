/++
Templates used to check primitives.

Publicly imports $(MREF mir,array,_primitives).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
+/
module mir.primitives;

import mir.internal.utility;
public import mir.array.primitives;

@fastmath:

/++
Returns: `true` if `R` has a `length` member that returns an
integral type implicitly convertible to `size_t`.

`R` does not have to be a range.
+/
enum bool hasLength(R) = is(typeof(
(R r, inout int = 0)
{
    size_t l = r.length;
}));

///
@safe unittest
{
    static assert(hasLength!(char[]));
    static assert(hasLength!(int[]));
    static assert(hasLength!(inout(int)[]));

    struct B { size_t length() { return 0; } }
    struct C { @property size_t length() { return 0; } }
    static assert(hasLength!(B));
    static assert(hasLength!(C));
}

/++
Returns: `true` if `R` has a `shape` member that returns an static array type of size_t[N].
+/
enum bool hasShape(R) = is(typeof(
(R r, inout int = 0)
{
    auto l = r.shape;
    alias F = typeof(l);
    import std.traits;
    static assert(isStaticArray!F);
    static assert(is(Unqual!(ForeachType!F) == size_t));
}));

///
@safe unittest
{
    static assert(hasLength!(char[]));
    static assert(hasLength!(int[]));
    static assert(hasLength!(inout(int)[]));

    struct B { size_t length() { return 0; } }
    struct C { @property size_t length() { return 0; } }
    static assert(hasLength!(B));
    static assert(hasLength!(C));
}

///
template DimensionCount(T)
    if (hasShape!T || hasLength!T)
{
    static if (hasShape!T)
        enum size_t DimensionCount = typeof(T.shape).length;
    else
        enum size_t DimensionCount = 1;
}

///
size_t length(size_t d : 0, T)(T[] array)
{
    pragma(inline, true);
    return array.length;
}

///
alias elementsCount = length;
