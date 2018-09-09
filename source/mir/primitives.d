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
import mir.math.common: optmath;
import std.traits;

@optmath:

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
@safe version(mir_test) unittest
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
    static assert(is(ForeachType!F == size_t));
}));

///
@safe version(mir_test) unittest
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
auto shape(Range)(auto ref Range range) @property
    if (hasLength!Range || hasShape!Range)
{
    static if (__traits(hasMember, Range, "shape"))
    {
        return range.shape;
    }
    else
    {
        size_t[1] ret;
        ret[0] = range.length;
        return ret;
    }
}

///
version(mir_test) unittest
{
    static assert([2, 2, 2].shape == [3]);
}

///
template DimensionCount(T)
{
    import mir.ndslice.slice: Slice, SliceKind;
    /// Extracts dimension count from a $(LREF Slice). Alias for $(LREF isSlice).
    static if(is(T : Slice!(Iterator, N, kind), Iterator, size_t N, SliceKind kind))
      enum size_t DimensionCount = N;
    else
    static if (hasShape!T)
        enum size_t DimensionCount = typeof(T.init.shape).length;
    else
        enum size_t DimensionCount = 1;
}

package(mir) bool anyEmptyShape(size_t N)(auto ref in size_t[N] shape) @property
{
    foreach (i; Iota!N)
        if (shape[i] == 0)
            return true;
    return false;
}

///
bool anyEmpty(Range)(Range range) @property
    if (hasShape!Range || __traits(hasMember, Range, "anyEmpty"))
{
    static if (__traits(hasMember, Range, "anyEmpty"))
    {
        return range.anyEmpty;
    }
    else
    static if (__traits(hasMember, Range, "shape"))
    {
        return anyEmptyShape(range.shape);
    }
    else
    {
        return range.empty;
    }
}

///
size_t elementCount(Range)(Range range) @property
    if (hasShape!Range || __traits(hasMember, Range, "elementCount"))
{
    static if (__traits(hasMember, Range, "elementCount"))
    {
        return range;
    }
    else
    {
        auto sh = range.shape;
        size_t ret = sh[0];
        foreach(i; Iota!(1, sh.length))
        {
            ret *= sh[i];
        }
        return ret;
    }
}

deprecated("use elementCount instead")
alias elementsCount = elementCount;


/++
Returns the element type of a struct with `.DeepElement` inner alias or a type of common array.
Returns `ForeachType` if struct does not have `.DeepElement` member.
+/
template DeepElementType(S)
    if (is(S == struct) || is(S == class) || is(S == interface))
{
    static if (__traits(hasMember, S, "DeepElement"))
        alias DeepElementType = S.DeepElement;
    else
        alias DeepElementType = ForeachType!S;
}

/// ditto
alias DeepElementType(S : T[], T) = T;

///
version(mir_test) unittest
{
    import mir.ndslice.slice;
    import std.range: std_iota = iota;
    static assert(is(DeepElementType!(typeof(std_iota(5))) == int));
    static assert(is(DeepElementType!(Slice!(const(int)*, 2))     == const(int)));
    static assert(is(DeepElementType!(Slice!(immutable(int)*, 2))  == immutable(int)));
}
