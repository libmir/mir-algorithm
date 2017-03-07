/++
Templates used to check primitives.
+/
module mir.primitives;

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
