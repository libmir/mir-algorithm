/++
+/
module mir.primitives;

/++
Returns `true` if `R` has a `length` member that returns an
integral type. `R` does not have to be a range.
+/
template hasLength(R)
{
    enum bool hasLength = is(typeof(
    (R r, inout int = 0)
    {
        size_t l = r.length;
    }));
}

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
