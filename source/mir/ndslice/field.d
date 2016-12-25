module mir.ndslice.field;

import mir.internal.utility;
import std.traits;

///
struct RepeatField(T)
{
    // UT definition is from std.range
    // Store a non-qualified T when possible: This is to make RepeatField assignable
    static if ((is(T == class) || is(T == interface)) && (is(T == const) || is(T == immutable)))
    {
        import std.typecons : Rebindable;
        private alias UT = Rebindable!T;
    }
    else static if (is(T : Unqual!T) && is(Unqual!T : T))
        private alias UT = Unqual!T;
    else
        private alias UT = T;
    private UT _value;

    auto ref T opIndex(ptrdiff_t)
    { return _value; }
}

///
struct BitwiseField(Field, I = typeof(Field.init[size_t.init]))
    if (isIntegral!I)
{
    Field _field;
    import core.bitop: bsr;
    private enum shift = bsr(I.sizeof) + 3;
    private enum mask = (1 << shift) - 1;

    ///
    bool opIndex(size_t index)
    {
        return ((_field[index >> shift] & (I(1) << (index & mask)))) != 0;
    }

    static if (__traits(compiles, Field.init[size_t.init] |= I.init))
    ///
    bool opIndexAssign(bool value, size_t index)
    {
        auto m = I(1) << (index & mask);
        index >>= shift;
        if (value)
            _field[index] |= m;
        else
            _field[index] &= ~m;
        return value;
    }
}

///
unittest
{
	import mir.ndslice.iterator: FieldIterator;
    short[10] data;
    auto f = FieldIterator!(BitwiseField!(short*))(0, BitwiseField!(short*)(data.ptr));
    f[123] = true;
    f++;
    assert(f[122]);
}

/++
Iterator composed of indexes.
See_also: $(LREF ndiota)
+/
struct ndIotaField(size_t N)
    if (N)
{
    private size_t[N-1] _lengths;

    ///
    size_t[N] opIndex(size_t index) const
    {
        size_t[N] indexes = void;
        foreach_reverse (i; Iota!(N - 1))
        {
            indexes[i + 1] = index % _lengths[i];
            index /= _lengths[i];
        }
        indexes[0] = index;
        return indexes;
    }
}
