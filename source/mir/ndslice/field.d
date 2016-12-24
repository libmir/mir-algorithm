module mir.ndslice.field;

import mir.internal.utility;
import std.traits;

///
struct BitField(Field, I = typeof(Field.init[size_t.init]))
    if (isIntegral!I)
{
    import core.bitop: bsr;
    private Field field;
    private enum shift = bsr(I.sizeof) + 3;
    private enum mask = (1 << shift) - 1;

    ///
    bool opIndex(size_t index)
    {
        return ((field[index >> shift] & (I(1) << (index & mask)))) != 0;
    }

    static if (__traits(compiles, Field.init[size_t.init] |= I.init))
    ///
    bool opIndexAssign(bool value, size_t index)
    {
        auto m = I(1) << (index & mask);
        index >>= shift;
        if (value)
            field[index] |= m;
        else
            field[index] &= ~m;
        return value;
    }
}

///
BitField!Field bitField(Field)(Field field)
{
    return typeof(return)(field);
}

///
unittest
{
	import mir.ndslice.iterator: fieldIterator;
    short[10] data;
    auto f = data.ptr.bitField.fieldIterator;
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
