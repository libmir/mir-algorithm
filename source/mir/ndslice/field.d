/++
This is a submodule of $(MREF mir,ndslice).

Field is a type with `opIndex(ptrdiff_t index)` primitive.
An iterator can be created on top of a field using $(REF FieldIterator, mir,ndslice,iterator).
An ndslice can be created on top of a field using $(REF slicedField, mir,ndslice,slice).

$(BOOKTABLE $(H2 Fields),
$(TR $(TH Field Name) $(TH Used By))
$(T2 BitwiseField, $(REF bitwise, mir,ndslice,topology))
$(T2 MapField, $(REF map, mir,ndslice,topology))
$(T2 ndIotaField, $(REF ndiota, mir,ndslice,topology))
$(T2 RepeatField, $(REF repeat, mir,ndslice,topology))
)


License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.field;

import std.traits;
import mir.internal.utility;
import mir.ndslice.internal;

@fastmath:

/++
`MapField` is used by $(REF map, mir,ndslice,topology).
+/
struct MapField(Field, alias fun)
{
@fastmath:
    ///
    Field _field;

    /++
    User defined constructor used by $(LREF mapField).
    +/
    static auto __map(alias fun1)(ref typeof(this) f)
    {
        import mir.funcitonal: pipe;
        return MapField!(Field, pipe!(fun, fun1))(f._field);
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        return fun(_field[index]);
    }
}

/++
Creates a mapped field. Uses `__map` if possible.
+/
static auto mapField(alias fun, Field)(Field field)
{
    static if (__traits(hasMember, Field, "__map"))
        return Field.__map!fun(field);
    else
        return MapField!(Field, fun)(field);
}

/++
`RepeatField` is used by $(REF repeat, mir,ndslice,topology).
+/
struct RepeatField(T)
{
@fastmath:
    static if (is(T == class) || is(T == interface) || is(T : Unqual!T) && is(Unqual!T : T))
        ///
        alias UT = Unqual!T;
    else
        ///
        alias UT = T;

    ///
    UT _value;

    auto ref T opIndex(ptrdiff_t)
    { return cast(T) _value; }
}

/++
`BitwiseField` is used by $(REF bitwise, mir,ndslice,topology).
+/
struct BitwiseField(Field, I = typeof(Field.init[size_t.init]))
    if (isIntegral!I)
{
@fastmath:
    import core.bitop: bsr;
    package alias E = I;
    package enum shift = bsr(I.sizeof) + 3;
    package enum mask = (1 << shift) - 1;

    ///
    Field _field;

    bool opIndex(size_t index)
    {
        return ((_field[index >> shift] & (I(1) << (index & mask)))) != 0;
    }

    static if (__traits(compiles, Field.init[size_t.init] |= I.init))
    bool opIndexAssign()(bool value, size_t index)
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
`ndIotaField` is used by $(REF ndiota, mir,ndslice,topology).
+/
struct ndIotaField(size_t N)
    if (N)
{
@fastmath:
    ///
    size_t[N - 1] _lengths;

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
