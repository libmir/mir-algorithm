/++
This is a submodule of $(MREF mir,ndslice).

Field is a type with `opIndex(ptrdiff_t index)` primitive.
An iterator can be created on top of a field using $(SUBREF iterator, FieldIterator).
An ndslice can be created on top of a field using $(SUBREF slice, slicedField).

$(BOOKTABLE $(H2 Fields),
$(TR $(TH Field Name) $(TH Used By))
$(T2 BitpackField, $(SUBREF topology, bitpack))
$(T2 BitwiseField, $(SUBREF topology, bitwise))
$(T2 LinspaceField, $(SUBREF topology, linspace))
$(T2 MagicField, $(SUBREF topology, magic))
$(T2 MapField, $(SUBREF topology, map))
$(T2 ndIotaField, $(SUBREF topology, ndiota))
$(T2 OrthogonalReduceField, $(SUBREF topology, orthogonalReduceField))
$(T2 RepeatField, $(SUBREF topology, repeat))
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
import mir.internal.utility: Iota;
import mir.math.common: optmath;
import mir.ndslice.internal;
import mir.qualifier;

@optmath:

auto MapField__map(Field, alias fun, alias fun1)(ref MapField!(Field, fun) f)
{
    import mir.functional: pipe;
    return MapField!(Field, pipe!(fun, fun1))(f._field);
}


/++
`MapField` is used by $(SUBREF topology, map).
+/
struct MapField(Field, alias fun)
{
@optmath:
    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        return MapField!(LightConstOf!Field, fun)(_field.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return MapField!(LightImmutableOf!Field, fun)(_field.lightImmutable);
    }

    /++
    User defined constructor used by $(LREF mapField).
    +/
    static alias __map(alias fun1) = MapField__map!(Field, fun, fun1);

    auto ref opIndex(T...)(auto ref T index)
    {
        import mir.functional: RefTuple, unref;
        static if (is(typeof(_field[index]) : RefTuple!K, K...))
        {
            auto t = _field[index];
            return mixin("fun(" ~ _iotaArgs!(K.length, "t.expand[", "].unref, ") ~ ")");
        }
        else
            return fun(_field[index]);
    }

    auto length()() @property
    {
        return _field.length;
    }

    auto shape()() @property
    {
        return _field.shape;
    }

    auto elementsCount()() @property
    {
        return _field.elementsCount;
    }
}

/++
Creates a mapped field. Uses `__map` if possible.
+/
auto mapField(alias fun, Field)(Field field)
{
    static if (__traits(hasMember, Field, "__map"))
        return Field.__map!fun(field);
    else
        return MapField!(Field, fun)(field);
}

/++
`RepeatField` is used by $(SUBREF topology, repeat).
+/
struct RepeatField(T)
{
@optmath:
    static if (is(T == class) || is(T == interface) || is(T : Unqual!T) && is(Unqual!T : T))
        ///
        alias UT = Unqual!T;
    else
        ///
        alias UT = T;

    ///
    UT _value;

    ///
    auto lightConst()() const @property
    {
        return RepeatField!(const T)(cast(UT) _value);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return RepeatField!(immutable T)(cast(UT) _value);
    }

    auto ref T opIndex()(ptrdiff_t)
    { return cast(T) _value; }
}

/++
`BitwiseField` is used by $(SUBREF topology, bitwise).
+/
struct BitwiseField(Field, I = typeof(Field.init[size_t.init]))
    if (isUnsigned!I)
{
@optmath:
    import core.bitop: bsr;
    package(mir) alias E = I;
    package(mir) enum shift = bsr(I.sizeof) + 3;
    package(mir) enum mask = (1 << shift) - 1;

    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        return BitwiseField!(LightConstOf!Field)(_field.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return BitwiseField!(LightImmutableOf!Field)(_field.lightImmutable);
    }

    bool opIndex()(size_t index)
    {
        return ((_field[index >>> shift] & (I(1) << (index & mask)))) != 0;
    }

    bool opIndexAssign()(bool value, size_t index)
    {
        auto m = I(1) << (index & mask);
        index >>= shift;
        Unqual!I e = _field[index];
        if (value)
            e |= m;
        else
            e &= ~m;
        _field[index] = e;
        return value;
    }
}

///
version(mir_test) unittest
{
	import mir.ndslice.iterator: FieldIterator;
    ushort[10] data;
    auto f = FieldIterator!(BitwiseField!(ushort*))(0, BitwiseField!(ushort*)(data.ptr));
    f[123] = true;
    f++;
    assert(f[122]);
}

/++
`BitpackField` is used by $(SUBREF topology, bitpack).
+/
struct BitpackField(Field, uint pack, I = typeof(Field.init[size_t.init]))
    if (isUnsigned!I)
{
    //static assert();
@optmath:
    package(mir) alias E = I;
    package(mir) enum mask = (I(1) << pack) - 1;
    package(mir) enum bits = I.sizeof * 8;

    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        return BitpackField!(LightConstOf!Field, pack)(_field.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return BitpackField!(LightImmutableOf!Field, pack)(_field.lightImmutable);
    }

    I opIndex()(size_t index)
    {
        index *= pack;
        size_t start = index % bits;
        index /= bits;
        auto ret = (_field[index] >>> start) & mask;
        static if (bits % pack)
        {
            sizediff_t end = start - (bits - pack);
            if (end > 0)
                ret ^= cast(I)(_field[index + 1] << (bits - end)) >>> (bits - pack);
        }
        return cast(I) ret;
    }

    I opIndexAssign()(I value, size_t index)
    {
        assert(cast(Unsigned!I)value <= mask);
        index *= pack;
        size_t start = index % bits;
        index /= bits;
        _field[index] = cast(I)((_field[index] & ~(mask << start)) ^ (value << start));
        static if (bits % pack)
        {
            sizediff_t end = start - (bits - pack);
            if (end > 0)
                _field[index + 1] = cast(I)((_field[index + 1] & ~((I(1) << end) - 1)) ^ (value >>> (pack - end)));
        }
        return value;
    }
}

///
unittest
{
    import mir.ndslice.iterator: FieldIterator;
    ushort[10] data;
    auto f = FieldIterator!(BitpackField!(ushort*, 6))(0, BitpackField!(ushort*, 6)(data.ptr));
    f[0] = cast(ushort) 31;
    f[1] = cast(ushort) 13;
    f[2] = cast(ushort)  8;
    f[3] = cast(ushort) 43;
    f[4] = cast(ushort) 28;
    f[5] = cast(ushort) 63;
    f[6] = cast(ushort) 39;
    f[7] = cast(ushort) 23;
    f[8] = cast(ushort) 44;

    assert(f[0] == 31);
    assert(f[1] == 13);
    assert(f[2] ==  8);
    assert(f[3] == 43);
    assert(f[4] == 28);
    assert(f[5] == 63);
    assert(f[6] == 39);
    assert(f[7] == 23);
    assert(f[8] == 44);
    assert(f[9] == 0);
    assert(f[10] == 0);
    assert(f[11] == 0);
}

unittest
{
    import mir.ndslice.slice;
    import mir.ndslice.topology;
    import mir.ndslice.sorting;
    uint[2] data;
    auto packed = data[].sliced.bitpack!18;
    assert(packed.length == 3);
    packed[0] = 5;
    packed[1] = 3;
    packed[2] = 2;
    packed.sort;
    assert(packed[0] == 2);
    assert(packed[1] == 3);
    assert(packed[2] == 5);
}

///
struct OrthogonalReduceField(FieldsIterator, alias fun)
{
    import mir.ndslice.slice: Slice;

@optmath:
    /// non empty slice

    Slice!FieldsIterator _fields;

    ///
    auto lightConst()() const @property
    {
        auto fields = _fields.lightConst;
        return OrthogonalReduceField!(fields.Iterator, fun)(fields);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        auto fields = _fields.lightImmutable;
        return OrthogonalReduceField!(fields.Iterator, fun)(fields);
    }

    /// `r = fun(r, fields[i][index]);` reduction by `i`
    auto opIndex()(size_t index) const
    {
        assert(_fields.length);
        auto fields = _fields.lightConst;
        Unqual!(typeof(fun(fields.front[index], fields.front[index]))) r = fields.front[index];
        for(;;)
        {
            fields.popFront;
            if (fields.empty)
                break;
            r = fun(r, fields.front[index]);
        }
        return r;
    }
}

/++
`ndIotaField` is used by $(SUBREF topology, ndiota).
+/
struct ndIotaField(size_t N)
    if (N)
{
@optmath:
    ///
    size_t[N - 1] _lengths;

    ///
    auto lightConst()() const @property
    {
        return ndIotaField!N(_lengths);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return ndIotaField!N(_lengths);
    }

    ///
    size_t[N] opIndex()(size_t index) const
    {
        size_t[N] indexes;
        foreach_reverse (i; Iota!(N - 1))
        {
            indexes[i + 1] = index % _lengths[i];
            index /= _lengths[i];
        }
        indexes[0] = index;
        return indexes;
    }
}

/++
`LinspaceField` is used by $(SUBREF topology, linspace).
+/
struct LinspaceField(T)
{
    ///
    size_t _length;

    ///
    T _start = cast(T) 0, _stop = cast(T) 0;

    ///
    auto lightConst()() const @property
    {
        return LinspaceField!T(_length, _start, _stop);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return LinspaceField!T(_length, _start, _stop);
    }

    // no fastmath
    ///
    T opIndex()(sizediff_t index)
    {
        sizediff_t d = _length - 1;
        auto v = typeof(T.init.re)(d - index);
        auto w = typeof(T.init.re)(index);
        v /= d;
        w /= d;
        auto a = v * _start;
        auto b = w * _stop;
        return a + b;
    }

@optmath:

    ///
    size_t length()() @property
    {
        return _length;
    }

    ///
    size_t[1] shape(size_t dimension = 0)() @property @nogc
        if (dimension == 0)
    {
        return [_length];
    }
}

/++
Magic square field.
+/
struct MagicField()
{
@optmath:

    /++
    Magic Square size.
    Should be even.
    +/
    size_t _n;

    ///
    auto lightConst()() const @property
    {
        return MagicField!()(_n);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return MagicField!()(_n);
    }

    ///
    size_t length(size_t dimension = 0)() @property
        if(dimension <= 2)
    {
        return _n * _n;
    }

    ///
    size_t[1] shape()() @property @nogc
    {
        return [_n * _n];
    }

    ///
    size_t opIndex()(size_t index)
    {
        auto d = index / _n;
        auto m = index % _n;
        if (_n & 1)
        {
            //d = _n - 1 - d;     // MATLAB synchronization
            //index = d * _n + m; // ditto
            auto r = (index + 1 - d + (_n - 3) / 2) % _n;
            auto c = (_n * _n - index + 2 * d) % _n;
            return r * _n + c + 1;
        }
        else
        if ((_n & 2) == 0)
        {
            auto a = (d + 1) & 2;
            auto b = (m + 1) & 2;
            return a != b ? index + 1: _n * _n - index;
        }
        else
        {
            auto n = _n / 2 ;
            size_t shift;
            ptrdiff_t q;
            ptrdiff_t p = m - n;
            if (p >= 0)
            {
                m = p;
                shift = n * n;
                auto mul = m <= n / 2 + 1;
                q = d - n;
                if (q >= 0)
                {
                    d = q;
                    mul = !mul;
                }
                if (mul)
                {
                    shift *= 2;
                }
            }
            else
            {
                auto mul = m < n / 2;
                q = d - n;
                if (q >= 0)
                {
                    d = q;
                    mul = !mul;
                }
                if (d == n / 2 && (m == 0 || m == n / 2))
                {
                    mul = !mul;
                }
                if (mul)
                {
                    shift = n * n * 3; 
                }
            }
            index = d * n + m;
            auto r = (index + 1 - d + (n - 3) / 2) % n;
            auto c = (n * n - index + 2 * d) % n;
            return r * n + c + 1 + shift;
        }
    }
}
