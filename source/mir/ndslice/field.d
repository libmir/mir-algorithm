/++
This is a submodule of $(MREF mir,ndslice).

Field is a type with `opIndex(ptrdiff_t index)` primitive.
An iterator can be created on top of a field using $(SUBREF iterator, FieldIterator).
An ndslice can be created on top of a field using $(SUBREF slice, slicedField).

$(BOOKTABLE $(H2 Fields),
$(TR $(TH Field Name) $(TH Used By))
$(T2 BitField, $(SUBREF topology, bitwise))
$(T2 BitpackField, $(SUBREF topology, bitpack))
$(T2 CycleField, $(SUBREF topology, cycle) (2 kinds))
$(T2 LinspaceField, $(SUBREF topology, linspace))
$(T2 MagicField, $(SUBREF topology, magic))
$(T2 MapField, $(SUBREF topology, map) and $(SUBREF topology, mapField))
$(T2 ndIotaField, $(SUBREF topology, ndiota))
$(T2 OrthogonalReduceField, $(SUBREF topology, orthogonalReduceField))
$(T2 RepeatField, $(SUBREF topology, repeat))
$(T2 SparseField, Used for mutable DOK sparse matrixes )
)



License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.field;

import mir.internal.utility: Iota;
import mir.math.common: optmath;
import mir.ndslice.internal;
import mir.qualifier;

@optmath:

package template ZeroShiftField(T)
{
    static if (hasZeroShiftFieldMember!T)
        alias ZeroShiftField = typeof(T.init.assumeFieldsHaveZeroShift());
    else
        alias ZeroShiftField = T;
}

package enum hasZeroShiftFieldMember(T) = __traits(hasMember, T, "assumeFieldsHaveZeroShift");

package auto applyAssumeZeroShift(Types...)()
{
    import mir.ndslice.topology;
    string str;
    foreach(i, T; Types)
        static if (hasZeroShiftFieldMember!T)
            str ~= "_fields[" ~ i.stringof ~ "].assumeFieldsHaveZeroShift, ";
        else
            str ~= "_fields[" ~ i.stringof ~ "], ";
    return str;
}

auto MapField__map(Field, alias fun, alias fun1)(ref MapField!(Field, fun) f)
{
    import mir.functional: pipe;
    return MapField!(Field, pipe!(fun, fun1))(f._field);
}


/++
`MapField` is used by $(SUBREF topology, map).
+/
struct MapField(Field, alias _fun)
{
@optmath:
    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        return MapField!(LightConstOf!Field, _fun)(.lightConst(_field));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return MapField!(LightImmutableOf!Field, _fun)(.lightImmutable(_field));
    }

    /++
    User defined constructor used by $(LREF mapField).
    +/
    static alias __map(alias fun1) = MapField__map!(Field, _fun, fun1);

    auto ref opIndex(T...)(auto ref T index)
    {
        import mir.functional: RefTuple, unref;
        static if (is(typeof(_field[index]) : RefTuple!K, K...))
        {
            auto t = _field[index];
            return mixin("_fun(" ~ _iotaArgs!(K.length, "t.expand[", "].unref, ") ~ ")");
        }
        else
            return _fun(_field[index]);
    }

    static if (__traits(hasMember, Field, "length"))
    auto length() const @property
    {
        return _field.length;
    }

    static if (__traits(hasMember, Field, "shape"))
    auto shape() const @property
    {
        return _field.shape;
    }

    static if (__traits(hasMember, Field, "elementCount"))
    auto elementCount() const @property
    {
        return _field.elementCount;
    }

    static if (hasZeroShiftFieldMember!Field)
    /// Defined if `Field` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        return _mapField!_fun(_field.assumeFieldsHaveZeroShift);
    }
}

/++
`VmapField` is used by $(SUBREF topology, map).
+/
struct VmapField(Field, Fun)
{
@optmath:
    ///
    Field _field;
    ///
    Fun _fun;

    ///
    auto lightConst()() const @property
    {
        return VmapField!(LightConstOf!Field, _fun)(.lightConst(_field));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return VmapField!(LightImmutableOf!Field, _fun)(.lightImmutable(_field));
    }

    auto ref opIndex(T...)(auto ref T index)
    {
        import mir.functional: RefTuple, unref;
        static if (is(typeof(_field[index]) : RefTuple!K, K...))
        {
            auto t = _field[index];
            return mixin("_fun(" ~ _iotaArgs!(K.length, "t.expand[", "].unref, ") ~ ")");
        }
        else
            return _fun(_field[index]);
    }

    static if (__traits(hasMember, Field, "length"))
    auto length() const @property
    {
        return _field.length;
    }

    static if (__traits(hasMember, Field, "shape"))
    auto shape() const @property
    {
        return _field.shape;
    }

    static if (__traits(hasMember, Field, "elementCount"))
    auto elementCount()const @property
    {
        return _field.elementCount;
    }

    static if (hasZeroShiftFieldMember!Field)
    /// Defined if `Field` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        return _vmapField(_field.assumeFieldsHaveZeroShift, _fun);
    }
}

/+
Creates a mapped field. Uses `__map` if possible.
+/
auto _mapField(alias fun, Field)(Field field)
{
    import mir.functional: naryFun;
    static if ((
        __traits(isSame, fun, naryFun!"a|b") ||
        __traits(isSame, fun, naryFun!"a^b") ||
        __traits(isSame, fun, naryFun!"a&b") ||
        __traits(isSame, fun, naryFun!"a | b") ||
        __traits(isSame, fun, naryFun!"a ^ b") ||
        __traits(isSame, fun, naryFun!"a & b")) &&
        is(Field : ZipField!(BitField!(LeftField, I), BitField!(RightField, I)), LeftField, RightField, I))
    {
        import mir.ndslice.topology: bitwiseField;
        auto f = ZipField!(LeftField, RightField)(field._fields[0]._field, field._fields[1]._field)._mapField!fun;
        return f.bitwiseField!(typeof(f), I);
    }
    else
    static if (__traits(hasMember, Field, "__map"))
        return Field.__map!fun(field);
    else
        return MapField!(Field, fun)(field);
}

/+
Creates a mapped field. Uses `__vmap` if possible.
+/
auto _vmapField(Field, Fun)(Field field, Fun fun)
{
    static if (__traits(hasMember, Field, "__vmap"))
        return Field.__vmap(field, fun);
    else
        return VmapField!(Field, Fun)(field, fun);
}

/++
Iterates multiple fields in lockstep.

`ZipField` is used by $(SUBREF topology, zipFields).
+/
struct ZipField(Fields...)
    if (Fields.length > 1)
{
@optmath:
    import mir.functional: RefTuple, Ref;
    import std.meta: anySatisfy;

    ///
    Fields _fields;

    ///
    auto lightConst()() const @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        import std.meta: staticMap;
        return mixin("ZipField!(staticMap!(LightConstOf, Fields))(%(_fields[%s].lightConst,%)].lightConst)".format(_fields.length.iota));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        import std.meta: staticMap;
        return mixin("ZipField!(staticMap!(LightImmutableOf, Fields))(%(_fields[%s].lightImmutable,%)].lightImmutable)".format(_fields.length.iota));
    }

    auto opIndex()(ptrdiff_t index)
    {
        alias Iterators = Fields;
        alias _iterators = _fields;
        import mir.ndslice.iterator: _zip_types, _zip_index;
        return mixin("RefTuple!(_zip_types!Fields)(" ~ _zip_index!Fields ~ ")");
    }

    auto opIndexAssign(Types...)(RefTuple!(Types) value, ptrdiff_t index)
        if (Types.length == Fields.length)
    {
        foreach(i, ref val; value.expand)
        {
            _fields[i][index] = val;
        }
        return opIndex(index);
    }

    static if (anySatisfy!(hasZeroShiftFieldMember, Fields))
    /// Defined if at least one of `Fields` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        import std.meta: staticMap;
        return mixin("ZipField!(staticMap!(ZeroShiftField, Fields))(" ~ applyAssumeZeroShift!Fields ~ ")");
    }
}

/++
`RepeatField` is used by $(SUBREF topology, repeat).
+/
struct RepeatField(T)
{
    import std.traits: Unqual;

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
`BitField` is used by $(SUBREF topology, bitwise).
+/
struct BitField(Field, I = typeof(cast()Field.init[size_t.init]))
    if (__traits(isUnsigned, I))
{
@optmath:
    import mir.bitop: ctlz;
    package(mir) alias E = I;
    package(mir) enum shift = ctlz(I.sizeof) + 3;

    ///
    Field _field;

    /// optimization for bitwise operations
    auto __vmap(Fun : LeftOp!(op, bool), string op)(Fun fun)
        if (op == "|" || op == "&" || op == "^")
    {
        import mir.ndslice.topology: bitwiseField;
        return _vmapField(_field, RightOp!(op, I)(I(0) - fun.value)).bitwiseField;
    }

    /// ditto
    auto __vmap(Fun : RightOp!(op, bool), string op)(Fun fun)
        if (op == "|" || op == "&" || op == "^")
    {
        import mir.ndslice.topology: bitwiseField;
        return _vmapField(_field, RightOp!(op, I)(I(0) - fun.value)).bitwiseField;
    }

    /// ditto
    auto __vmap(Fun)(Fun fun)
    {
        return VmapField!(typeof(this), Fun)(this, fun);
    }

    /// ditto
    alias __map(alias fun) = BitField__map!(Field, I, fun);

    ///
    auto lightConst()() const @property
    {
        return BitField!(LightConstOf!Field, I)(mir.qualifier.lightConst(_field));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return BitField!(LightImmutableOf!Field, I)(mir.qualifier.lightImmutable(_field));
    }

    bool opIndex()(size_t index)
    {
        import mir.bitop: bt;
        return bt!(Field, I)(_field, index) != 0;
    }

    bool opIndexAssign()(bool value, size_t index)
    {
        import mir.bitop: bta;
        bta!(Field, I)(_field, index, value);
        return value;
    }

    static if (hasZeroShiftFieldMember!Field)
    /// Defined if `Field` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        return BitField!(ZeroShiftField!Field, I)(_field.assumeFieldsHaveZeroShift);
    }
}

///
version(mir_test) unittest
{
	import mir.ndslice.iterator: FieldIterator;
    ushort[10] data;
    auto f = FieldIterator!(BitField!(ushort*))(0, BitField!(ushort*)(data.ptr));
    f[123] = true;
    f++;
    assert(f[122]);
}

auto BitField__map(Field, I, alias fun)(BitField!(Field, I) field)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, fun, naryFun!"~a"))
    {
        import mir.ndslice.topology: bitwiseField;
        auto f = _mapField!fun(field._field);
        return f.bitwiseField!(typeof(f), I);
    }
    else
    {
        return field;
    }
}

/++
`BitpackField` is used by $(SUBREF topology, bitpack).
+/
struct BitpackField(Field, uint pack, I = typeof(cast()Field.init[size_t.init]))
    if (__traits(isUnsigned, I))
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
        return BitpackField!(LightConstOf!Field, pack)(.lightConst(_field));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return BitpackField!(LightImmutableOf!Field, pack)(.lightImmutable(_field));
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
        import std.traits: Unsigned;
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

    static if (hasZeroShiftFieldMember!Field)
    /// Defined if `Field` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        return BitpackField!(ZeroShiftField!Field, pack, I)(_field.assumeFieldsHaveZeroShift);
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
struct OrthogonalReduceField(FieldsIterator, alias fun, T)
{
    import mir.ndslice.slice: Slice;

@optmath:
    /// non empty slice

    Slice!FieldsIterator _fields;

    ///
    T _initialValue;

    ///
    auto lightConst()() const @property
    {
        auto fields = _fields.lightConst;
        return OrthogonalReduceField!(fields.Iterator, fun, T)(fields, _initialValue);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        auto fields = _fields.lightImmutable;
        return OrthogonalReduceField!(fields.Iterator, fun, T)(fields, _initialValue);
    }

    /// `r = fun(r, fields[i][index]);` reduction by `i`
    auto opIndex()(size_t index)
    {
        import std.traits: Unqual;
        auto fields = _fields;
        T r = _initialValue;
        if (!fields.empty) do
        {
            r = cast(T) fun(r, fields.front[index]);
            fields.popFront;
        }
        while(!fields.empty);
        return r;
    }
}

///
struct CycleField(Field)
{
    import mir.ndslice.slice: Slice;

@optmath:
    /// Cycle length
    size_t _length;
    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        auto field = .lightConst(_field);
        return CycleField!(typeof(field))(_length, field);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        auto field = .lightImmutable(_field);
        return CycleField!(typeof(field))(_length, field);
    }

    ///
    auto ref opIndex()(size_t index)
    {
        return _field[index % _length];
    }

    ///
    static if (!__traits(compiles, &opIndex(size_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, size_t index)
        {
            return _field[index % _length] = value;
        }
    }

    static if (hasZeroShiftFieldMember!Field)
    /// Defined if `Field` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        return CycleField!(ZeroShiftField!Field)(_length, _field.assumeFieldsHaveZeroShift);
    }
}

///
struct CycleField(Field, size_t length)
{
    import mir.ndslice.slice: Slice;

@optmath:
    /// Cycle length
    enum _length = length;
    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        auto field = .lightConst(_field);
        return CycleField!(typeof(field), _length)(field);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        auto field = .lightImmutable(_field);
        return CycleField!(typeof(field), _length)(field);
    }

    ///
    auto ref opIndex()(size_t index)
    {
        return _field[index % _length];
    }

    ///
    static if (!__traits(compiles, &opIndex(size_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, size_t index)
        {
            return _field[index % _length] = value;
        }
    }

    static if (hasZeroShiftFieldMember!Field)
    /// Defined if `Field` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        return CycleField!(ZeroShiftField!Field, _length)(_field.assumeFieldsHaveZeroShift);
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
    auto lightImmutable()() const @property
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
    auto lightImmutable()() const @property
    {
        return LinspaceField!T(_length, _start, _stop);
    }

    // no fastmath
    ///
    T opIndex()(sizediff_t index) const
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
    size_t length() const @property
    {
        return _length;
    }

    ///
    size_t[1] shape(size_t dimension = 0)() const @property @nogc
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
    +/
    size_t _n;

    ///
    auto lightConst()() const @property
    {
        return MagicField!()(_n);
    }

    ///
    auto lightImmutable()() const @property
    {
        return MagicField!()(_n);
    }

    ///
    size_t length(size_t dimension = 0)() const @property
        if(dimension <= 2)
    {
        return _n * _n;
    }

    ///
    size_t[1] shape() const @property @nogc
    {
        return [_n * _n];
    }

    ///
    size_t opIndex()(size_t index) const
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

/++
`SparseField` is used to represent Sparse ndarrays in mutable DOK format.
+/
struct SparseField(T)
{
    ///
    T[size_t] _table;

    ///
    auto lightConst()() const @trusted
    {
        return SparseField!(const T)(cast(const(T)[size_t])_table);
    }

    ///
    auto lightImmutable()() immutable @trusted
    {
        return SparseField!(immutable T)(cast(immutable(T)[size_t])_table);
    }

    ///
    T opIndex()(size_t index)
    {
        import std.traits: isScalarType;
        static if (isScalarType!T)
            return _table.get(index, cast(T)0);
        else
            return _table.get(index, null);
    }

    ///
    T opIndexAssign()(T value, size_t index)
    {
        import std.traits: isScalarType;
        static if (isScalarType!T)
        {
            if (value != 0)
                _table[index] = value;
            else
                _table.remove(index);
        }
        else
        {
            if (value !is null)
                _table[index] = value;
            else
                _table.remove(index);
        }
        return value;
    }

    ///
    T opIndexUnary(string op)(size_t index)
        if (op == `++` || op == `--`)
    {
        import std.traits: isScalarType;
        mixin (`auto value = ` ~ op ~ `_table[index];`);
        static if (isScalarType!T)
        {
            if (value == 0)
                _table.remove(index);
        }
        else
        {
            if (value is null)
                _table.remove(index);
        }
        return value;
    }

    ///
    T opIndexOpAssign(string op)(T value, size_t index)
        if (op == `+` || op == `-`)
    {
        import std.traits: isScalarType;
        mixin (`value = _table[index] ` ~ op ~ `= value;`); // this works
        static if (isScalarType!T)
        {
            if (value == 0)
                _table.remove(index);
        }
        else
        {
            if (value is null)
                _table.remove(index);
        }
        return value;
    }
}
