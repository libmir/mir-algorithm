/++
This is a submodule of $(MREF mir,ndslice).

Iterator is a type with a pointer like behavior.
An ndslice can be created on top of an iterator using $(SUBREF slice, sliced).

$(BOOKTABLE $(H2 Iterators),
$(TR $(TH Iterator Name) $(TH Used By))
$(T2 BytegroupIterator, $(SUBREF topology, bytegroup).)
$(T2 FieldIterator, $(SUBREF slice, slicedField), $(SUBREF topology, bitwise), $(SUBREF topology, ndiota), and others.)
$(T2 FlattenedIterator, $(SUBREF topology, flattened))
$(T2 IndexIterator, $(SUBREF topology, indexed))
$(T2 IotaIterator, $(SUBREF topology, iota))
$(T2 MapIterator, $(SUBREF topology, map))
$(T2 RetroIterator, $(SUBREF topology, retro))
$(T2 SliceIterator, $(SUBREF topology, map) in composition with $(LREF MapIterator) for packed slices.)
$(T2 SlideIterator, $(SUBREF topology, diff), $(SUBREF topology, pairwise), and $(SUBREF topology, slide).)
$(T2 StairsIterator, $(SUBREF topology, stairs))
$(T2 StrideIterator, $(SUBREF topology, stride))
$(T2 ZipIterator, $(SUBREF topology, zip))
)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.iterator;

import std.traits;
import mir.internal.utility: Iota;
import mir.math.common: optmath;
import mir.ndslice.slice: SliceKind, Slice, Universal, Canonical, Contiguous;
import mir.ndslice.internal;

@optmath:

enum std_ops = q{
    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin(op ~ "_iterator;"); }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index;"); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    { return this._iterator - right._iterator; }

    bool opEquals()(ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
};

/++
Step counter.

`IotaIterator` is used by $(SUBREF topology, iota).
+/
struct IotaIterator(I)
    if (isIntegral!I || isPointer!I)
{
@optmath:
    ///
    I _index;

    I opUnary(string op : "*")()
    { return _index; }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin(op ~ `_index;`); }

    I opIndex()(ptrdiff_t index) const
    { return cast(I)(_index + index); }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == `+` || op == `-`)
    { mixin(`_index ` ~ op ~ `= index;`); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(typeof(this) right) const
    { return this._index - right._index; }

    bool opEquals()(typeof(this) right) const
    { return this._index == right._index; }

    ptrdiff_t opCmp()(typeof(this) right) const
    { return this._index - right._index; }
}

///
@safe pure nothrow @nogc version(mir_test) unittest
{
    IotaIterator!int iota;
    assert(*iota == 0);

    // iteration
    ++iota;
    assert(*iota == 1);
    
    assert(iota[2] == 3);
    assert(iota[-1] == 0);

    --iota;
    assert(*iota == 0);

    // opBinary
    assert(*(iota + 2) == 2);
    assert(*(iota - 3) == -3);
    assert((iota - 3) - iota == -3);

    // construction
    assert(*IotaIterator!int(3) == 3);
    assert(iota - 1 < iota);
}

///
pure nothrow @nogc version(mir_test) unittest
{
    int[32] data;
    auto iota = IotaIterator!(int*)(data.ptr);
    assert(*iota == data.ptr);

    // iteration
    ++iota;
    assert(*iota == 1 + data.ptr);
    
    assert(iota[2] == 3 + data.ptr);
    assert(iota[-1] == 0 + data.ptr);

    --iota;
    assert(*iota == 0 + data.ptr);

    // opBinary
    assert(*(iota + 2) == 2 + data.ptr);
    assert(*(iota - 3) == -3 + data.ptr);
    assert((iota - 3) - iota == -3);

    // construction
    assert(*IotaIterator!(int*)(data.ptr) == data.ptr);
    assert(iota - 1 < iota);
}

auto RetroIterator__map(Iterator, alias fun)(ref RetroIterator!Iterator it)
{
    auto iterator = it._iterator.mapIterator!fun;
    return RetroIterator!(typeof(iterator))(iterator);
}

version(mir_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = iota(9).retro.map!(a => a).slice;
    uint r;
    auto w = iota(9).retro.map!(a => a).map!(a => a * r).slice;
}

/++
Reverse directions for an iterator.

`RetroIterator` is used by $(SUBREF topology, retro).
+/
struct RetroIterator(Iterator)
{
@optmath:
    ///
    Iterator _iterator;

    ///
    static alias __map(alias fun) = RetroIterator__map!(Iterator, fun);

    auto ref opUnary(string op : "*")()
    { return *_iterator; }

    void opUnary(string op : "--")()
    { ++_iterator; }

    void opUnary(string op : "++")()
    { --_iterator; }

    auto ref opIndex()(ptrdiff_t index)
    { return *(_iterator - index); }

    void opOpAssign(string op : "-")(ptrdiff_t index)
    { _iterator += index; }

    void opOpAssign(string op : "+")(ptrdiff_t index)
    { _iterator -= index; }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    { return right._iterator - this._iterator; }

    bool opEquals()(ref const typeof(this) right) const
    { return right._iterator == this._iterator; }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            return right._iterator - this._iterator;
        else
            return right._iterator.opCmp(this._iterator);
    }
}

///
@safe pure nothrow @nogc version(mir_test) unittest
{
    IotaIterator!int iota;
    RetroIterator!(IotaIterator!int) retro;

    ++iota;
    --retro;
    assert(*retro == *iota);

    --iota;
    ++retro;
    assert(*retro == *iota);

    assert(retro[-7] == iota[7]);

    iota += 100;
    retro -= 100;
    assert(*retro == *iota);

    iota -= 100;
    retro += 100;
    assert(*retro == *iota);

    assert(*(retro + 10) == *(iota - 10));

    assert(retro - 1 < retro);

    assert((retro - 5) - retro == -5);

    iota = IotaIterator!int(3);
    retro = RetroIterator!(IotaIterator!int)(iota);
    assert(*retro == *iota);
}

auto StrideIterator__map(Iterator, alias fun)(ref StrideIterator!Iterator it)
{
    auto iterator = it._iterator.mapIterator!fun;
    return StrideIterator!(typeof(iterator))(it._stride, iterator);
}

version(mir_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = iota([3], 0, 3).map!(a => a).slice;
    uint r;
    auto w = iota([3], 0, 3).map!(a => a).map!(a => a * r).slice;
}

/++
Iterates an iterator with a fixed strides.

`StrideIterator` is used by $(SUBREF topology, stride).
+/
struct StrideIterator(Iterator)
{
@optmath:
    ///
    ptrdiff_t _stride;
    ///
    Iterator _iterator;

    ///
    static alias __map(alias fun) = StrideIterator__map!(Iterator, fun);

    auto ref opUnary(string op : "*")()
    { return *_iterator; }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin("_iterator " ~ op[0] ~ "= _stride;"); }

    auto ref opIndex()(ptrdiff_t index)
    { return _iterator[index * _stride]; }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index * _stride;"); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    { return (this._iterator - right._iterator) / _stride; }

    bool opEquals()(ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            ptrdiff_t ret = this._iterator - right._iterator;
        else
            ptrdiff_t ret = this._iterator.opCmp(right._iterator);
        return _stride >= 0 ? ret : -ret;
    }
}

///
@safe pure nothrow @nogc version(mir_test) unittest
{
    IotaIterator!int iota;
    StrideIterator!(IotaIterator!int) stride;
    stride._stride = -3;

    iota -= stride._stride;
    --stride;
    assert(*stride == *iota);

    iota += stride._stride;
    ++stride;
    assert(*stride == *iota);

    assert(stride[7] == iota[7 * stride._stride]);

    iota -= 100 * stride._stride;
    stride -= 100;
    assert(*stride == *iota);

    iota += 100 * stride._stride;
    stride += 100;
    assert(*stride == *iota);

    assert(*(stride + 10) == *(iota + 10 * stride._stride));

    assert(stride - 1 < stride);

    assert((stride - 5) - stride == -5);

    iota = IotaIterator!int(3);
    stride = StrideIterator!(IotaIterator!int)(3, iota);
    assert(*stride == *iota);
}

private template _zip_types(Iterators...)
{
    import std.meta: AliasSeq;
    static if (Iterators.length)
    {
        enum i = Iterators.length - 1;
        static if (__traits(compiles, &*Iterators[i].init))
        {
            import mir.functional: Ref;
            alias _zip_types = AliasSeq!(_zip_types!(Iterators[0 .. i]), Ref!(typeof(*Iterators[i].init)));
        }
        else
            alias _zip_types = AliasSeq!(_zip_types!(Iterators[0 .. i]), typeof(*Iterators[i].init));
    }
    else
        alias _zip_types = AliasSeq!();
}

private template _zip_fronts(Iterators...)
{
    static if (Iterators.length)
    {
        enum i = Iterators.length - 1;
        static if (__traits(compiles, &*Iterators[i].init))
            enum _zip_fronts = _zip_fronts!(Iterators[0 .. i]) ~ "Ref!(typeof(*Iterators[" ~ i.stringof ~ "].init))(*_iterators[" ~ i.stringof ~ "]), ";
        else
            enum _zip_fronts = _zip_fronts!(Iterators[0 .. i]) ~ "*_iterators[" ~ i.stringof ~ "], ";
    }
    else
        enum _zip_fronts = "";
}

private template _zip_index(Iterators...)
{
    static if (Iterators.length)
    {
        enum i = Iterators.length - 1;
        static if (__traits(compiles, &*Iterators[i].init))
            enum _zip_index = _zip_index!(Iterators[0 .. i]) ~ "Ref!(typeof(*Iterators[" ~ i.stringof ~ "].init))(_iterators[" ~ i.stringof ~ "][index]), ";
        else
            enum _zip_index = _zip_index!(Iterators[0 .. i]) ~ "_iterators[" ~ i.stringof ~ "][index], ";
    }
    else
        enum _zip_index = "";
}

/++
Iterates multiple iterators in lockstep.

`ZipIterator` is used by $(SUBREF topology, zip).
+/
struct ZipIterator(Iterators...)
    if (Iterators.length > 1)
{
@optmath:
    import mir.functional: RefTuple, Ref;
    ///
    Iterators _iterators;

    auto opUnary(string op : "*")()
    { return mixin("RefTuple!(_zip_types!Iterators)(" ~ _zip_fronts!Iterators ~ ")"); }

    void opUnary(string op)()
        if (op == "++" || op == "--")
    {
        foreach (ref _iterator; _iterators)
            mixin(op ~ `_iterator;`);
    }

    auto opIndex()(ptrdiff_t index)
    { return mixin("RefTuple!(_zip_types!Iterators)(" ~ _zip_index!Iterators ~ ")"); }

    auto opIndexAssign(Types...)(RefTuple!(Types) value, ptrdiff_t index)
        if (Types.length == Iterators.length)
    {
        foreach(i, val; value.expand)
        {
            _iterators[i][index] = val;
        }
        return opIndex(index);
    }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        foreach (ref _iterator; _iterators)
            mixin(`_iterator ` ~ op ~ `= index;`);
    }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    { return this._iterators[0] - right._iterators[0]; }

    bool opEquals()(ref const typeof(this) right) const
    { return this._iterators[0] == right._iterators[0]; }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    {
        static if (isPointer!(Iterators[0]))
            return this._iterators[0] - right._iterators[0];
        else
            return this._iterators[0].opCmp(right._iterators[0]);
    }
}

///
pure nothrow @nogc version(mir_test) unittest
{
    double[10] data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    alias ItA = IotaIterator!int;
    alias ItB = double*;
    alias ItZ = ZipIterator!(ItA, ItB);
    auto zip = ItZ(ItA(3), data.ptr);
    assert((*zip).a == 3);
    assert((*zip).b == 1);

    // iteration
    ++zip;
    assert((*zip).a == 3 + 1);
    assert((*zip).b == 1 + 1);
    assert(&(*zip).b() == data.ptr + 1);
    
    assert(zip[4].a == 3 + 5);
    assert(zip[4].b == 1 + 5);
    assert(&zip[4].b() == data.ptr + 5);

    --zip;
    assert((*zip).a == 3);
    assert((*zip).b == 1);

    assert((*(zip + 2)).a == 3 + 2);
    assert((*(zip - 3)).a == 3 + -3);
    assert((*(zip + 2)).b == 1 + 2);
    assert((*(zip + 3 - 3)).b == 1);
    assert((zip - 3).opBinary!"-"(zip) == -3);

    assert(zip == zip);
    assert(zip - 1 < zip);
}

private enum map_primitives = q{

    import mir.functional: RefTuple, unref;

    auto ref opUnary(string op : "*")()
    {
        static if (is(typeof(*_iterator) : RefTuple!T, T...))
        {
            auto t = *_iterator;
            return mixin("fun(" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ ")");
        }
        else
            return fun(*_iterator);
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = _iterator[index];
            return mixin("fun(" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ ")");
        }
        else
            return fun(_iterator[index]);
    }

    static if (!__traits(compiles, &opIndex(ptrdiff_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("fun(" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ ") = value");
            }
            else
                return fun(_iterator[index]) = value;
        }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin(op ~ "fun(" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ ")");
            }
            else
                return mixin(op ~ "fun(_iterator[index])");
        }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("fun(" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ ")" ~ op ~ "= value");
            }
            else
                return mixin("fun(_iterator[index])" ~ op ~ "= value");
        }
    }
};

/++
`VmapIterator` is used by $(SUBREF topology, map).
+/
struct VmapIterator(Iterator, Fun)
{
@optmath:
    ///
    Iterator _iterator;
    ///
    Fun fun;

    mixin(map_primitives);
    mixin(std_ops);
}

auto MapIterator__map(Iterator, alias fun0, alias fun)(ref MapIterator!(Iterator, fun0) it)
{
    return MapIterator!(Iterator, fun)(it._iterator);
}

/++
`MapIterator` is used by $(SUBREF topology, map).
+/
struct MapIterator(Iterator, alias fun)
{
@optmath:
    ///
    Iterator _iterator;

    import mir.functional: pipe;
    ///
    static alias __map(alias fun1) = MapIterator__map!(Iterator, fun, pipe!(fun, fun1));

    mixin(map_primitives);
    mixin(std_ops);
}

/++
Creates a mapped iterator. Uses `__map` if possible.
+/
auto mapIterator(alias fun, Iterator)(Iterator iterator)
{
    static if (__traits(hasMember, Iterator, "__map"))
    {
        static if (is(Iterator : MapIterator!(Iter0, fun0), Iter0, alias fun0)
                && !__traits(compiles, Iterator.__map!fun(iterator)))
        {
            // https://github.com/libmir/mir-algorithm/issues/111
            pragma(msg, __FUNCTION__~" not coalescing chained map calls into a single lambda, possibly because of multiple embedded context pointers");
            return MapIterator!(Iterator, fun)(iterator);
        }
        else
            return Iterator.__map!fun(iterator);
    }
    else
       return MapIterator!(Iterator, fun)(iterator);
}

@safe pure nothrow @nogc version(mir_test) unittest
{
    // https://github.com/libmir/mir-algorithm/issues/111
    import mir.ndslice.topology : iota, map;
    import mir.functional : pipe;

    static auto foo(T)(T x)
    {
        return x.map!(a => a + 1);
    }

    static auto bar(T)(T x)
    {
        return foo(x).map!(a => a + 2);
    }

    auto data = iota(5);
    auto result = iota([5], 3);

    auto x = data.map!(a => a + 1).map!(a => a + 2);
    assert(x == result);

    auto y = bar(data);
    assert(y == result);
}

/++
`BytegroupIterator` is used by $(SUBREF topology, Bytegroup) and $(SUBREF topology, bytegroup).
+/
struct BytegroupIterator(Iterator, size_t count, DestinationType)
    if (count)
{
@optmath:
    ///
    Iterator _iterator;

    package alias Byte = Unqual!(typeof(_iterator[0]));

    version(LittleEndian)
        private enum BE = false;
    else
        private enum BE = true;

    private union U
    {
        DestinationType value;
        static if (DestinationType.sizeof > Byte[count].sizeof && BE && isScalarType!DestinationType)
        {
            struct
            {
                ubyte[DestinationType.sizeof - Byte[count].sizeof] shiftPayload;
                Byte[count] bytes;
            }
        }
        else
        {
            Byte[count] bytes;
        }
    }

    DestinationType opUnary(string op : "*")()
    {
        U ret = { value: DestinationType.init };
        foreach (i; Iota!count)
            ret.bytes[i] = _iterator[i];
        return ret.value;
    }

    DestinationType opIndex()(ptrdiff_t index)
    {
        return *(this + index);
    }

    DestinationType opIndexAssign(T)(auto ref T val, ptrdiff_t index)
    {
        auto it = this + index;
        U ret = { value: val };
        foreach (i; Iota!count)
            it._iterator[i] = ret.bytes[i];
        return ret.value;
    }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin("_iterator " ~ op[0] ~ "= count;"); }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index * count;"); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    { return (this._iterator - right._iterator) / count; }

    bool opEquals()(ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
}

auto SlideIterator__map(Iterator, size_t params, alias fun0, alias fun)(ref SlideIterator!(Iterator, params, fun0) it)
{
    return SlideIterator!(Iterator, params, fun)(it._iterator);
}

/++
`SlideIterator` is used by $(SUBREF topology, diff) and $(SUBREF topology, slide).
+/
struct SlideIterator(Iterator, size_t params, alias fun)
    if (params > 1)
{
@optmath:
    ///
    Iterator _iterator;

    import mir.functional: pipe;
    ///
    static alias __map(alias fun1) = SlideIterator__map!(Iterator, params, fun, pipe!(fun, fun1));

    auto ref opUnary(string op : "*")()
    {
        return mixin("fun(" ~ _iotaArgs!(params, "_iterator[", "], ") ~ ")");
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        return mixin("fun(" ~ _iotaArgs!(params, "_iterator[index + ", "], ") ~ ")");
    }

    mixin(std_ops);
}

///
version(mir_test) unittest
{
    import mir.functional: naryFun;
    auto data = [1, 3, 8, 18];
    auto diff = SlideIterator!(int*, 2, naryFun!"b - a")(data.ptr);
    assert(*diff == 2);
    assert(diff[1] == 5);
    assert(diff[2] == 10);
}

auto IndexIterator__map(Iterator, Field, alias fun)(ref IndexIterator!(Iterator, Field) it)
{
    import mir.ndslice.field: mapField;
    auto field = it._field.mapField!fun;
    return IndexIterator!(Iterator, typeof(field))(it._iterator, field);
}

version(mir_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto indices = [4, 3, 1, 2, 0, 4].sliced;
    auto v = iota(5).indexed(indices).map!(a => a).slice;
    uint r;
    auto w = iota(5).indexed(indices).map!(a => a).map!(a => a * r).slice;
}

/++
Iterates a field using an iterator.

`IndexIterator` is used by TODO.
+/
struct IndexIterator(Iterator, Field)
{
    import mir.functional: RefTuple, unref;

@optmath:
    ///
    Iterator _iterator;
    ///
    Field _field;

    ///
    static alias __map(alias fun) = IndexIterator__map!(Iterator, Field, fun);

    auto ref opUnary(string op : "*")()
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = *_iterator;
            return mixin("_field[" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ "]");
        }
        else
            return _field[*_iterator];
    }

    auto ref opIndex(ptrdiff_t index)
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = _iterator[index];
            return mixin("_field[" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ "]");
        }
        else
            return _field[_iterator[index]];
    }

    static if (!__traits(compiles, &opIndex(ptrdiff_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("_field[" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ "] = value");
            }
            else
                return _field[_iterator[index]] = value;
        }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin(op ~ "_field[" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ "]");
            }
            else
                return mixin(op ~ "_field[_iterator[index]]");
        }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("_field[" ~ _iotaArgs!(T.length, "t.expand[", "].unref, ") ~ "]" ~ op ~ "= value");
            }
            else
                return mixin("_field[_iterator[index]]" ~ op ~ "= value");
        }
    }

    mixin(std_ops);
}

/++
Iterates on top of another iterator and returns a slice
as a multidimensional window at the current position.

`SliceIterator` is used by $(SUBREF topology, map) for packed slices.
+/
struct SliceIterator(SliceKind kind, size_t[] packs, Iterator)
{
@optmath:
    ///
    alias Elem = Slice!(kind, packs, Iterator);
    ///
    size_t[Elem.N] _lengths;
    ///
    ptrdiff_t[Elem.S] _strides;
    ///
    Iterator _iterator;

    auto opUnary(string op : "*")()
    { return Elem(_lengths, _strides, _iterator); }

    auto opIndex()(ptrdiff_t index)
    { return Elem(_lengths, _strides, _iterator + index); }

    mixin(std_ops);
}

public auto FieldIterator__map(Field, alias fun)(ref FieldIterator!(Field) it)
{
    import mir.ndslice.field: mapField;
    auto field = it._field.mapField!fun;
    return FieldIterator!(typeof(field))(it._index, field);
}

version(mir_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = ndiota(3, 3).map!(a => a).slice;
    uint r;
    auto w = ndiota(3, 3).map!(a => a).map!(a => a[0] * r).slice;
}

/++
Creates an iterator on top of a field.

`FieldIterator` is used by $(SUBREF slice, slicedField), $(SUBREF topology, bitwise), $(SUBREF topology, ndiota), and others.
+/
struct FieldIterator(Field)
{
@optmath:
    ///
    ptrdiff_t _index;
    ///
    Field _field;

    ///
    static alias __map(alias fun) = FieldIterator__map!(Field, fun);

    ///
    _Slice!() opSlice(size_t dimension)(size_t i, size_t j) const
    {
        return typeof(return)(i, j);
    }

    /++
    Returns:
        `_field[_index + sl.i .. _index + sl.j]`.
    +/
    auto opIndex()(_Slice!() sl)
    {
        return _field[_index + sl.i .. _index + sl.j];
    }

    auto ref opUnary(string op : "*")()
    { return _field[_index]; }

    void opUnary(string op)()
        if (op == "++" || op == "--")
    { mixin(op ~ `_index;`); }

    auto ref opIndex()(ptrdiff_t index)
    { return _field[_index + index]; }

    static if (!__traits(compiles, &_field[_index]))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index)
        { return _field[_index + index] = value; }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        { mixin (`return ` ~ op ~ `_field[_index + index];`); }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        { mixin (`return _field[_index + index] ` ~ op ~ `= value;`); }
    }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    { mixin(`_index ` ~ op ~ `= index;`); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    { return this._index - right._index; }

    bool opEquals()(ref const typeof(this) right) const
    { return this._index == right._index; }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    { return this._index - right._index; }
}

auto FlattenedIterator__map(SliceKind kind, size_t[] packs, Iterator, alias fun)(ref FlattenedIterator!(kind, packs, Iterator) it)
{
    import mir.ndslice.topology: map;
    auto slice = it._slice.map!fun;
    return FlattenedIterator!(TemplateArgsOf!(typeof(slice)))(it._indexes, slice);
}

version(mir_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = iota(3, 3).universal.flattened.map!(a => a).slice;
    uint r;
    auto w = iota(3, 3).universal.flattened.map!(a => a).map!(a => a * r).slice;
}

/++
Creates an iterator on top of all elements in a slice.

`FieldIterator` is used by $(SUBREF topology, bitwise), $(SUBREF topology, ndiota), and others.
+/
struct FlattenedIterator(SliceKind kind, size_t[] packs, Iterator)
    if (packs[0] > 1 && (kind == Universal || kind == Canonical))
{
@optmath:
    ///
    ptrdiff_t[packs[0]] _indexes;
    ///
    Slice!(kind, packs, Iterator) _slice;

    ///
    static alias __map(alias fun) = FlattenedIterator__map!(kind, packs, Iterator, fun);

    private ptrdiff_t getShift()(ptrdiff_t n)
    {
        ptrdiff_t _shift;
        n += _indexes[$ - 1];
        foreach_reverse (i; Iota!(1, packs[0]))
        {
            immutable v = n / ptrdiff_t(_slice._lengths[i]);
            n %= ptrdiff_t(_slice._lengths[i]);
            static if (i == _slice.S)
                _shift += (n - _indexes[i]);
            else
                _shift += (n - _indexes[i]) * _slice._strides[i];
            n = _indexes[i - 1] + v;
        }
        _shift += (n - _indexes[0]) * _slice._strides[0];
        return _shift;
    }

    auto ref opUnary(string op : "*")()
    {
        static if (packs.length == 1)
        {
            return *_slice._iterator;
        }
        else
        {
            alias M = _slice.DeepElemType.N;
            return _slice.DeepElemType(_slice._lengths[$ - M .. $], _slice._strides[$ - M .. $], _slice._iterator);
        }
    }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    {
        foreach_reverse (i; Iota!(packs[0]))
        {
            static if (i == _slice.S)
                mixin(op ~ `_slice._iterator;`);
            else
                mixin(`_slice._iterator ` ~ op[0] ~ `= _slice._strides[i];`);
            mixin (op ~ `_indexes[i];`);
            static if (i)
            {
                static if (op == "++")
                {
                    if (_indexes[i] < _slice._lengths[i])
                        return;
                    static if (i == _slice.S)
                        _slice._iterator -= _slice._lengths[i];
                    else
                        _slice._iterator -= _slice._lengths[i] * _slice._strides[i];
                    _indexes[i] = 0;
                }
                else
                {
                    if (_indexes[i] >= 0)
                        return;
                    static if (i == _slice.S)
                        _slice._iterator += _slice._lengths[i];
                    else
                        _slice._iterator += _slice._lengths[i] * _slice._strides[i];
                    _indexes[i] = _slice._lengths[i] - 1;
                }
            }
        }
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        static if (packs.length == 1)
        {
            return _slice._iterator[getShift(index)];
        }
        else
        {
            alias M = _slice.DeepElemType.N;
            return _slice.DeepElemType(_slice._lengths[$ - M .. $], _slice._strides[$ - M .. $], _slice._iterator + getShift(index));
        }
    }

    static if (isMutable!(_slice.DeepElemType) && !_slice.hasAccessByRef)
    ///
    auto opIndexAssign(E)(auto ref E elem, size_t index)
    {
        static if (packs.length == 1)
        {
            return _slice._iterator[getShift(index)] = elem;
        }
        else
        {
            static assert(0,
                "flattened.opIndexAssign is not implemented for packed slices."
                ~ "Use additional empty slicing `flattenedSlice[index][] = value;`"
                ~ tailErrorMessage());
        }
    }

    void opOpAssign(string op : "+")(ptrdiff_t n)
    {
        ptrdiff_t _shift;
        n += _indexes[$ - 1];
        foreach_reverse (i; Iota!(1, packs[0]))
        {
            immutable v = n / ptrdiff_t(_slice._lengths[i]);
            n %= ptrdiff_t(_slice._lengths[i]);
            static if (i == _slice.S)
                _shift += (n - _indexes[i]);
            else
                _shift += (n - _indexes[i]) * _slice._strides[i];
            _indexes[i] = n;
            n = _indexes[i - 1] + v;
        }
        _shift += (n - _indexes[0]) * _slice._strides[0];
        _indexes[0] = n;
        foreach_reverse (i; Iota!(1, packs[0]))
        {
            if (_indexes[i] >= 0)
                break;
            _indexes[i] += _slice._lengths[i];
            _indexes[i - 1]--;
        }
        _slice._iterator += _shift;
    }

    void opOpAssign(string op : "-")(ptrdiff_t n)
    { this += -n; }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    {
        ptrdiff_t ret = this._indexes[0] - right._indexes[0];
        foreach (i; Iota!(1, packs[0]))
        {
            ret *= _slice._lengths[i];
            ret += this._indexes[i] - right._indexes[i];
        }
        return ret;
    }

    bool opEquals()(ref const typeof(this) right) const
    {
        foreach_reverse (i; Iota!(packs[0]))
            if (this._indexes[i] != right._indexes[i])
                return false;
        return true;
    }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    {
        foreach (i; Iota!(packs[0] - 1))
            if (auto ret = this._indexes[i] - right._indexes[i])
                return ret;
        return this._indexes[$ - 1] - right._indexes[$ - 1];
    }
}

version(mir_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.slice;

    auto it0 = iota(3, 4).universal.flattened._iterator;
    auto it1 = it0;
    assert(it0 == it1);
    it0 += 5;
    assert(it0 > it1);
    it0 -= 5;
    assert(*it0 == *it1);
    assert(it0 == it1);
    it0 += 5;
    it0 += 7;
    it0 -= 9;
    assert(it0 > it1);
    it1 += 3;
    assert(*it0 == *it1);
    assert(it0 == it1);
    assert(it0 <= it1);
    assert(it0 >= it1);

    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;

    assert(it0 - it1 == 9);
    assert(it1 - it0 == -9);

    ++it0;

    assert(it0 - it1 == 10);
    assert(it1 - it0 == -10);

    --it0;

    assert(it0 - it1 == 9);
    assert(it1 - it0 == -9);
    assert(it0[-9] == *it1);
    assert(*it0 == it1[9]);

    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    assert(*it0 == *it1);
    assert(it0 == it1);
    assert(it0 <= it1);
    assert(it0 >= it1);
}

/++
`StairsIterator` is used by $(SUBREF topology, stairs).
+/
struct StairsIterator(Iterator)
{
    ///
    size_t _length = 1;

    ///
    Iterator _iterator;

@optmath:

    ///
    Slice!(Contiguous, [1], Iterator) opUnary(string op : "*")()
    {
        import mir.ndslice.slice: sliced;
        return _iterator.sliced(_length);
    }

    ///
    Slice!(Contiguous, [1], Iterator) opIndex()(ptrdiff_t index)
    {
        import mir.ndslice.slice: sliced;
        auto newLength = _length + index;
        assert(ptrdiff_t(newLength) >= 0);
        auto shift = ptrdiff_t(_length + newLength - 1) * index / 2;
        return (_iterator + shift).sliced(newLength);
    }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    {
        static if (op == "++")
        {
            _iterator += _length;
            ++_length;
        }
        else
        {
            assert(_length);
            --_length;
            _iterator -= _length;
        }
    }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == "-" || op == "+")
    {
        auto newLength = mixin("_length " ~ op ~ " index");
        assert(ptrdiff_t(newLength) >= 0);
        auto shift = ptrdiff_t(_length + newLength - 1) * index / 2;
        _length = newLength;
        mixin("_iterator " ~ op ~ "= shift;");
    }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(auto ref const typeof(this) right) const
    { return this._length - right._length; }

    bool opEquals()(ref const typeof(this) right) const
    { return this._length == right._length; }

    ptrdiff_t opCmp()(ref const typeof(this) right) const
    { return this._length - right._length; }
}

///
version(mir_test) unittest
{
    // 0
    // 1 2
    // 3 4 5
    // 6 7 8 9
    // 10 11 12 13 14
    auto it = StairsIterator!(IotaIterator!size_t)(1, IotaIterator!size_t());
    assert(*it == [0]);
    assert(it[4] == [10, 11, 12, 13, 14]);
    assert(*(it + 4) == [10, 11, 12, 13, 14]);
    ++it;
    assert(*it == [1, 2]);
    it += 3;
    assert(*it == [10, 11, 12, 13, 14]);
    assert(it[-3] == [1, 2]);
    assert(*(it - 3) == [1, 2]);
    assert(it + 1 > it);
    assert(it + 1 - 1 == it);
    assert(it + 3 - it == 3);
    --it;
    assert(*it == [6, 7, 8, 9]);
}
