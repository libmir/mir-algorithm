/++
This is a submodule of $(MREF mir,ndslice).

Iterator is a type with a pointer like behavior.
An ndslice can be created on top of a field using $(REF sliced, mir,ndslice,slice).

$(BOOKTABLE $(H2 Iterators),
$(TR $(TH Iterator Name) $(TH Used By))
$(T2 IotaIterator, $(REF iota, mir,ndslice,topology))
$(T2 RetroIterator, $(REF retro, mir,ndslice,topology))
$(T2 StrideIterator, $(REF stride, mir,ndslice,topology))
$(T2 ZipIterator, $(REF zip, mir,ndslice,topology))
$(T2 MapIterator, $(REF map, mir,ndslice,topology))
$(T2 IndexIterator, TODO)
$(T2 SliceIterator, $(REF map, mir,ndslice,topology) in composition with $(LREF MapIterator) for packed slices.)
$(T2 FieldIterator, $(REF bitwise, mir,ndslice,topology), $(REF ndiota, mir,ndslice,topology), and others.)
$(T2 FlattenedIterator, $(REF flattened, mir,ndslice,topology))
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
import mir.internal.utility;
import mir.ndslice.slice: SliceKind, Slice;
import mir.ndslice.internal;

@fastmath:

/++
Step counter.

`IotaIterator` is used by $(REF iota, mir,ndslice,topology).
+/
struct IotaIterator(I)
    if (isIntegral!I || isPointer!I)
{
@fastmath:
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
@safe pure nothrow @nogc unittest
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
pure nothrow @nogc unittest
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

/++
Reverse directions for an iterator.

`RetroIterator` is used by $(REF retro, mir,ndslice,topology).
+/
struct RetroIterator(Iterator)
{
@fastmath:
    ///
    Iterator _iterator;

    ///
    static auto __map(alias fun)(ref typeof(this) it)
    {
        auto iterator = it._iterator.mapIterator!fun;
        return RetroIterator!(typeof(iterator))(iterator);
    }

    auto ref opUnary(string op : "*")()
    { return *_iterator; }

    void opUnary(string op : "--")()
    { ++_iterator; }

    void opUnary(string op : "++")()
    { --_iterator; }

    auto ref opIndex()(ptrdiff_t index)
    { return _iterator[-index]; }

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

    bool opEquals(ref const typeof(this) right) const
    { return right._iterator == this._iterator; }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            return right._iterator - this._iterator;
        else
            return right._iterator.opCmp(this._iterator);
    }
}

///
@safe pure nothrow @nogc unittest
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

/++
Iterates an iterator with a fixed strides.

`StrideIterator` is used by $(REF stride, mir,ndslice,topology).
+/
struct StrideIterator(Iterator)
{
@fastmath:
    ///
    ptrdiff_t _stride;
    ///
    Iterator _iterator;

    ///
    static auto __map(alias fun)(ref typeof(this) it)
    {
        auto iterator = it._iterator.mapIterator!fun;
        return StrideIterator!(typeof(iterator))(it._stride, iterator);
    }

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

    bool opEquals(ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            ptrdiff_t ret = this._iterator - right._iterator;
        else
            ptrdiff_t ret = this._iterator.opCmp(right._iterator);
        return _stride >= 0 ? ret : -ret;
    }
}

///
@safe pure nothrow @nogc unittest
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

`ZipIterator` is used by $(REF zip, mir,ndslice,topology).
+/
struct ZipIterator(Iterators...)
    if (Iterators.length > 1)
{
@fastmath:
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

    auto ref opIndex()(ptrdiff_t index)
    { return mixin("RefTuple!(_zip_types!Iterators)(" ~ _zip_index!Iterators ~ ")"); }

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

    bool opEquals(ref const typeof(this) right) const
    { return this._iterators[0] == right._iterators[0]; }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    {
        static if (isPointer!(Iterators[0]))
            return this._iterators[0] - right._iterators[0];
        else
            return this._iterators[0].opCmp(right._iterators[0]);
    }
}

///
pure nothrow @nogc unittest
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

/++
`MapIterator` is used by $(REF map, mir,ndslice,topology).
+/
struct MapIterator(Iterator, alias fun)
{
@fastmath:
    ///
    Iterator _iterator;

    ///
    static auto __map(alias fun1)(ref typeof(this) it)
    {
        import mir.functional: pipe;
        return MapIterator!(Iterator, pipe!(fun, fun1))(it._iterator);
    }

    auto ref opUnary(string op : "*")()
    {
        static if (is(Iterator : ZipIterator!(Iterators), Iterators...))
            return mixin("fun(" ~ _iotaArgs!(Iterators.length, "*_iterator._iterators[", "], ") ~ ")");
        else
            return fun(*_iterator);
    }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin(op ~ "_iterator;"); }

    auto ref opIndex()(ptrdiff_t index)
    {
        static if (is(Iterator : ZipIterator!(Iterators), Iterators...))
            return mixin("fun(" ~ _iotaArgs!(Iterators.length, "_iterator._iterators[", "][index], ") ~ ")");
        else
            return fun(_iterator[index]);
    }

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

    bool opEquals(ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
}

/++
Creates a mapped iterator. Uses `__map` if possible.
+/
auto mapIterator(alias fun, Iterator)(Iterator iterator)
{
    static if (__traits(hasMember, Iterator, "__map"))
        return Iterator.__map!fun(iterator);
    else
       return MapIterator!(Iterator, fun)(iterator);
}

/++
Iterates a field using an iterator.

`IndexIterator` is used by TODO.
+/
struct IndexIterator(Iterator, Field)
{
@fastmath:
    ///
    Iterator _iterator;
    ///
    Field _field;

    ///
    static auto __map(alias fun)(ref typeof(this) it)
    {
        import mir.ndslice.field: mapField;
        auto field = it._field.mapField!fun;
        return IndexIterator!(Iterator, typeof(field))(it._iterator, field);
    }

    auto ref opUnary(string op : "*")()
    { return _field[*_iterator]; }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin(op ~ "_iterator;"); }

    auto ref opIndex()(ptrdiff_t index)
    { return _field[_iterator[index]]; }

    static if (!__traits(compiles, &_field[_iterator[ptrdiff_t.init]]))
    void opIndexAssign(T)(T value, ptrdiff_t index)
    { return _field[_iterator[index]] = value; }

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

    bool opEquals(ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
}

/++
Iterates on top of another iterator and returns a slice
as a multidimensional window at the current position.

`SliceIterator` is used by $(REF map, mir,ndslice,topology) for packed slices.
+/
struct SliceIterator(SliceKind kind, size_t[] packs, Iterator)
{
@fastmath:
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

    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin(op ~ "_iterator;"); }

    auto opIndex()(ptrdiff_t index)
    { return Elem(_lengths, _strides, _iterator + index); }

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

    bool opEquals(ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
}

/++
Creates an iterator on top of a field.

`FieldIterator` is used by $(REF bitwise, mir,ndslice,topology), $(REF ndiota, mir,ndslice,topology), and others.
+/
struct FieldIterator(Field)
{
@fastmath:
    ///
    ptrdiff_t _index;
    ///
    Field _field;

    ///
    static auto __map(alias fun)(ref typeof(this) it)
    {
        import mir.ndslice.field: mapField;
        auto field = it._field.mapField!fun;
        return FieldIterator!(typeof(field))(it._index, field);
    }

    auto ref opUnary(string op : "*")()
    { return _field[_index]; }

    void opUnary(string op)()
        if (op == "++" || op == "--")
    { mixin(op ~ `_index;`); }

    auto ref opIndex()(ptrdiff_t index)
    { return _field[_index + index]; }

    static if (!__traits(compiles, &_field[_index]) && isMutable!(typeof(_field[_index])))
    auto opIndexAssign(T)(T value, ptrdiff_t index)
    { return _field[_index + index] = value; }

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

    bool opEquals(ref const typeof(this) right) const
    { return this._index == right._index; }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    { return this._index - right._index; }
}

/++
Creates an iterator on top of all elements in a slice.

`FieldIterator` is used by $(REF bitwise, mir,ndslice,topology), $(REF ndiota, mir,ndslice,topology), and others.
+/
struct FlattenedIterator(SliceKind kind, size_t[] packs, Iterator)
    if (packs[0] > 1 && (kind == SliceKind.universal || kind == SliceKind.canonical))
{
@fastmath:
    ///
    ptrdiff_t[packs[0]] _indexes;
    ///
    Slice!(kind, packs, Iterator) _slice;

    ///
    static auto __map(alias fun)(ref typeof(this) it)
    {
        import mir.ndslice.topology: map;
        auto slice = _slice.map!fun;
        return FlattenedIterator!(TemplateArgsOf!(typeof(slice)))(_indexes, slice);
    }

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
    auto opIndexAssign(E)(E elem, size_t index)
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

    bool opEquals(ref const typeof(this) right) const
    {
        foreach_reverse (i; Iota!(packs[0]))
            if (this._indexes[i] != right._indexes[i])
                return false;
        return true;
    }

    ptrdiff_t opCmp(ref const typeof(this) right) const
    {
        foreach (i; Iota!(packs[0] - 1))
            if (auto ret = this._indexes[i] - right._indexes[i])
                return ret;
        return this._indexes[$ - 1] - right._indexes[$ - 1];
    }
}

unittest
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
