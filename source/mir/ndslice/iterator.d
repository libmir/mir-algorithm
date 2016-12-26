
module mir.ndslice.iterator;

import mir.internal.utility;
import mir.ndslice.slice: SliceKind, Slice;
import std.traits;

/++
+/
struct IotaIterator(I)
    if (isIntegral!I || isPointer!I)
{
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
+/
struct RetroIterator(Iterator)
{
    ///
    Iterator _iterator;

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

    bool opEquals()(auto ref const typeof(this) right) const
    { return right._iterator == this._iterator; }

    ptrdiff_t opCmp()(auto ref const typeof(this) right) const
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
+/
struct StrideIterator(Iterator)
{
    ///
    ptrdiff_t _stride;
    ///
    Iterator _iterator;

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
    { return _stride ? (this._iterator - right._iterator) / _stride : _stride; }

    bool opEquals()(auto ref const typeof(this) right) const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(auto ref const typeof(this) right) const
    {
        static if (isPointer!Iterator)
            ptrdiff_t ret = this._iterator - right._iterator;
        else
            ptrdiff_t ret = this._iterator.opCmp(right._iterator);
        return _stride ? _stride > 0 ? ret : -ret : _stride;
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

/++
+/
struct FieldIterator(Field)
{
    ///
    ptrdiff_t _index;
    ///
    Field _field;

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

    ptrdiff_t opBinary()(auto ref const typeof(this) right) const
    { return this._index - right._index; }

    bool opEquals()(auto ref const typeof(this) right) const
    { return this._index == right._index; }

    ptrdiff_t opCmp()(auto ref const typeof(this) right) const
    { return this._index - right._index; }
}

/++
+/
struct FlattenedIterator(SliceKind kind, size_t[] packs, Iterator)
    if (packs[0] > 1 && (kind == SliceKind.universal || kind == SliceKind.canonical))
{
    ///
    ptrdiff_t[packs[0]] _indexes;
    ///
    Slice!(kind, packs, Iterator) _slice;

    private ptrdiff_t getShift()(ptrdiff_t n)
    {
        ptrdiff_t _shift;
        n += _indexes[$ - 1];
        with (_slice) foreach_reverse (i; Iota!(1, packs[0]))
        {
            immutable v = n / ptrdiff_t(_lengths[i]);
            n %= ptrdiff_t(_lengths[i]);
            static if (i == _slice.S)
                _shift += (n - _indexes[i]);
            else
                _shift += (n - _indexes[i]) * _strides[i];
            n = _indexes[i - 1] + v;
        }
        with (_slice)
            _shift += (n - _indexes[0]) * _strides[0];
        return _shift;
    }

    auto ref opUnary(string op : "*")()
    {
        static if (packs.length == 1)
        {
            return *_slice._iterator;
        }
        else with (_slice)
        {
            alias M = DeepElemType.N;
            return DeepElemType(_lengths[$ - M .. $], _strides[$ - M .. $], _iterator);
        }
    }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    {
        with(_slice) foreach_reverse (i; Iota!(packs[0]))
        {
            static if (i == _slice.S)
                mixin(op ~ `_iterator;`);
            else
                mixin(`_iterator ` ~ op[0] ~ `= _strides[i];`);
            mixin (op ~ `_indexes[i];`);
            static if (i)
            {
                static if (op == "++")
                {
                    if (_indexes[i] < _lengths[i])
                        return;
                    static if (i == _slice.S)
                        _iterator -= _lengths[i];
                    else
                        _iterator -= _lengths[i] * _strides[i];
                    _indexes[i] = 0;
                }
                else
                {
                    if (_indexes[i] >= 0)
                        return;
                    static if (i == _slice.S)
                        _iterator += _lengths[i];
                    else
                        _iterator += _lengths[i] * _strides[i];
                    _indexes[i] = _lengths[i] - 1;
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
        else with (_slice)
        {
            alias M = DeepElemType.N;
            return DeepElemType(_lengths[$ - M .. $], _strides[$ - M .. $], _iterator + getShift(index));
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
        with (_slice)
        {
            n += _indexes[$ - 1];
            foreach_reverse (i; Iota!(1, packs[0]))
            {
                immutable v = n / ptrdiff_t(_lengths[i]);
                n %= ptrdiff_t(_lengths[i]);
                static if (i == _slice.S)
                    _shift += (n - _indexes[i]);
                else
                    _shift += (n - _indexes[i]) * _strides[i];
                _indexes[i] = n;
                n = _indexes[i - 1] + v;
            }
            _shift += (n - _indexes[0]) * _strides[0];
            _indexes[0] = n;
            foreach_reverse (i; Iota!(1, packs[0]))
            {
                if (_indexes[i] >= 0)
                    break;
                _indexes[i] += _lengths[i];
                _indexes[i - 1]--;
            }
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

    bool opEquals()(auto ref const typeof(this) right) const
    {
        foreach_reverse (i; Iota!(packs[0]))
            if (this._indexes[i] != right._indexes[i])
                return false;
        return true;
    }

    ptrdiff_t opCmp()(auto ref const typeof(this) right) const
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
