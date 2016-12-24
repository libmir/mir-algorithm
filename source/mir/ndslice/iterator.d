
module mir.ndslice.iterator;

import mir.internal.utility;
import mir.ndslice.slice: SliceKind, Slice;
import std.traits;

struct RepeatIterator(T)
{
    // UT definition is from std.range
    // Store a non-qualified T when possible: This is to make RepeatIterator assignable
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


    ///
    ref T opIndex(sizediff_t)
    {
        return _value;
    }

    ///
    RepeatIterator opBinary(string op)(size_t index) const @safe pure nothrow @nogc @property
    {
        RepeatIterator ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ///
    void opOpAssign(string op)(sizediff_t)
        if (op == `+` || op == `-`)
    {
    }

    ///
    ref opUnary(string op : "*")()
    {
        return _value;
    }

    ///
    auto ref opUnary(string op)()
        if (op == `++` || op == `--`)
    {
        return this;
    }
}

@safe pure nothrow @nogc unittest
{
    RepeatIterator!double val;
    val._value = 3;
    assert((++val)._value == 3);
    val += 2;
    assert((val + 3)._value == 3);
}

struct IotaIterator(I)
    if (isIntegral!I || isPointer!I)
{
    ///
    I iterator;
    ///
    alias iterator this;

    ///
    I opIndex(size_t index) @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return cast(I)(iterator + index);
    }

    ///
    IotaIterator opBinary(string op)(size_t index) const @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        IotaIterator ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ///
    I opUnary(string op : "*")() const @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return iterator;
    }

    ///
    auto opUnary(string op)() @safe pure nothrow @nogc @property
        if (op == "--" || op == "++")
    {
        pragma(inline, true);
        return mixin(op ~ `iterator`);
    }
}

///
@safe pure nothrow @nogc unittest
{
    IotaIterator!int iterator;
    assert(*iterator == 0);

    // iteration
    iterator++;
    assert(*iterator == 1);
    assert(iterator[2] == 3);
    iterator--;
    assert(iterator == 0);

    // opBinary
    assert(*(iterator + 2) == 2);
    assert(*(iterator - 3) == -3);

    // construction
    assert(IotaIterator!int(3) == 3);
}

struct ShellIterator(Field)
{
    ///
    size_t iterator;
    ///
    alias iterator this;
    ///
    Field field;

    ///
    auto ref opIndex(size_t index)
    {
        return field[iterator + index];
    }

    static if (!__traits(compiles, &field[iterator]) && isMutable!(typeof(field[iterator])))
    ///
    auto opIndexAssign(T)(T value, size_t index)
    {
        return field[iterator + index] = value;
    }

    static if (__traits(compiles, Field.init[size_t.init] |= I.init))
    ///
    ShellIterator opBinary(string op)(size_t index) const @safe pure nothrow @nogc @property
    {
        ShellIterator ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ///
    auto ref opUnary(string op : "*")()
    {
        return field[iterator];
    }

    ///
    auto opUnary(string op)() @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return mixin(op ~ `iterator`);
    }
}

auto shellIterator(Field)(Field field)
{
    return ShellIterator!Field(0, field);
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
    short[10] data;
    auto f = data.ptr.bitField.shellIterator;
    f[123] = true;
    f++;
    assert(f[122]);
}


struct FlattenedIterator(SliceKind kind, size_t[] packs, Iterator)
    if (packs[0] > 1 && (kind == SliceKind.universal || kind == SliceKind.canonical))
{
    ///
    Slice!(kind, packs, Iterator) _slice;
    ///
    ptrdiff_t[packs[0]] _indexes;


    private sizediff_t getShift(size_t n)
    {
        sizediff_t _shift;
        n += _indexes[$ - 1];
        with (_slice) foreach_reverse (i; Iota!(1, packs[0]))
        {
            immutable v = n / _lengths[i];
            n %= _lengths[i];
            static if (i == _slice.S)
                _shift += (n - _indexes[i]);
            else
                _shift += (n - _indexes[i]) * _strides[i];
            n = _indexes[i - 1] + v;
        }
        debug (ndslice) assert(n < _slice._lengths[0]);
        with (_slice)
            _shift += (n - _indexes[0]) * _strides[0];
        return _shift;
    }

    ///
    auto ref opIndex(size_t index)
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

    //static if (PureN == 1 && isMutable!DeepElemType && !hasAccessByRef)
    /////
    //auto opIndexAssign(E)(E elem, size_t index)
    //{
    //    static if (N == PureN)
    //    {
    //        return _slice._iterator[getShift(index)] = elem;
    //    }
    //    else
    //    {
    //        static assert(0,
    //            "ByElement.opIndexAssign is not implemented for packed slices."
    //            ~ "Use additional empty slicing `elemsOfSlice[index][] = value`"
    //            ~ tailErrorMessage());
    //    }
    //}

    ///
    FlattenedIterator opBinary(string op)(size_t index) const
    {
        pragma(inline, true);
        FlattenedIterator ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ///
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
            static if (op == "++")
            {
                if (_indexes[i] < _lengths[i])
                    return;
                //debug (ndslice) assert(_indexes[i] == _lengths[i]);
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

    void opOpAssign(string op : "+")(size_t n)
    {
        sizediff_t _shift;
        n += _indexes[$ - 1];
        with (_slice) foreach_reverse (i; Iota!(1, packs[0]))
        {
            immutable v = n / _lengths[i];
            n %= _lengths[i];
            static if (i == _slice.S)
                _shift += (n - _indexes[i]);
            else
                _shift += (n - _indexes[i]) * _strides[i];
            _indexes[i] = n;
            n = _indexes[i - 1] + v;
        }
        assert(n <= _slice._lengths[0]);
        with (_slice)
        {
            _shift += (n - _indexes[0]) * _strides[0];
            _indexes[0] = n;
        }
        _slice._iterator += _shift;
    }

    void opOpAssign(string op : "-")(size_t n)
    {
        this += this.elementsCount - n;
    }
}
