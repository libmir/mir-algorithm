
module mir.ndslice.cursor;

import mir.internal.utility;
import mir.ndslice.slice: SliceKind, Slice;
import std.traits;

struct RepeatCursor(T)
{
    // UT definition is from std.range
    // Store a non-qualified T when possible: This is to make RepeatCursor assignable
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
    RepeatCursor opBinary(string op)(size_t index) const @safe pure nothrow @nogc @property
    {
        RepeatCursor ret = this;
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
    RepeatCursor!double val;
    val._value = 3;
    assert((++val)._value == 3);
    val += 2;
    assert((val + 3)._value == 3);
}

struct IotaCursor(I)
    if (isIntegral!I || isPointer!I)
{
    ///
    I cursor;
    ///
    alias cursor this;

    ///
    I opIndex(size_t index) @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return cast(I)(cursor + index);
    }

    ///
    IotaCursor opBinary(string op)(size_t index) const @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        IotaCursor ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ///
    I opUnary(string op : "*")() const @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return cursor;
    }

    ///
    auto opUnary(string op)() @safe pure nothrow @nogc @property
        if (op == "--" || op == "++")
    {
        pragma(inline, true);
        return mixin(op ~ `cursor`);
    }
}

///
@safe pure nothrow @nogc unittest
{
    IotaCursor!int cursor;
    assert(*cursor == 0);

    // iteration
    cursor++;
    assert(*cursor == 1);
    assert(cursor[2] == 3);
    cursor--;
    assert(cursor == 0);

    // opBinary
    assert(*(cursor + 2) == 2);
    assert(*(cursor - 3) == -3);

    // construction
    assert(IotaCursor!int(3) == 3);
}

struct ShellCursor(Field)
{
    ///
    size_t cursor;
    ///
    alias cursor this;
    ///
    Field field;

    ///
    auto ref opIndex(size_t index)
    {
        return field[cursor + index];
    }

    static if (!__traits(compiles, &field[cursor]) && isMutable!(typeof(field[cursor])))
    ///
    auto opIndexAssign(T)(T value, size_t index)
    {
        return field[cursor + index] = value;
    }

    static if (__traits(compiles, Field.init[size_t.init] |= I.init))
    ///
    ShellCursor opBinary(string op)(size_t index) const @safe pure nothrow @nogc @property
    {
        ShellCursor ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ///
    auto ref opUnary(string op : "*")()
    {
        return field[cursor];
    }

    ///
    auto opUnary(string op)() @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return mixin(op ~ `cursor`);
    }
}

auto shellCursor(Field)(Field field)
{
    return ShellCursor!Field(0, field);
}

/++
Cursor composed of indexes.
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
    auto f = data.ptr.bitField.shellCursor;
    f[123] = true;
    f++;
    assert(f[122]);
}


struct FlattenedCursor(SliceKind kind, size_t[] packs, Cursor)
    if (packs[0] > 1 && (kind == SliceKind.universal || kind == SliceKind.canonical))
{
    ///
    Slice!(kind, packs, Cursor) _slice;
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
            return _slice._cursor[getShift(index)];
        }
        else with (_slice)
        {
            alias M = DeepElemType.N;
            return DeepElemType(_lengths[$ - M .. $], _strides[$ - M .. $], _cursor + getShift(index));
        }
    }

    //static if (PureN == 1 && isMutable!DeepElemType && !hasAccessByRef)
    /////
    //auto opIndexAssign(E)(E elem, size_t index)
    //{
    //    static if (N == PureN)
    //    {
    //        return _slice._cursor[getShift(index)] = elem;
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
    FlattenedCursor opBinary(string op)(size_t index) const
    {
        pragma(inline, true);
        FlattenedCursor ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ///
    auto ref opUnary(string op : "*")()
    {
        static if (packs.length == 1)
        {
            return *_slice._cursor;
        }
        else with (_slice)
        {
            alias M = DeepElemType.N;
            return DeepElemType(_lengths[$ - M .. $], _strides[$ - M .. $], _cursor);
        }
    }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    {
        with(_slice) foreach_reverse (i; Iota!(packs[0]))
        {
            static if (i == _slice.S)
                mixin(op ~ `_cursor;`);
            else
                mixin(`_cursor ` ~ op[0] ~ `= _strides[i];`);
            mixin (op ~ `_indexes[i];`);
            static if (op == "++")
            {
                if (_indexes[i] < _lengths[i])
                    return;
                //debug (ndslice) assert(_indexes[i] == _lengths[i]);
                static if (i == _slice.S)
                    _cursor -= _lengths[i];
                else
                    _cursor -= _lengths[i] * _strides[i];
                _indexes[i] = 0;
            }
            else
            {
                if (_indexes[i] >= 0)
                    return;
                static if (i == _slice.S)
                    _cursor += _lengths[i];
                else
                    _cursor += _lengths[i] * _strides[i];
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
        _slice._cursor += _shift;
    }

    void opOpAssign(string op : "-")(size_t n)
    {
        this += this.elementsCount - n;
    }
}
