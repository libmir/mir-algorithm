
module mir.ndslice.iterator;

import mir.internal.utility;
import mir.ndslice.slice: SliceKind, Slice;
import std.traits;

private mixin template _opBinary()
{
    auto opBinary(string op, T)(const T index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }
}

///
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

    auto ref opUnary(string op : "*")()
    { return _value; }

    auto ref opUnary(string op)()
        if (op == `++` || op == `--`)
    { return this; }

    auto ref T opIndex(size_t)
    { return _value; }

    void opOpAssign(string op)(ptrdiff_t)
        if (op == `+` || op == `-`) {}

    RepeatIterator opBinary(string op)(ptrdiff_t)
    { return this; }
}

///
@safe pure nothrow @nogc unittest
{
    RepeatIterator!double val;
    val._value = 3;
    assert((++val)._value == 3);
    val += 2;
    assert((val + 3)._value == 3);
}

///
struct IotaIterator(I)
    if (isIntegral!I || isPointer!I)
{
    ///
    I _iterator;

    auto opUnary(string op : "*")()
    { return _iterator; }

    auto opUnary(string op)()
        if (op == "--" || op == "++")
    { return mixin(op ~ `_iterator`); }

    auto opIndex(size_t index)
    { return cast(I)(_iterator + index); }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == `+` || op == `-`) { mixin(`_iterator ` ~ op ~ `= index;`); }

    mixin _opBinary;
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
    assert(*iterator == 0);

    // opBinary
    assert(*(iterator + 2) == 2);
    assert(*(iterator - 3) == -3);

    // construction
    assert(*IotaIterator!int(3) == 3);
}

///
struct FieldIterator(Field)
{
    ///
    size_t _iterator;
    ///
    Field _field;

    auto ref opUnary(string op : "*")()
    { return _field[_iterator]; }

    auto ref opUnary(string op)()
        if (op == "++" || op == "--")
    { return mixin(op ~ `_iterator`); }

    auto ref opIndex(size_t index)
    { return _field[_iterator + index]; }

    static if (!__traits(compiles, &_field[_iterator]) && isMutable!(typeof(_field[_iterator])))
    auto opIndexAssign(T)(T value, size_t index)
    { return _field[_iterator + index] = value; }

    void opOpAssign(string op, T)(const T index)
        if (op == "+" || op == "-")
    { mixin(`_iterator ` ~ op ~ `= index;`); }

    mixin _opBinary;
}

auto fieldIterator(Field)(Field field)
{
    return FieldIterator!Field(0, field);
}

struct FlattenedIterator(SliceKind kind, size_t[] packs, Iterator)
    if (packs[0] > 1 && (kind == SliceKind.universal || kind == SliceKind.canonical))
{
    ///
    ptrdiff_t[packs[0]] _indexes;
    ///
    Slice!(kind, packs, Iterator) _slice;

    private ptrdiff_t getShift(size_t n)
    {
        ptrdiff_t _shift;
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

    void opOpAssign(string op : "+")(size_t n)
    {
        ptrdiff_t _shift;
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

    mixin _opBinary;
}
