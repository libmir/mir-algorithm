
module mir.ndslice.cursor;

import mir.internal.utility;
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
    I opUnary(string op : "*")() @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return cursor;
    }

    ///
    auto opUnary(string op)() @safe pure nothrow @nogc @property
    {
        pragma(inline, true);
        return mixin(op ~ `cursor`);
    }
}

///
@safe pure nothrow @nogc unittest
{
    IotaCursor!int cursor;
    assert(cursor == 0);

    // iteration
    cursor++;
    assert(cursor == 1);
    assert(cursor[2] == 3);
    assert(cursor[-2] == -1);
    cursor--;
    assert(cursor == 0);

    // opBinary
    assert(cursor + 2 == 2);
    assert(cursor - 3 == -3);

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
    auto ref opIndex(size_t index) @safe pure nothrow @nogc @property
    {
        return field[cursor + index];
    }

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

struct BitCursor(T)
{
	
}
