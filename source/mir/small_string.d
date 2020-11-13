/++
$(H1 Small String)

The module contains self-contained generic small string implementaton.

$(LREF SmallString) supports ASDF - Json Serialisation Library.

See also `include/mir/small_series.h` for a C++ version of this type.
Both C++ and D implementations have the same ABI and name mangling.

Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilya Yaroshenko
+/
module mir.small_string;

import mir.serde: serdeScoped, serdeProxy;

private extern (C) @system nothrow @nogc pure size_t strnlen_s(scope const char* s, size_t n);

private static immutable errorMsg = "Cannot create SmallString: input string exceeds maximum allowed length.";
version(D_Exceptions)
    private static immutable exception = new Exception(errorMsg);

extern(C++, "mir"):

/++
Self-contained generic Small String implementaton.
+/
@serdeScoped @serdeProxy!(const(char)[])
struct SmallString(uint maxLength)
    if (maxLength)
{

    import core.stdc.string: memcmp, memcpy, strlen;
    import std.traits: Unqual, isIterable;

    // maxLength bytes
    char[maxLength] _data = '\0';

extern(D) @safe pure @nogc:

    /// Constructor
    this(typeof(null))
    {
    }

    /// ditto
    this(scope const(char)[] str)
    {
        this.opAssign(str);
    }

    /// ditto
    this(uint n)(auto ref scope const SmallString!n str)
    {
        this.opAssign(str);
    }

    /// ditto
    this(Range)(auto ref Range str)
        if (isIterable!Range)
    {
        size_t i = 0;
        foreach(char c; str)
        {
            if (i > _data.length)
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data[i++] = c;
        }
    }

    /// `=` operator
    ref typeof(this) opAssign(typeof(null)) return
    {
        _data = '\0';
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(scope const(char)[] str) return @trusted
    {
        if (str.length > _data.sizeof)
        {
            version(D_Exceptions) throw exception;
            else assert(0, errorMsg);
        }
        if (__ctfe)
            _data[0 .. str.length] =  str;
        else
            memcpy(_data.ptr, str.ptr, str.length);
        _data[str.length .. $] = '\0';
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(uint n)(auto ref scope const SmallString!n rhs) return
        if (n != maxLength)
    {
        static if (n < maxLength)
        {
            version (LDC)
                cast(char[n])(_data[0 .. n]) = rhs._data;
            else
                _data[0 .. n] = rhs._data;
            _data[n .. maxLength] = '\0';
        }
        else
        {
            if (rhs._data[maxLength])
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data = cast(char[maxLength])(rhs._data[0 .. maxLength]);
        }
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(uint n)(const SmallString!n rhs) return
        if (n != maxLength)
    {
        static if (n < maxLength)
        {
            version (LDC)
                cast(char[n])(_data[0 .. n]) = rhs._data;
            else
                _data[0 .. n] = rhs._data;
            _data[n .. maxLength] = '\0';
        }
        else
        {
            if (rhs._data[maxLength])
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data = cast(char[maxLength])(rhs._data[0 .. maxLength]);
        }
        return this;
    }

    /// ditto
    void trustedAssign(scope const(char)[] str) return @trusted nothrow
    {
        _data = '\0';
        if (__ctfe)
            _data[0 .. str.length] =  str;
        else
            memcpy(_data.ptr, str.ptr, str.length);
    }

    ///
    ref typeof(this) append(char c) @trusted
    {
        auto length = opIndex.length;
        if (length == maxLength)
        {
            version(D_Exceptions) throw exception;
            else assert(0, errorMsg);
        }
        _data[length] = c;
        return this;
    }

    ///
    ref typeof(this) append(scope const(char)[] str) @trusted
    {
        auto length = opIndex.length;
        if (length + str.length > maxLength)
        {
            version(D_Exceptions) throw exception;
            else assert(0, errorMsg);
        }
        if (__ctfe)
            _data[length .. str.length + length] = str;
        else
            memcpy(_data.ptr + length, str.ptr, str.length);
        return this;
    }

    /// ditto
    alias put = append;

    /// ditto
    alias opOpAssign(string op : "~") = append;

    ///
    SmallString concat(scope const(char)[] str) scope const
    {
        SmallString c = this;
        c.append(str);
        return c; 
    }

    /// ditto
    alias opBinary(string op : "~") = concat;


scope nothrow:

    /++
    Returns an scope common string.

    The property is used as common string representation self alias.

    The alias helps with `[]`, `[i]`, `[i .. j]`, `==`, and `!=` operations and implicit conversion to strings.
    +/
    inout(char)[] opIndex() inout @trusted scope return
    {
        size_t i;
        if (__ctfe)
            while (i < maxLength && _data[i]) i++;
        else
            i = _data[$ - 1] ? _data.length : strlen(_data.ptr);
        return _data[0 .. i];
    }

    ///
    ref inout(char) opIndex(size_t index) inout scope return
    {
        return opIndex[index];
    }

const:

    ///
    bool empty() @property
    {
        return _data[0] == 0;
    }

    ///
    size_t length() @property
    {
        return opIndex.length;
    }

    ///
    alias toString = opIndex;

    /// Hash implementation
    size_t toHash()
    {
        return hashOf(opIndex);
    }

    /// Comparisons operator overloads
    bool opEquals(uint rhsMaxLength)(auto ref scope const SmallString!rhsMaxLength rhs) scope
    {
        return opIndex == rhs.opIndex;
    }

    /// ditto
    bool opEquals()(scope const(char)[] str) scope
    {
        return opIndex == str;
    }

    /// Comparisons operator overloads
    int opCmp(uint rhsMaxLength)(auto ref scope const SmallString!rhsMaxLength rhs) scope
    {
        return __cmp(opIndex, rhs.opIndex);
    }

    /// ditto
    int opCmp()(scope const(char)[] str) scope
    {
        return __cmp(opIndex, str);
    }
}

///
@safe pure @nogc version(mir_test) unittest
{
    SmallString!16 s16;
    assert(s16.empty);

    auto s8 = SmallString!8("Hellow!!");
    assert(s8 == "Hellow!!", s8[]);

    s16 = s8;
    assert(s16 == "Hellow!!", s16[]);
    s16[7] = '@';
    s8 = null;
    assert(s8.empty);
    s8 = s16;
    assert(s8 == "Hellow!@");

    auto s8_2 = s8;
    assert(s8_2 == "Hellow!@");
    assert(s8_2 == s8);

    assert(s8 < "Hey");
    assert(s8 > "Hellow!");

    assert(s8.opCmp("Hey") < 0);
    assert(s8.opCmp(s8) == 0);
}

/// Concatenation
@safe pure @nogc version(mir_test) unittest
{
    auto a = SmallString!16("asdf");
    a ~= " ";
    auto b = a ~ "qwerty";
    static assert(is(typeof(b) == SmallString!16));
    assert(b == "asdf qwerty");
    b.put('!');
    b.put("!");
    assert(b == "asdf qwerty!!");
}

@safe pure @nogc nothrow version(mir_test) unittest
{
    import mir.conv: emplaceRef;
    SmallString!32 a, b;
    emplaceRef!(const SmallString!32)(a, cast(const)b);
}
