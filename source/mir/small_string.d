/++
$(H1 Small String)

The module contains self-contained generic small string implementaton.

$(LREF SmallString) supports ASDF - Json Serialisation Library.

See also `include/mir/small_series.h` for a C++ version of this type.
Both C++ and D implementations have the same ABI and name mangling.

Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki
+/
module mir.small_string;

import mir.serde: serdeScoped, serdeProxy;

private static immutable errorMsg = "Cannot create SmallString: input string exceeds maximum allowed length.";
version(D_Exceptions)
    private static immutable exception = new Exception(errorMsg);

/++
Self-contained generic Small String implementaton.
+/
extern(C++, "mir")
@serdeScoped @serdeProxy!(const(char)[])
struct SmallString(uint maxLength)
    if (maxLength)
{

    import core.stdc.string: memcmp, memcpy;
    import std.traits: Unqual, isIterable;

    // maxLength bytes
    char[maxLength] _data = '\0';

extern(D) @safe pure @nogc:

    /// Constructor
    this(typeof(null)) scope
    {
    }

    /// ditto
    this(scope const(char)[] str) scope
    {
        this.opAssign(str);
    }

    /// ditto
    this(uint n)(auto ref scope const SmallString!n str) scope
    {
        this.opAssign(str);
    }

    /// ditto
    this(Range)(auto ref scope Range str) scope
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
    ref typeof(this) opAssign(typeof(null)) scope return
    {
        _data = '\0';
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(scope const(char)[] str) scope return @trusted
    {
        _data = '\0';
        if (str.length > _data.sizeof)
        {
            version(D_Exceptions) throw exception;
            else assert(0, errorMsg);
        }
        if (__ctfe)
            _data[0 .. str.length] =  str;
        else
            memcpy(_data.ptr, str.ptr, str.length);
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(uint n)(auto ref scope const SmallString!n rhs) scope return
        if (n != maxLength)
    {
        static if (n < maxLength)
        {
            _data = '\0';
            version (LDC)
                cast(char[n])(_data[0 .. n]) = rhs._data;
            else
                _data[0 .. n] = rhs._data;
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
    ref typeof(this) opAssign(uint n)(const SmallString!n rhs) scope return
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

    ///
    extern (D) size_t toHash() const nothrow @safe
    {
        return hashOf(this[]);
    }

scope nothrow:

    /++
    Returns an scope common string.

    The method implement with `[]` operation.
    +/
    inout(char)[] opIndex() inout @trusted scope return
    {
        import mir.string: scanLeftAny;
        return _data[0 .. $ - _data.scanLeftAny('\0').length];
    }

    ///
    ref inout(char) opIndex(size_t index) inout scope return
    {
        return opIndex[index];
    }

    /++
    Returns a common scope string.

    The method implement with `[i .. j]` operation.
    +/
    inout(char)[] opIndex(size_t[2] range) inout @trusted scope return
    in (range[0] <= range[1])
    in (range[1] <= this.length)
    {
        return opIndex()[range[0] .. range[1]];
    }

scope const:

    /// ditto
    size_t[2] opSlice(size_t pos : 0)(size_t i, size_t j) {
        return [i, j];
    }

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

    /// ditto
    alias opDollar(size_t pos : 0) = length;

    ///
    alias toString = opIndex;

    /// Comparisons operator overloads
    bool opEquals(ref scope const SmallString rhs)
    {
        return _data == rhs._data;
    }

    /// ditto
    bool opEquals(SmallString rhs)
    {
        return _data == rhs._data;
    }

    /// ditto
    bool opEquals(uint rhsMaxLength)(auto ref scope const SmallString!rhsMaxLength rhs)
        if (rhsMaxLength != maxLength)
    {
        return opIndex == rhs.opIndex;
    }

    /// ditto
    bool opEquals()(scope const(char)[] str)
    {
        return opIndex == str;
    }

    /// ditto
    int opCmp(uint rhsMaxLength)(auto ref scope const SmallString!rhsMaxLength rhs)
    {
        return __cmp(opIndex, rhs.opIndex);
    }

    /// ditto
    int opCmp()(scope const(char)[] str)
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
    assert(s8 == "Hellow!!");
    assert(s8[] == "Hellow!!");
    assert(s8[0 .. $] == "Hellow!!");
    assert(s8[1 .. 4] == "ell");

    s16 = s8;
    assert(s16 == "Hellow!!");
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
