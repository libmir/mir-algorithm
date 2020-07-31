/++
$(H1 Small String)

The module contains self-contained generic small string implementaton.

$(LREF SmallString) supports ASDF - Json Serialisation Library.

See also `include/mir/small_series.h` for a C++ version of this type.
Both C++ and D implementations have the same ABI and name mangling.

Copyright: Copyright © 2019, Symmetry Investments, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko
+/
module mir.small_string;

private extern (C) @system nothrow @nogc pure size_t strnlen_s(scope const char* s, size_t n);

private static immutable errorMsg = "Cannot create SmallString: input string exceeds maximum allowed length.";
version(D_Exceptions)
    private static immutable exception = new Exception(errorMsg);

extern(C++, "mir"):

/++
Self-contained generic Small String implementaton.
+/
struct SmallString(uint maxLength)
    if (maxLength)
{

    import core.stdc.string: memcmp, memcpy, strlen;
    import std.traits: Unqual, isIterable;

    // maxLength bytes
    private char[maxLength] _data = '\0';

extern(D):

	static SmallString deserialize(S)(S data)
	{
        import asdf.serialization: deserialize;
        return SmallString(data.deserialize!(const(char)[]));
	}

	void serialize(S)(ref S serializer)
	{
		serializer.putValue(asArray);
	}

@safe pure @nogc:

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
    this(const SmallString str) nothrow
    {
        this.opAssign(str);
    }

    /// ditto
    this(uint n)(const SmallString!n str)
    {
        this.opAssign(str);
    }

    /// ditto
    this(uint n)(ref scope const SmallString!n str)
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
        _data = '\0';
        if (__ctfe)
            (cast(char[])_data)[0 .. str.length] = cast(char[]) str;
        else
            memcpy(_data.ptr, str.ptr, str.length);
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(ref scope const SmallString rhs) return nothrow
    {
        _data = rhs._data;
        return this;
    }
    
    /// ditto
    ref typeof(this) opAssign(const SmallString rhs) return nothrow
    {
        _data = rhs._data;
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(uint n)(ref scope const SmallString!n rhs) return
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
            (cast(char[])_data)[0 .. str.length] = cast(char[]) str;
        else
            memcpy(_data.ptr, str.ptr, str.length);
    }

    ///
    ref typeof(this) append(char c) @trusted
    {
        auto length = asArray.length;
        if (length == maxLength)
            throw exception;
        _data[length] = c;
        return this;
    }

    ///
    ref typeof(this) append(scope const(char)[] str) @trusted
    {
        auto length = asArray.length;
        if (length + str.length > maxLength)
            throw exception;
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
    inout(char)[] asArray() inout @trusted return @property
    {
        size_t i;
        if (__ctfe)
            while (i < maxLength && _data[i]) i++;
        else
            i = _data[$ - 1] ? _data.length : strlen(_data.ptr);
        return _data[0 .. i];
    }

    alias asArray this;

const:

    ///
    const(char)[] toString() return
    {
        return asArray;
    }

    /// Comparisons operator overloads
    int opCmp(ref scope const typeof(this) rhs) @trusted
    {
        if (__ctfe)
        {
            foreach (i, ref c; _data)
                if (auto d = c - rhs._data[i])
                    return d;
            return 0;
        }
        else
        {
            return memcmp(this._data.ptr, rhs._data.ptr, _data.sizeof);
        }

    }

    /// ditto
    int opCmp(scope const(char)[] str)
    {
        import mir.algorithm.iteration: cmp;
        return cast(int) cmp(asArray, str);
    }

    /++
    Checks if the string is empty (null).
    +/
    C opCast(C)() const
        if (is(Unqual!C == bool))
    {
        return _data[0] != 0;
    }

    /// Hash implementation
    size_t toHash()
    {
        return hashOf(_data[]);
    }
}

///
@safe pure @nogc version(mir_test) unittest
{
    SmallString!16 s16;
    assert(!s16);

    auto s8 = SmallString!8("Hellow!!");
    assert(s8);
    assert(s8 == "Hellow!!", s8[]);

    s16 = s8;
    assert(s16 == "Hellow!!", s16);
    s16[7] = '@';
    s8 = null;
    assert(!s8);
    assert(s8 == null);
    assert(s8 !is null);
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
