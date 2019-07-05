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
    import std.traits: isIterable;

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
    this(uint n)(SmallString!n str)
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
        if (__ctfe)
            (cast(ubyte[])_data)[0 .. str.length] = cast(ubyte[]) str;
        else
            memcpy(_data.ptr, str.ptr, str.length);
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(ref scope const SmallString rhs) return
    {
        _data = rhs._data;
        return this;
    }
    
    /// ditto
    ref typeof(this) opAssign(SmallString rhs) return
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
            _data = cast(char[0 .. maxLength])(rhs._data[0 .. maxLength]);
        }
    }

    /// ditto
    ref typeof(this) opAssign(uint n)(SmallString!n rhs) return
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
    bool opCast(T : bool)()
    {
        return cast(bool) _data[0] != 0;
    }

    /// Hash implementation
    size_t toHash()
    {
        return hashOf(_data[]);
    }
}

///
@safe pure version(mir_test) unittest
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
