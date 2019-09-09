/++
$(H1 Small Array)

The module contains self-contained generic small array implementaton.

$(LREF SmallArray) supports ASDF - Json Serialisation Library.

Copyright: Copyright © 2019, Symmetry Investments, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko
+/
module mir.small_array;

private static immutable errorMsg = "Cannot create SmallArray: input range exceeds maximum allowed length.";
version(D_Exceptions)
    private static immutable exception = new Exception(errorMsg);

///
struct SmallArray(T, uint maxLength)
    if (maxLength)
{
    import std.traits: isIterable, isImplicitlyConvertible;

    private uint _length;
    T[maxLength] _data;

	static SmallArray deserialize(S)(S data)
	{
        import asdf.serialization: deserialize;
        return SmallArray(data.deserialize!(T[]));
	}

	void serialize(S)(ref S serializer)
	{
		serializer.putValue(asArray);
	}

    static if (isImplicitlyConvertible!(const T, T))
        alias V = const T;
    else
        alias V = T;

@safe pure @nogc:

    /// Constructor
    this(typeof(null))
    {
    }

    /// ditto
    this(V[] array)
    {
        this.opAssign(array);
    }

    /// ditto
    this(uint n)(SmallArray!(T, n) array)
    {
        this.opAssign(array);
    }

    /// ditto
    this(uint n)(ref SmallArray!(T, n) array)
    {
        this.opAssign(array);
    }

    /// ditto
    this(Range)(auto ref Range array)
        if (isIterable!Range)
    {
        foreach(ref c; array)
        {
            if (_length > _data.length)
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data[_length++] = c;
        }
    }

    /// `=` operator
    ref typeof(this) opAssign(typeof(null)) return
    {
        _length = 0;
        _data = T.init;
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(V[] array) return @trusted
    {
        if (array.length > maxLength)
        {
            version(D_Exceptions) throw exception;
            else assert(0, errorMsg);
        }
        _data[0 .. _length] = T.init;
        _length = cast(uint) array.length;
        _data[0 .. _length] = array;
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(ref SmallArray rhs) return
    {
        _data = rhs._data;
        return this;
    }
    
    /// ditto
    ref typeof(this) opAssign(SmallArray rhs) return
    {
        _data = rhs._data;
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(uint n)(ref SmallArray!(T, n) rhs) return
        if (n != maxLength)
    {
        static if (n < maxLength)
        {
            _data[0 .. n] = rhs._data;
            if (_length > n)
                _data[n .. _length] = T.init;
        }
        else
        {
            if (rhs._length > maxLength)
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data = rhs._data[0 .. maxLength];
        }
        _length = rhs._length;
        return this;
    }

    /// ditto
    ref typeof(this) opAssign(uint n)(SmallArray!(T, n) rhs) return
        if (n != maxLength)
    {
        static if (n < maxLength)
        {
            _data[0 .. n] = rhs._data;
            if (_length > n)
                _data[n .. _length] = T.init;
        }
        else
        {
            if (rhs._data[maxLength])
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data = rhs._data[0 .. maxLength];
        }
        _length = rhs._length;
        return this;
    }

    ///
    ref typeof(this) append(V[] array)
    {
        auto length = asArray.length;
        if (length + array.length > maxLength)
            throw exception;
        _data[_length .. _length + array.length] = array;
        _length += array.length;
        return this;
    }

    /// ditto
    alias put = append;

    /// ditto
    alias opOpAssign(string op : "~") = append;

    ///
    SmallArray concat(V[] array) scope const
    {
        SmallArray c = this;
        c.append(array);
        return c; 
    }

    /// ditto
    alias opBinary(string op : "~") = concat;


scope nothrow:

    /++
    Returns an scope common array.

    The property is used as common array representation self alias.

    The alias helps with `[]`, `[i]`, `[i .. j]`, `==`, and `!=` operations and implicit conversion to strings.
    +/
    inout(T)[] asArray() inout @trusted return @property
    {
        return _data[0 .. _length];
    }

    alias asArray this;

const:

    /++
    Checks if the array is empty (null).
    +/
    bool opCast(T : bool)()
    {
        return _length != 0;
    }

    /// Hash implementation
    size_t toHash()
    {
        return hashOf(asArray);
    }

    /// ditto
    auto opCmp()(V[] array)
    {
        import mir.algorithm.iteration: cmp;
        return cmp(asArray, array);
    }
}

///
@safe pure @nogc version(mir_test) unittest
{
    SmallArray!(char, 16) s16;
    assert(!s16);

    auto s8 = SmallArray!(char, 8)("Hellow!!");
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
    auto a = SmallArray!(char, 16)("asdf");
    a ~= " ";
    auto b = a ~ "qwerty";
    static assert(is(typeof(b) == SmallArray!(char, 16)));
    assert(b == "asdf qwerty");
    b.put("!");
    assert(b == "asdf qwerty!");
}
