/++
$(H1 Ordered string-value associtaive array)
Macros:
AlgebraicREF = $(GREF_ALTTEXT mir-core, $(TT $1), $1, mir, algebraic)$(NBSP)
+/

module mir.string_map;

import std.traits;

/++
Ordered string-value associtaive array with extremely fast lookup.

Params:
    T = mutable value type, can be instance of $(AlgebraicREF Algebraic) for example.
    U = an unsigned type that can hold an index of keys. `U.max` must be less then the maximum possible number of struct members.
+/
struct StringMap(T, U = uint)
    if (isMutable!T && !__traits(hasMember, T, "opPostMove") && __traits(isUnsigned, U))
{
    import mir.utility: _expect;
    import core.lifetime: move;
    import mir.conv: emplaceRef;

    private alias Impl = StructImpl!(T, U);
    private Impl* implementation;

    /++
    +/
    this(T[string] aa) @trusted pure nothrow
    {
        this(aa.keys, aa.values);
    }

    static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!int map = ["key" : 1];
        assert(map.findPos("key") == 0);
    }

    /++
    +/
    this(string[] keys, T[] values) @trusted pure nothrow
    {
        assert(keys.length == values.length);
        implementation = new Impl(keys, values);
    }

    static if (is(T == int))
    ///
    @safe pure unittest
    {
        auto keys = ["ba", "a"];
        auto values = [1.0, 3.0];
        auto map = StringMap!double(keys, values);
        assert(map.keys is keys);
        assert(map.values is values);
    }

    /++
    Returns: number of elements in the table.
    +/
    size_t length() @safe pure nothrow @nogc const @property
    {
        return implementation ? implementation.length : 0;
    }

    static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!double map;
        assert(map.length == 0);
        map["a"] = 3.0;
        assert(map.length == 1);
        map["c"] = 4.0;
        assert(map.length == 2);
        map.remove("c");
        assert(map.length == 1);
        map.remove("c");
        assert(map.length == 1);
        map.remove("a");
        assert(map.length == 0);
    }

    /++
    Returns a dynamic array, the elements of which are the keys in the associative array.
    Doesn't allocate a new copy.
    +/
    const(string)[] keys() @safe pure nothrow @nogc const @property
    {
        return implementation ? implementation.keys : null;
    }

    static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!double map;
        assert(map.keys == []);
        map["c"] = 4.0;
        assert(map.keys == ["c"]);
        map["a"] = 3.0;
        assert(map.keys == ["c", "a"]);
        map.remove("c");
        assert(map.keys == ["a"]);
        map.remove("a");
        assert(map.keys == []);
        map["c"] = 4.0;
        assert(map.keys == ["c"]);
    }

    /++
    Returns a dynamic array, the elements of which are the values in the associative array.
    Doesn't allocate a new copy.
    +/
    inout(T)[] values() @safe pure nothrow @nogc inout @property
    {
        return implementation ? implementation.values : null;
    }

    static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!double map;
        assert(map.values == []);
        map["c"] = 4.0;
        assert(map.values == [4.0]);
        map["a"] = 3.0;
        assert(map.values == [4.0, 3.0]);
        map.values[0]++;
        assert(map.values == [5.0, 3.0]);
        map.remove("c");
        assert(map.values == [3.0]);
        map.remove("a");
        assert(map.values == []);
        map["c"] = 4.0;
        assert(map.values == [4.0]);
    }

    /++
    (Property) Gets the current capacity of an associative array.
    The capacity is the size that the underlaynig slices can grow to before the underlying arrays may be reallocated or extended.
    +/
    size_t capacity() @safe pure nothrow const @property
    {
        import mir.utility: min;

        return !implementation ? 0 : min(
            implementation.keys.capacity,
            implementation.values.capacity,
            implementation.indices.capacity,
        );
    }

    static if (is(T == int))
    ///
    unittest
    {
        StringMap!double map;
        assert(map.capacity == 0);
        map["c"] = 4.0;
        assert(map.capacity >= 1);
        map["a"] = 3.0;
        assert(map.capacity >= 2);
        map.remove("c");
        map.assumeSafeAppend;
        assert(map.capacity >= 2);
    }

    /++
    Reserves capacity for an associative array. 
    The capacity is the size that the underlaying slices can grow to before the underlying arrays may be reallocated or extended.
    +/
    size_t reserve(size_t newcapacity) @trusted pure nothrow 
    {
        import mir.utility: min;

        if (_expect(!implementation, false))
        {
            implementation = new Impl;
        }

        auto keysV = implementation.keys;
        auto keysVCaacity = keysV.reserve(newcapacity);
        implementation._keys = keysV.ptr;

        auto valuesV = implementation.values;
        auto valuesCapacity = valuesV.reserve(newcapacity);
        implementation._values = valuesV.ptr;

        auto indicesV = implementation.indices;
        auto indicesCapacity = indicesV.reserve(newcapacity);
        implementation._indices = indicesV.ptr;

        return min(
            keysVCaacity,
            valuesCapacity,
            indicesCapacity,
        );
    }

    /++
    Assume that it is safe to append to this associative array.
    Appends made to this associative array after calling this function may append in place, even if the array was a slice of a larger array to begin with.
    Use this only when it is certain there are no elements in use beyond the associative array in the memory block. If there are, those elements will be overwritten by appending to this associative array.

    Warning: Calling this function, and then using references to data located after the given associative array results in undefined behavior.

    Returns: The input is returned.
    +/
    ref inout(typeof(this)) assumeSafeAppend() @system nothrow inout return
    {
        if (implementation)
        {
            implementation.keys.assumeSafeAppend;
            implementation.values.assumeSafeAppend;
            implementation.indices.assumeSafeAppend;
        }
        return this;
    }

    /++
    Removes all remaining keys and values from an associative array.
    +/
    void clear() @safe pure nothrow @nogc
    {
        if (implementation)
        {
            implementation._length = 0;
            implementation._lengthTable = implementation._lengthTable[0 .. 0];
        }

    }

    /++
    +/
    bool remove(scope const(char)[] key) @trusted pure nothrow @nogc
    {
        size_t index;
        if (implementation && implementation.findIndex(key, index))
        {
            implementation.removeAt(index);
            return true;
        }
        return false;
    }

    /++
    +/
    ptrdiff_t findPos(scope const(char)[] key) @trusted pure nothrow @nogc const
    {
        if (!implementation)
            return -1;
        size_t index;
        if (!implementation.findIndex(key, index))
            return -1;
        return implementation._indices[index];
    }

    /++
    +/
    inout(T)* opBinaryRight(string op : "in")(scope const(char)[] key) @system pure nothrow @nogc inout
    {
        if (!implementation)
            return null;
        size_t index;
        if (!implementation.findIndex(key, index))
            return null;
        return implementation._values + index;
    }

    /++
    +/
    ref inout(T) opIndex(scope const(char)[] key) @trusted pure inout //@nogc
    {
        size_t index;
        if (implementation && implementation.findIndex(key, index))
        {
            assert (index < length);
            index = implementation._indices[index];
            assert (index < length);
            return implementation._values[index];
        }
        import mir.exception: MirException;
        throw new MirException("No member: ", key);
    }

    /++
    +/
    ref T opIndexAssign(T value, string key) @trusted pure nothrow
    {
        size_t index;
        if (_expect(!implementation, false))
        {
            implementation = new Impl;
        }
        else
        {
            if (key.length + 1 < implementation.lengthTable.length)
            {
                if (implementation.findIndex(key, index))
                {
                    assert (index < length);
                    index = implementation._indices[index];
                    assert (index < length);
                    implementation._values[index] = move(value);
                    return implementation._values[index];
                }
                assert (index <= length);
                index = index < length ? implementation.indices[index] : length;
                assert (index <= length);
            }
            else
            {
                index = length;
            }
        }
        assert (index <= length);
        implementation.insertAt(key, move(value), index);
        return implementation._values[index];
    }

    /++
    +/
    inout(T) get(scope const(char)[] key, lazy inout(T) defaultValue)
    {
        size_t index;
        if (implementation && implementation.findIndex(key, index))
        {
            assert (index < length);
            index = implementation.indices[index];
            assert (index < length);
            return implementation.values[index];
        }
        return defaultValue;
    }

    /++
    +/
    ref T require(string key, lazy T value = T.init)
    {
        import std.stdio;
        size_t index;
        if (_expect(!implementation, false))
        {
            implementation = new Impl;
        }
        else
        {
            if (key.length + 1 < implementation.lengthTable.length)
            {
                if (implementation.findIndex(key, index))
                {
                    assert (index < length);
                    index = implementation.indices[index];
                    assert (index < length);
                    return implementation.values[index];
                }
                assert (index <= length);
                index = index < length ? implementation.indices[index] : length;
                assert (index <= length);
            }
            else
            {
                index = length;
            }
        }
        assert (index <= length);
        implementation.insertAt(key, value, index);
        return implementation.values[index];
    }

    static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!int aa = ["aa": 1];
        assert(aa.require("aa", 0) == 1);
        assert(aa.require("bb", 0) == 0);
        assert(aa["bb"] == 0);
    }
}

///
unittest
{
    StringMap!int table;
    table["L"] = 3;
    table["A"] = 2;
    table["val"] = 1;
    assert(table.keys == ["L", "A", "val"]);
    assert(table.values == [3, 2, 1]);
    assert(table["A"] == 2);
    table.values[2] += 10;
    assert(table["A"] == 2);
    assert(table["L"] == 3);
    assert(table["val"] == 11);
    assert(table.keys == ["L", "A", "val"]);
    assert(table.values == [3, 2, 11]);
    table.remove("A");
    assert(table.keys == ["L", "val"]);
    assert(table.values == [3, 11]);
    assert(table["L"] == 3);
    assert(table["val"] == 11);
}

private struct StructImpl(T, U = uint)
    if (!__traits(hasMember, T, "opPostMove") && __traits(isUnsigned, U))
{
    import core.lifetime: move;
    import mir.conv: emplaceRef;

    size_t _length;
    string* _keys;
    T* _values;
    U* _indices;
    U[] _lengthTable;

    /++
    +/
    this(string[] keys, T[] values) @trusted pure nothrow
    {
        import mir.array.allocation: array;
        import mir.ndslice.sorting: sort;
        import mir.ndslice.topology: iota, indexed;
        import mir.string_table: smallerStringFirst;

        assert(keys.length == values.length);
        if (keys.length == 0)
            return;
        _length = keys.length;
        _keys = keys.ptr;
        _values = values.ptr;
        _indices = keys.length.iota!U.array.ptr;
        auto sortedKeys = _keys.indexed(indices);
        sortedKeys.sort!smallerStringFirst;
        size_t maxKeyLength;
        foreach (ref key; keys)
            if (key.length > maxKeyLength)
                maxKeyLength = key.length;
        _lengthTable = new U[maxKeyLength + 2];

        size_t ski;
        foreach (length; 0 .. maxKeyLength + 1)
        {
            while(ski < sortedKeys.length && sortedKeys[ski].length == length)
                ski++;
            _lengthTable[length + 1] = cast(U)ski;
        }
    }

    // this(size_t length, size_t maxKeyLength)
    // {
    //     assert(length);
    //     _length = length;
    //     _keys = new string[length].ptr;
    //     _values = new T[length].ptr;
    //     _indices = new U[length].assumeSafeAppend;
    //     _lengthTable = new U[maxKeyLength + 2].assumeSafeAppend;
    // }

    // void addFirstEntry(string key, T value)
    // {
    //     import core.lifetime: move;
    //     pragma(inline, false);
    //     __ctor(1, key.length);
    //     keys[0] = key;
    //     values[0] = move(value);
    //     lengthTable[key.length + 1 .. $] = 1;
    // }

    void insertAt(string key, T value, size_t i) @trusted
    {
        pragma(inline, false);

        assert(i <= length);
        {
            auto a = keys;
            a ~= key;
            _keys = a.ptr;
        }
        {
            auto a = values;
            a ~= move(value);
            _values = a.ptr;
        }
        {
            auto a = indices;
            a ~= 0;
            _indices = a.ptr;

            if (__ctfe)
            {
                foreach_reverse (idx; i .. length)
                {
                    _indices[idx + 1] = _indices[idx];
                }
            }
            else
            {
                import core.stdc.string: memmove;
                memmove(_indices + i + 1, _indices + i, (length - i) * U.sizeof);
            }
            assert(length <= U.max);
            _indices[i] = cast(U)length;
            _length++;
        }
        {
            if (key.length + 2 <= lengthTable.length)
            {
                ++lengthTable[key.length + 1 .. $];
            }
            else
            {
                auto oldLen = _lengthTable.length;
                _lengthTable.length = key.length + 2;
                auto oldVal = oldLen ? _lengthTable[oldLen - 1] : 0;
                _lengthTable[oldLen .. key.length + 1] =  oldVal;
                _lengthTable[key.length + 1] =  oldVal + 1;
            }
        }
    }

    void removeAt(size_t i)
    {
        assert(i < length);
        auto j = _indices[i];
        assert(j < length);
        {
            --_lengthTable[_keys[j].length + 1 .. $];
        }
        {
            if (__ctfe)
            {
                foreach (idx; i .. length)
                {
                    _indices[idx] = _indices[idx + 1];
                    _indices[idx] = _indices[idx + 1];
                }
            }
            else
            {
                import core.stdc.string: memmove;
                memmove(_indices + i, _indices + i + 1, (length - 1 - i) * U.sizeof);
            }
            foreach (ref elem; indices[0 .. $ - 1])
                if (elem > j)
                    elem--;
        }
        {
            if (__ctfe)
            {
                foreach_reverse (idx; j .. length - 1)
                {
                    _keys[idx] = _keys[idx + 1];
                    _values[idx] = move(_values[idx + 1]);
                }
            }
            else
            {
                import core.stdc.string: memmove;
                destroy!false(_values[j]);
                memmove(_keys + j, _keys + j + 1, (length - 1 - j) * string.sizeof);
                memmove(_values + j, _values + j + 1, (length - 1 - j) * T.sizeof);
                emplaceRef(_values[length - 1]);
            }
        }
        _length--;
        _lengthTable = _lengthTable[0 .. length ? _keys[length - 1].length + 2 : 0];
    }

    size_t length() @safe pure nothrow @nogc const @property
    {
        return _length;
    }

    inout(string)[] keys() @trusted inout @property
    {
        return _keys[0 .. _length];
    }
    
    inout(T)[] values() @trusted inout @property
    {
        return _values[0 .. _length];
    }
    
    inout(U)[] indices() @trusted inout @property
    {
        return _indices[0 .. _length];
    }
    
    inout(U)[] lengthTable() @trusted inout @property
    {
        return _lengthTable;
    }

    auto sortedKeys() @trusted const @property
    {
        import mir.ndslice.topology: indexed;
        return _keys.indexed(indices);
    }

    bool findIndex(scope const(char)[] key, ref size_t index) @trusted pure nothrow @nogc const
    {
        import mir.utility: _expect;
        if (_expect(key.length + 1 < _lengthTable.length, true))
        {

            // 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
            // 0 1 2 3 4 5 6   8 9 10    12          16

            auto low = _lengthTable[key.length] + 0u;
            auto high = _lengthTable[key.length + 1] + 0u;
            while (low < high)
            {
                auto mid = (low + high) / 2;

                import core.stdc.string: memcmp;
                int r = void;

                if (__ctfe)
                    r = __cmp(key, _keys[_indices[mid]]);
                else
                    r = memcmp(key.ptr, _keys[_indices[mid]].ptr, key.length);

                if (r == 0)
                {
                    index = mid;
                    return true;
                }
                if (r > 0)
                    low = mid + 1;
                else
                    high = mid;
            }
            index = low;
        }
        return false;
    }
}
