/++
$(H1 Ordered string-value associtaive array)
Macros:
AlgebraicREF = $(GREF_ALTTEXT mir-core, $(TT $1), $1, mir, algebraic)$(NBSP)
+/

module mir.string_map;

import std.traits;

/++
Checks if the type is instance of $(LREF StringMap).
+/
enum isStringMap(T) = is(Unqual!T == StringMap!V, V);

version(mir_test)
///
unittest
{
    static assert(isStringMap!(StringMap!int));
    static assert(isStringMap!(const StringMap!int));
    static assert(!isStringMap!int);
}

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

    private alias Impl = StructImpl!(T, U);
    private Impl* implementation;

    ///
    // current implementation is workaround for linking bugs when used in self referencing algebraic types
    bool opEquals(V)(scope const StringMap!(V, U) rhs) const
    {
        // NOTE: moving this to template restriction fails with recursive template instanation
        static assert(is(typeof(T.init == V.init) : bool),
                      "Unsupported rhs of type " ~ typeof(rhs).stringof);
        if (keys != rhs.keys)
            return false;
        if (implementation)
            foreach (const i; 0 .. implementation._length)
                if (implementation.values[i] != rhs.implementation.values[i]) // needs `values` instead of `_values` to be @safe
                    return false;
        return true;
    }
    /// ditto
    bool opEquals(K, V)(scope const V[K] rhs) const
    {
        // NOTE: moving this to template restriction fails with recursive template instanation
        static assert(is(typeof(K.init == string.init) : bool),
                      "Unsupported rhs key type " ~ typeof(rhs).stringof);
        static assert(is(typeof(V.init == T.init) : bool),
                      "Unsupported rhs value type " ~ typeof(rhs).stringof);
        if (implementation is null)
            return rhs.length == 0;
        if (implementation._length != rhs.length)
            return false;
        foreach (const i; 0 .. implementation._length)
        {
            if (const valuePtr = implementation.keys[i] in rhs)
            {
                if (*valuePtr != implementation.values[i])
                    return false;
            }
            else
                return false;
        }
        return true;
    }

    // // linking bug
    // version(none)
    // {
    //     /++
    //     +/
    //     bool opEquals()(typeof(null)) @safe pure nothrow @nogc const
    //     {
    //         return implementation is null;
    //     }

    //     version(mir_test) static if (is(T == int))
    //     ///
    //     @safe pure unittest
    //     {
    //         StringMap!int map;
    //         assert(map == null);
    //         map = StringMap!int(["key" : 1]);
    //         assert(map != null);
    //         map.remove("key");
    //         assert(map != null);
    //     }
    // }

    /++
    Reset the associtave array
    +/
    ref opAssign()(typeof(null)) return @safe pure nothrow @nogc
    {
        implementation = null;
        return this;
    }

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!int map = ["key" : 1];
        map = null;
    }

    /++
    Initialize the associtave array with default value.
    +/
    this()(typeof(null) aa) @safe pure nothrow @nogc
    {
        implementation = null;
    }

    version(mir_test) static if (is(T == int))
    /// Usefull for default funcion argument.
    @safe pure unittest
    {
        StringMap!int map = null; //
    }

    /++
    Constructs an associative array using keys and values from the builtin associative array
    Complexity: `O(n log(n))`
    +/
    this()(T[string] aa) @trusted pure nothrow
    {
        this(aa.keys, aa.values);
    }

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!int map = ["key" : 1];
        assert(map.findPos("key") == 0);
    }

    ///
    string toString()() const
    {
        import mir.format: stringBuf;
        stringBuf buffer;
        toString(buffer);
        return buffer.data.idup;
    }

    ///ditto
    void toString(W)(scope ref W w) const
    {
        bool next;
        w.put('[');
        import mir.format: printEscaped, EscapeFormat, print;
        foreach (i, ref value; values)
        {
            if (next)
                w.put(`, `);
            next = true;
            w.put('\"');
            printEscaped!(char, EscapeFormat.ion)(w, keys[i]);
            w.put(`": `);
            print(w, value);
        }
        w.put(']');
    }

    /++
    Constructs an associative array using keys and values.
    Params:
        keys = mutable array of keys
        values = mutable array of values
    Key and value arrays must have the same length.

    Complexity: `O(n log(n))`
    +/
    this()(string[] keys, T[] values) @trusted pure nothrow
    {
        assert(keys.length == values.length);
        implementation = new Impl(keys, values);
    }

    version(mir_test) static if (is(T == int))
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
    size_t length()() @safe pure nothrow @nogc const @property
    {
        return implementation ? implementation.length : 0;
    }

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!double map;
        assert(map.length == 0);
        map["a"] = 3.0;
        assert(map.length == 1);
        map["c"] = 4.0;
        assert(map.length == 2);
        assert(map.remove("c"));
        assert(map.length == 1);
        assert(!map.remove("c"));
        assert(map.length == 1);
        assert(map.remove("a"));
        assert(map.length == 0);
    }

    /++
    Returns a dynamic array, the elements of which are the keys in the associative array.
    Doesn't allocate a new copy.

    Complexity: `O(1)`
    +/
    const(string)[] keys()() @safe pure nothrow @nogc const @property
    {
        return implementation ? implementation.keys : null;
    }

    version(mir_test) static if (is(T == int))
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

    Complexity: `O(1)`
    +/
    inout(T)[] values()() @safe pure nothrow @nogc inout @property
    {
        return implementation ? implementation.values : null;
    }

    version(mir_test) static if (is(T == int))
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

    Complexity: `O(1)`
    +/
    size_t capacity()() @safe pure nothrow const @property
    {
        import mir.utility: min;

        return !implementation ? 0 : min(
            implementation.keys.capacity,
            implementation.values.capacity,
            implementation.indices.capacity,
        );
    }

    version(mir_test) static if (is(T == int))
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
    size_t reserve()(size_t newcapacity) @trusted pure nothrow
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

    version(mir_test) static if (is(T == int))
    ///
    unittest
    {
        StringMap!double map;
        auto capacity = map.reserve(10);
        assert(capacity >= 10);
        assert(map.capacity == capacity);
        map["c"] = 4.0;
        assert(map.capacity == capacity);
        map["a"] = 3.0;
        assert(map.capacity >= 2);
        assert(map.remove("c"));
        capacity = map.reserve(20);
        assert(capacity >= 20);
        assert(map.capacity == capacity);
    }

    /++
    Assume that it is safe to append to this associative array.
    Appends made to this associative array after calling this function may append in place, even if the array was a slice of a larger array to begin with.
    Use this only when it is certain there are no elements in use beyond the associative array in the memory block. If there are, those elements will be overwritten by appending to this associative array.

    Warning: Calling this function, and then using references to data located after the given associative array results in undefined behavior.

    Returns: The input is returned.
    +/
    ref inout(typeof(this)) assumeSafeAppend()() nothrow inout return
    {
        if (implementation)
        {
            implementation.keys.assumeSafeAppend;
            implementation.values.assumeSafeAppend;
            implementation.indices.assumeSafeAppend;
        }
        return this;
    }

    version(mir_test) static if (is(T == int))
    ///
    unittest
    {
        StringMap!double map;
        map["c"] = 4.0;
        map["a"] = 3.0;
        assert(map.capacity >= 2);
        map.remove("c");
        assert(map.capacity == 0);
        map.assumeSafeAppend;
        assert(map.capacity >= 2);
    }

    /++
    Removes all remaining keys and values from an associative array.

    Complexity: `O(1)`
    +/
    void clear()() @safe pure nothrow @nogc
    {
        if (implementation)
        {
            implementation._length = 0;
            implementation._lengthTable = implementation._lengthTable[0 .. 0];
        }

    }

    version(mir_test) static if (is(T == int))
    ///
    unittest
    {
        StringMap!double map;
        map["c"] = 4.0;
        map["a"] = 3.0;
        map.clear;
        assert(map.length == 0);
        assert(map.capacity == 0);
        map.assumeSafeAppend;
        assert(map.capacity >= 2);
    }

    /++
    `remove(key)` does nothing if the given key does not exist and returns false. If the given key does exist, it removes it from the AA and returns true.

    Complexity: `O(log(s))` (not exist) or `O(n)` (exist), where `s` is the count of the strings with the same length as they key.
    +/
    bool remove()(scope const(char)[] key) @trusted pure nothrow @nogc
    {
        size_t index;
        if (implementation && implementation.findIndex(key, index))
        {
            implementation.removeAt(index);
            return true;
        }
        return false;
    }

    version(mir_test) static if (is(T == int))
    ///
    unittest
    {
        StringMap!double map;
        map["a"] = 3.0;
        map["c"] = 4.0;
        assert(map.remove("c"));
        assert(!map.remove("c"));
        assert(map.remove("a"));
        assert(map.length == 0);
        assert(map.capacity == 0);
        assert(map.assumeSafeAppend.capacity >= 2);
    }

    /++
    Finds position of the key in the associative array .

    Return: An index starting from `0` that corresponds to the key or `-1` if the associative array doesn't contain the key.

    Complexity: `O(log(s))`, where `s` is the number of the keys with the same length as the input key.
    +/
    ptrdiff_t findPos()(scope const(char)[] key) @trusted pure nothrow @nogc const
    {
        if (!implementation)
            return -1;
        size_t index;
        if (!implementation.findIndex(key, index))
            return -1;
        return implementation._indices[index];
    }

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!double map;
        map["c"] = 3.0;
        map["La"] = 4.0;
        map["a"] = 5.0;

        assert(map.findPos("C") == -1);
        assert(map.findPos("c") == 0);
        assert(map.findPos("La") == 1);
        assert(map.findPos("a") == 2);

        map.remove("c");

        assert(map.findPos("c") == -1);
        assert(map.findPos("La") == 0);
        assert(map.findPos("a") == 1);
    }

    /++
    Complexity: `O(log(s))`, where `s` is the number of the keys with the same length as the input key.
    +/
    inout(T)* opBinaryRight(string op : "in")(scope const(char)[] key) pure nothrow @nogc inout
    {
        if (!implementation)
            return null;
        size_t index;
        if (!implementation.findIndex(key, index))
            return null;
        assert (index < length);
        index = implementation.indices[index];
        assert (index < length);
        return &implementation.values[index];
    }

    version(mir_test) static if (is(T == int))
    ///
    @safe nothrow pure unittest
    {
        StringMap!double map;
        assert(("c" in map) is null);
        map["c"] = 3.0;
        assert(*("c" in map) == 3.0);
    }

    /++
    Complexity: `O(log(s))`, where `s` is the number of the keys with the same length as the input key.
    +/
    ref inout(T) opIndex()(scope const(char)[] key) @trusted pure inout //@nogc
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

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!double map;
        map["c"] = 3.0;
        map["La"] = 4.0;
        map["a"] = 5.0;

        map["La"] += 10;
        assert(map["La"] == 14.0);
    }

    /++
    Complexity: `O(log(s))` (exist) or `O(n)` (not exist), where `s` is the count of the strings with the same length as they key.
    +/
    ref T opIndexAssign(R)(auto ref R value, string key) @trusted pure nothrow
    {
        import core.lifetime: forward, move;
        T v;
        v = forward!value;
        return opIndexAssign(move(v), key);
    }

    /// ditto
    ref T opIndexAssign()(T value, string key) @trusted pure nothrow
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
            }
            else
            {
                index = length;
            }
        }
        assert (index <= length);
        implementation.insertAt(key, move(value), index);
        index = implementation._indices[index];
        return implementation._values[index];
    }

    /++
    Looks up key; if it exists returns corresponding value else evaluates and returns defaultValue.

    Complexity: `O(log(s))`, where `s` is the number of the keys with the same length as the input key.
    +/
    inout(T) get()(scope const(char)[] key, lazy inout(T) defaultValue)
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

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!int map;
        map["c"] = 3;
        assert(map.get("c", 1) == 3);
        assert(map.get("C", 1) == 1);
    }

    /++
    Looks up key; if it exists returns corresponding value else evaluates value, adds it to the associative array and returns it.

    Complexity: `O(log(s))` (exist) or `O(n)` (not exist), where `s` is the count of the strings with the same length as they key.
    +/
    ref T require()(string key, lazy T value = T.init)
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
            }
            else
            {
                index = length;
            }
        }
        assert (index <= length);
        implementation.insertAt(key, value, index);
        index = implementation.indices[index];
        return implementation.values[index];
    }

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!int map = ["aa": 1];
        int add3(ref int x) { x += 3; return x; }
        assert(add3(map.require("aa", 10)) == 4);
        assert(add3(map.require("bb", 10)) == 13);
        assert(map.require("a", 100));
        assert(map.require("aa") == 4);
        assert(map.require("bb") == 13);
        assert(map.keys == ["aa", "bb", "a"]);
    }

    /++
    Converts to a builtin associative array.

    Complexity: `O(n)`.
    +/
    template toAA()
    {
        static if (__traits(compiles, (ref const T a) { T b; b = a;}))
        {
            ///
            T[string] toAA()() const
            {
                T[string] ret;
                foreach (i; 0 .. length)
                {
                    ret[implementation.keys[i]] = implementation.values[i];
                }
                return ret;
            }
        }
        else
        {
            ///
            T[string] toAA()()
            {
                T[string] ret;
                foreach (i; 0 .. length)
                {
                    ret[implementation.keys[i]] = implementation.values[i];
                }
                return ret;
            }

            ///
            const(T)[string] toAA()() const
            {
                const(T)[string] ret;
                foreach (i; 0 .. length)
                {
                    ret[implementation.keys[i]] = implementation.values[i];
                }
                return ret;
            }
        }
    }

    ///
    @safe pure nothrow unittest
    {
        StringMap!int map = ["k": 1];
        int[string] aa = map.toAA;
        assert(aa["k"] == 1);
    }
}

version(mir_test)
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

    assert(table == table);
}

version(mir_test)
///
@safe unittest
{
    static void testEquals(X, Y)()
    {
        X x;
        Y y;
        assert(x == y);

        x["L"] = 3;
        assert(x != y);
        x["A"] = 2;
        assert(x != y);
        x["val"] = 1;
        assert(x != y);

        y["L"] = 3;
        assert(x != y);
        y["A"] = 2;
        assert(x != y);
        y["val"] = 1;
        assert(x == y);

        x = X.init;
        assert(x != y);

        y = Y.init;
        assert(x == y);
    }

    testEquals!(StringMap!int, StringMap!uint)();
    testEquals!(StringMap!int, uint[string])();
    testEquals!(uint[string], StringMap!int)();
}

private struct StructImpl(T, U = uint)
    if (!__traits(hasMember, T, "opPostMove") && __traits(isUnsigned, U))
{
    import core.lifetime: move;

    size_t _length;
    string* _keys;
    T* _values;
    U* _indices;
    U[] _lengthTable;

    /++
    +/
    this()(string[] keys, T[] values) @trusted pure nothrow
    {
        import mir.array.allocation: array;
        import mir.ndslice.sorting: makeIndex;
        import mir.ndslice.topology: iota, indexed;
        import mir.string_table: smallerStringFirst;

        assert(keys.length == values.length);
        if (keys.length == 0)
            return;
        _length = keys.length;
        _keys = keys.ptr;
        _values = values.ptr;
        _indices = keys.makeIndex!(U, smallerStringFirst).ptr;
        auto sortedKeys = _keys.indexed(indices);
        size_t maxKeyLength = sortedKeys[$ - 1].length;
        _lengthTable = new U[maxKeyLength + 2];

        size_t ski;
        foreach (length; 0 .. maxKeyLength + 1)
        {
            while(ski < sortedKeys.length && sortedKeys[ski].length == length)
                ski++;
            _lengthTable[length + 1] = cast(U)ski;
        }
    }

    void insertAt()(string key, T value, size_t i) @trusted
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

    void removeAt()(size_t i)
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
                import mir.conv: emplaceRef;
                destroy!false(_values[j]);
                memmove(_keys + j, _keys + j + 1, (length - 1 - j) * string.sizeof);
                memmove(_values + j, _values + j + 1, (length - 1 - j) * T.sizeof);
                emplaceRef(_values[length - 1]);
            }
        }
        _length--;
        _lengthTable = _lengthTable[0 .. length ? _keys[_indices[length - 1]].length + 2 : 0];
    }

    size_t length()() @safe pure nothrow @nogc const @property
    {
        return _length;
    }

    inout(string)[] keys()() @trusted inout @property
    {
        return _keys[0 .. _length];
    }

    inout(T)[] values()() @trusted inout @property
    {
        return _values[0 .. _length];
    }

    inout(U)[] indices()() @trusted inout @property
    {
        return _indices[0 .. _length];
    }

    inout(U)[] lengthTable()() @trusted inout @property
    {
        return _lengthTable;
    }

    auto sortedKeys()() @trusted const @property
    {
        import mir.ndslice.topology: indexed;
        return _keys.indexed(indices);
    }

    bool findIndex()(scope const(char)[] key, ref size_t index) @trusted pure nothrow @nogc const
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
                const mid = (low + high) / 2;

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

version(mir_test)
@safe unittest
{
    import mir.algebraic_alias.json: JsonAlgebraic;
    import mir.string_map: StringMap;

    StringMap!JsonAlgebraic token;
    token[`access_token`] = "secret-data";
    token[`expires_in`] = 3599;
    token[`token_type`] = "Bearer";

    assert(token[`access_token`] == "secret-data");
    assert(token[`expires_in`] == 3599);
    assert(token[`token_type`] == "Bearer"); // mir/string_map.d(511): No member: token_type

    const tkType = `token_type` in token;

    assert((*tkType) == "Bearer"); // *tkType contains value 3599
}
