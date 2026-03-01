/++
$(H1 Ordered string-value associative array)
Macros:
AlgebraicREF = $(GREF_ALTTEXT mir-core, $(TT $1), $1, mir, algebraic)$(NBSP)
+/

module mir.string_map;

import std.traits;
import mir.internal.meta: basicElementType;

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

private alias U = uint;

/++
Ordered string-value associative array with extremely fast lookup.

Params:
    T = mutable value type, can be instance of $(AlgebraicREF Algebraic) for example.
    U = an unsigned type that can hold an index of keys. `U.max` must be less then the maximum possible number of struct members.
+/
struct StringMap(T)
    // if (!is(typeof(T.opPostMove)))
{
    import mir.utility: _expect;
    import core.lifetime: move;
    import mir.conv: emplaceRef;
    import mir.algebraic: Algebraic;

    ///
    static struct KeyValue
    {
        ///
        string key;
        ///
        T value;
    }

    /// `hashOf` Implementation. Doesn't depend on order
    static if (is(T == Algebraic!Union, Union) && is(Union == union))
    size_t toHash() scope @trusted const nothrow pure @nogc
    {
        if (implementation is null)
            return 0;
        size_t hash;
        foreach (i, index; implementation.indices)
        {
            hash = hashOf(implementation._keys[index], hash);
            static if (__traits(hasMember, T, "toHash"))
               hash = hashOf(implementation._values[index].toHash, hash);
            else
               hash = hashOf(implementation._values[index], hash);
        }
        return hash;
    }
    else
    size_t toHash() scope @trusted const nothrow // pure @nogc
    {
        if (implementation is null)
            return 0;
        size_t hash;
        foreach (i, index; implementation.indices)
        {
            hash = hashOf(implementation._keys[index], hash);
            static if (__traits(hasMember, T, "toHash"))
               hash = hashOf(implementation._values[index].toHash, hash);
            else
               hash = hashOf(implementation._values[index], hash);
        }
        return hash;
    }

    /// `==` implementation. Doesn't depend on order
    // current implementation is workaround for linking bugs when used in self referencing algebraic types
    bool opEquals(V)(scope const StringMap!V rhs) scope const @trusted pure @nogc nothrow
    {
        import std.traits: isAggregateType;
        // NOTE: moving this to template restriction fails with recursive template instanation
        if (implementation is null)
            return rhs.length == 0;
        if (rhs.implementation is null)
            return length == 0;
        if (implementation._length != rhs.implementation._length)
            return false;
        foreach (const i, const index; implementation.indices)
            if (implementation._keys[index] != rhs.implementation._keys[rhs.implementation._indices[i]] ||
                implementation._values[index] != rhs.implementation._values[rhs.implementation._indices[i]])
                return false;
        return true;
    }

    /// ditto
    bool opEquals(K, V)(scope const const(V)[const(K)] rhs) scope const
    if (is(typeof(K.init == string.init) : bool) &&
        is(typeof(V.init == T.init) : bool))
    {
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
    Reset the associative array
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
    Initialize the associative array with default value.
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
    string toString()() const scope
    {
        import mir.format: stringBuf;
        stringBuf buffer;
        toString(buffer);
        return buffer.data.idup;
    }

    ///ditto
    void toString(W)(ref scope W w) const scope
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

    /++
    Returns: number of elements in the table.
    +/
    bool empty()() @safe pure nothrow @nogc const @property
    {
        return !implementation || implementation.length == 0;
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

    The keys returned are guaranteed to be in the ordered inserted as long as no
    key removals followed by at least one key insertion has been performed.

    Complexity: `O(1)`
    +/
    const(string)[] keys()() @safe pure nothrow @nogc const @property
    {
        return implementation ? implementation.keys : null;
    }
    ///
    alias byKey = keys;

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

    The values returned are guaranteed to be in the ordered inserted as long as no
    key removals followed by at least one key insertion has been performed.

    Complexity: `O(1)`
    +/
    inout(T)[] values()() @safe pure nothrow @nogc inout @property
    {
        return implementation ? implementation.values : null;
    }

    /// ditto
    alias byValue = values;

    version(mir_test) static if (is(T == int))
    ///
    @safe pure unittest
    {
        StringMap!double map;
        assert(map.byKeyValue == StringMap!double.KeyValue[].init);
        map["c"] = 4.0;
        map["a"] = 3.0;
        assert(map.byKeyValue == [StringMap!double.KeyValue("c", 4.0), StringMap!double.KeyValue("a", 3.0)]);
    }

    /** Return a range over all elements (key-values pairs) currently stored in the associative array.

        The elements returned are guaranteed to be in the ordered inserted as
        long as no key removals nor no value mutations has been performed.
    */
    auto byKeyValue(this This)() @trusted pure nothrow @nogc
    {
        import mir.ndslice.topology: map;
        return this.opIndex.map!KeyValue;
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

    ///
    auto opIndex(this This)() @trusted pure nothrow @nogc
    {
        import mir.ndslice.topology: zip;
        return keys.zip(values);
    }

    ///
    auto dup(this This)() @trusted
    {
        return StringMap(keys.dup, values.dup);
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
    ref inout(T) opIndex()(scope const(char)[] key) @trusted pure inout nothrow @nogc
    {
        size_t index;
        if (implementation && implementation.findIndex(key, index))
        {
            assert (index < length);
            index = implementation._indices[index];
            assert (index < length);
            return implementation._values[index];
        }
        import core.exception : onRangeError;
        onRangeError();
        return implementation._values[0]; // TODO: remove when onRangeError is noreturn
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
                    move(cast()value, cast()(implementation._values[index]));
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
        implementation.insertAt(key, move(cast()value), index);
        index = implementation._indices[index];
        return implementation._values[index];
    }

    /++
    Looks up key; if it exists returns corresponding value else evaluates and returns defaultValue.

    Complexity: `O(log(s))`, where `s` is the number of the keys with the same length as the input key.
    +/
    inout(T) get()(scope const(char)[] key, lazy inout(T) defaultValue) inout
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
    version(mir_test) static if (is(T == int))
    @safe pure nothrow unittest
    {
        StringMap!int map = ["k": 1];
        int[string] aa = map.toAA;
        assert(aa["k"] == 1);
    }

    private static struct Impl
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
        this()(string[] keys, T[] values) @trusted pure nothrow
        {
            assert(keys.length == values.length);
            if (keys.length == 0)
                return;
            _length = keys.length;
            _keys = keys.ptr;
            _values = values.ptr;
            _indices = new U[keys.length].ptr;
            size_t maxKeyLength;
            foreach(ref key; keys)
                if (key.length > maxKeyLength)
                    maxKeyLength = key.length;
            _lengthTable = new U[maxKeyLength + 2];
            sortIndices();
        }

        private void sortIndices() pure nothrow
        {
            import mir.ndslice.sorting: sort;
            import mir.ndslice.topology: indexed;
            import mir.string_table: smallerStringFirst;
            foreach (i, ref index; indices)
                index = cast(U)i;

            indices.sort!((a, b) => smallerStringFirst(keys[a], keys[b]));
            auto sortedKeys = _keys.indexed(indices);
            size_t maxKeyLength = sortedKeys[$ - 1].length;

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
                a ~= move(cast()value);
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

        inout(string)[] keys()() @trusted inout @property pure @nogc nothrow
        {
            return _keys[0 .. _length];
        }

        inout(T)[] values()() @trusted inout @property pure @nogc nothrow
        {
            return _values[0 .. _length];
        }

        inout(U)[] indices()() @trusted inout @property pure @nogc nothrow
        {
            return _indices[0 .. _length];
        }

        inout(U)[] lengthTable()() @trusted inout @property pure @nogc nothrow
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

    /// Sorts table according to the keys
    ref sort(alias less = "a < b")() return
    {
        import mir.functional: naryFun;
        import mir.ndslice.sorting: sort;
        import mir.ndslice.topology: zip;
        if (length) {
            zip(implementation.keys, implementation.values).sort!((l, r) => naryFun!less(l.a, r.a));
            implementation.sortIndices;
        }
        return this;
    }

    import std.traits: isAssociativeArray, isAggregateType;
    // static if (!isAssociativeArray!(.basicElementType!T) && (!isAggregateType!(.basicElementType!T) || __traits(hasMember, .basicElementType!T, "opCmp")))
    /// `opCmp` Implementation. Doesn't depend on order
    int opCmp()(scope const typeof(this) rhs) scope const @trusted // pure nothrow @nogc
    {
        if (sizediff_t d = length - rhs.length)
            return d < 0 ? -1 : 1;
        if (length == 0)
            return 0;

        foreach (i, index; implementation.indices)
            if (auto d = __cmp(implementation._keys[index], rhs.implementation._keys[rhs.implementation._indices[i]]))
                return d;
        foreach (i, index; implementation.indices)
            static if (__traits(compiles, __cmp(implementation._values[index], rhs.implementation._values[rhs.implementation._indices[i]])))
            {
                if (auto d = __cmp(implementation._values[index], rhs.implementation._values[rhs.implementation._indices[i]]))
                    return d;
            }
            else
            static if (__traits(hasMember, T, "opCmp"))
            {
                if (auto d = implementation._values[index].opCmp(rhs.implementation._values[rhs.implementation._indices[i]]))
                    return d;
            }
            else
            {
                return
                    implementation._values[index] < rhs.implementation._values[rhs.implementation._indices[i]] ? -1 :
                    implementation._values[index] > rhs.implementation._values[rhs.implementation._indices[i]] ? +1 : 0;
            }
        return false;
    }

    private Impl* implementation;

    ///
    static if (is(T == const) || is(T == immutable))
    {
        alias serdeKeysProxy = Unqual!T;
    }
    else
    {
        alias serdeKeysProxy = T;
    }
}

version(mir_test)
///
@safe unittest
{
    class C
    {
        this(int x) { this.x = x; }
        int x;
        bool opEquals(scope const C rhs) const scope @safe pure nothrow @nogc
        {
            return x == rhs.x;
        }

        override size_t toHash() @safe const scope pure nothrow @nogc
        {
            return x;
        }
    }
    StringMap!(const C) table;
    const v0 = new C(42);
    const v1 = new C(43);
    table["0"] = v0;
    table["1"] = v1;
    assert(table.keys == ["0", "1"]);
    assert(table.values == [v0, v1]); // TODO: qualify unittest as `pure` when this is inferred `pure`
    static assert(is(typeof(table.values) == const(C)[]));
}

version(mir_test)
///
@safe pure unittest
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

    // sorting
    table["A"] = 2;
    table.sort;
    assert(table.keys == ["A", "L", "val"]);
    assert(table.values == [2, 3, 11]);
    assert(table["A"] == 2);
    assert(table["L"] == 3);
    assert(table["val"] == 11);
}

version(mir_test)
///
@safe pure unittest
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

        y["val"] = 1;
        assert(x != y);
        y["L"] = 3;
        assert(x != y);
        y["A"] = 2;
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

version(mir_test)
@safe pure unittest
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

///
template intersectionMap(alias merger)
{
    ///
    StringMap!V intersectionMap(V)(StringMap!V a, StringMap!V b)
    {
        import mir.functional : naryFun;
        typeof(return) res;
        foreach (key, ref value; a)
            if (auto bValPtr = key in b)
                res[key] = naryFun!merger(value, *bValPtr);
        return res;
    }
}

///
version(mir_test)
@safe pure
unittest {
    import mir.test: should;
    import mir.string_map : StringMap;
    auto m0 = StringMap!int(["foo", "bar"], [1, 2]);
    auto m1 = StringMap!int(["foo"], [2]);
    auto m2 = StringMap!int(["foo"], [3]);
    intersectionMap!"a + b"(m0, m1).should == m2;
}

///
template unionMap(alias merger)
{
    ///
    StringMap!V unionMap(V)(StringMap!V a, StringMap!V b)
    {
        import mir.functional : naryFun;
        typeof(return) res;
        foreach (key, ref value; a)
            if (auto bValPtr = key in b)
                res[key] = naryFun!merger(value, *bValPtr);
            else
                res[key] = value;
        foreach (key, ref value; b)
            if (key !in res)
                res[key] = value;
        return res;
    }
}

///
version(mir_test)
@safe pure
unittest {
    import mir.test: should;
    import mir.string_map : StringMap;
    auto m0 = StringMap!int(["foo", "bar"], [1, 2]);
    auto m1 = StringMap!int(["foo"], [2]);
    auto m2 = StringMap!int(["foo", "bar"], [3, 2]);
    unionMap!"a + b"(m0, m1).should == m2;
}
