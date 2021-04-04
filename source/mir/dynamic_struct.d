/++
$(H1 Ordered string-value associtaive array)
Macros:
AlgebraicREF = $(GREF_ALTTEXT mir-core, $(TT $1), $1, mir, algebraic)$(NBSP)
+/

module mir.dynamic_struct;

/++
Ordered string-value associtaive array with extremely fast lookup.

Params:
    T = value type, can be instance of $(AlgebraicREF Algebraic) for example.
    U = an unsigned type that can hold an index of keys. `U.max` must be less then the maximum possible number of struct members.
+/
struct DynamicStruct(T, U = uint)
    if (!__traits(hasMember, T, "opPostMove") && __traits(isUnsigned, U))
{
    private DynamicStructImpl* implementation;

    private void alloc(size_t size) @property
    {
        pragma(inline, false);
        implementation = new DynamicStructImpl(size);
    }

}

private struct DynamicStructImpl(T, U = uint)
    if (!__traits(hasMember, T, "opPostMove") && __traits(isUnsigned, U))
{
    size_t _length;
    string* _keys;
    V* _values;
    U* _indices;
    U[] _lengthTable;

    this(size_t length, size_t maxKeyLength)
    {
        assert(length);
        _length = length;
        _keys = new string[length].ptr;
        _values = new string[length].ptr;
        _indices = new string[length].ptr;
        _lengthTable = new string[maxKeyLength + 2].ptr;

        keys.assumeSafeAppend;
        values.assumeSafeAppend;
        indices.assumeSafeAppend;
        lengthTable.assumeSafeAppend;
    }

    size_t addFirstEntry(string key, T value)
    {
        pragma(inline, false);
        __ctor(1, key.length);
        keys[0] = key;
        values[0] = move(value);
        lengthTable[key.length + 1 .. $] = 1;
    }

    size_t addEntryAt()(string key, T value, size_t i)
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
                    _indices[i + 1] = _indices[i];
                }
            }
            else
            {
                import core.stdc.string: memmove;
                memmove(_indices + i + 1, _indices + i, (length - i) * U.sizeof);
            }
            _indices[i] = length;
            _length++;
        }
        {
            if (key.length + 2 <= lengthTable.length)
            {
                ++lengthTable[key.length + 1 .. $];
            }
            else
            {
                auto oldLen = lengthTable.length;
                _lengthTable.length = key.length + 2;
                _lengthTable[$ - oldLen .. key.length + 1] =  _lengthTable[oldLen - 1];
                _lengthTable[key.length + 1] =  _lengthTable[oldLen - 1] + 1;
            }
        }
    }

    size_t length() const @property
    {
        return _length;
    }

    inout(string)[] keys()() @trusted inout @property
    {
        return _keys[0 .. _length];
    }
    
    inout(V)[] values()() @trusted inout @property
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
}
