/++
$(H1 Scoped Buffer)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko
+/
module mir.appender;

// import std.traits: isAssignable, hasElaborateDestructorhasElaborateCopyConstructor, hasElaborateAssign;
import mir.conv: _mir_destroy = xdestroy;

private extern(C) @system nothrow @nogc pure void* memcpy(scope void* s1, scope const void* s2, size_t n);

/++
The buffer uses stack memory and C Runtime to allocate temporal memory.

Shouldn't store references to GC allocated data.
+/
struct ScopedBuffer(T, size_t bytes = 4096)
    if (bytes && T.sizeof <= bytes)
{
    import std.traits: Unqual, isMutable, isIterable, hasElaborateAssign, isAssignable, isArray;
    import mir.primitives: hasLength;
    import mir.conv: emplaceRef;

    private enum size_t _bufferLength =  bytes / T.sizeof + (bytes % T.sizeof != 0);
    private T[] _buffer;
    size_t _currentLength;
    bool _heapAllocated;

    version (mir_secure_memory)
        private align(T.alignof) ubyte[_bufferLength * T.sizeof] _scopeBufferPayload;
    else
        private align(T.alignof) ubyte[_bufferLength * T.sizeof] _scopeBufferPayload = void;

    private ref inout(T[_bufferLength]) _scopeBuffer() inout @trusted scope
    {
        return *cast(inout(T[_bufferLength])*)&_scopeBufferPayload;
    }

    ///
    T[] reserve(size_t n) @system return scope
    {
        import mir.internal.memory: realloc, malloc;
        auto newLength = _currentLength + n;
        if (newLength > _buffer.length)
        {
            if (!_heapAllocated)
            {
                    auto newLen = newLength << 1;
                    if (auto p = malloc(T.sizeof * newLen))
                    {
                        _heapAllocated = true;
                        _buffer = (cast(T*)p)[0 .. newLen];
                    }
                    else assert(0);
                    version (mir_secure_memory)
                    {
                        (cast(ubyte[])_buffer)[] = 0;
                    }
                    memcpy(cast(void*)_buffer.ptr, _scopeBuffer.ptr, T.sizeof * (newLength - n));
            }
            else
            {
                auto newLen = newLength << 1;
                _buffer = (cast(T*)realloc(cast(void*)_buffer.ptr, T.sizeof * newLen))[0 .. newLen];
                version (mir_secure_memory)
                {
                    (cast(ubyte[])_buffer[newLength .. $])[] = 0;
                }
            }
        }
        return _buffer[_currentLength .. newLength];
    }

    ///
    T[] prepare(size_t n) @trusted return scope
    {
        reserve(n);
        _currentLength += n;
        return data;
    }

    static if (isAssignable!(T, const T))
        private alias R = const T;
    else
        private alias R = T;

    static if (isMutable!T && !hasElaborateAssign!T)
    {
        /// Copy constructor is enabled only if `T` is mutable type without eleborate assign.
        this(this)
        {
            import mir.internal.memory: malloc;
            if (_heapAllocated)
            {
                typeof(_buffer) buffer;
                if (auto p = malloc(T.sizeof * _buffer.length))
                {
                    buffer = (cast(T*)p)[0 .. T.sizeof * _buffer.length];
                }
                else assert(0);
                version (mir_secure_memory)
                {
                    (cast(ubyte[])buffer)[] = 0;
                }
                buffer[0 .. _currentLength] = _buffer[0 .. _currentLength];
                _buffer = buffer;
            }
        }
    }
    else
    {
        @disable this(this);
    }

    ///
    ~this()
    {
        import mir.internal.memory: free;
        data._mir_destroy;
        version(mir_secure_memory)
            _currentLength = 0;
        if (!__ctfe)
            (() @trusted { if (_heapAllocated) free(cast(void*)_buffer.ptr); })();
    }

    ///
    void shrinkTo(size_t length)
    {
        assert(length <= _currentLength);
        data[length .. _currentLength]._mir_destroy;
        _currentLength = length;
    }

    ///
    size_t length() scope const @property
    {
        return _currentLength;
    }

    ///
    void popBackN(size_t n)
    {
        sizediff_t t = _currentLength - n;
        if (t < 0)
            assert(0, "ScopedBffer.popBackN: n is too large.");
        data[t .. _currentLength]._mir_destroy;
        _currentLength = t;
    }

    ///
    void put(T e) @safe scope
    {
        auto cl = _currentLength;
        auto d = prepare(1);
        static if (isMutable!T)
        {
            import core.lifetime: moveEmplace;
            ()@trusted{moveEmplace(e, d[cl]);}();
        }
        else
        {
            emplaceRef!(Unqual!T)(d[cl], e);
        }
    }

    static if (T.sizeof > 8 || hasElaborateAssign!T)
    ///
    void put(ref R e) scope
    {
        auto cl = _currentLength;
        auto d = prepare(1);
        emplaceRef!(Unqual!T)(d[cl], e);
    }

    static if (!hasElaborateAssign!T)
    ///
    void put(scope R[] e) scope
    {
        auto cl = _currentLength;
        auto d = prepare(e.length);
        if (!__ctfe)
            (()@trusted=>memcpy(cast(void*)(d.ptr + cl), e.ptr, e.length * T.sizeof))();
        else
            static if (isMutable!T)
                (()@trusted=> d[cl .. cl + e.length] = e)();
            else
                assert(0);
    }

    ///
    void put(Iterable)(Iterable range) scope
        if (isIterable!Iterable && !__traits(isStaticArray, Iterable) && (!isArray!Iterable || hasElaborateAssign!T))
    {
        static if (hasLength!Iterable)
        {
            auto cl = _currentLength;
            auto d = prepare(range.length);
            foreach(ref e; range)
                emplaceRef!(Unqual!T)(d[cl++], e);
            assert(_currentLength == cl);
        }
        else
        {
            foreach(ref e; range)
                put(e);
        }
    }

    ///
    void reset() scope nothrow
    {
        this.__dtor;
        _currentLength = 0;
        _buffer = null;
    }

    ///
    void initialize() @system scope nothrow @nogc
    {
        _heapAllocated = false;
        _currentLength = 0;
        _buffer = cast(T[]) _scopeBufferPayload;
    }

    ///
    inout(T)[] data() inout @property @trusted return scope
    {
        return _buffer[0 .. _currentLength];
    }

    /++
    Copies data into an array of the same length using `memcpy` C routine.
    Shrinks the length to `0`.
    +/
    void moveDataAndEmplaceTo(T[] array) @system
    in {
        assert(array.length == _currentLength);
    }
    do {
        memcpy(cast(void*)array.ptr, data.ptr, _currentLength * T.sizeof);
        _currentLength = 0;
    }
}

/// ditto
auto scopedBuffer(T, size_t bytes = 4096)() @trusted
{
    ScopedBuffer!(T, bytes) buffer = void;
    buffer.initialize;
    return buffer;
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto buf = scopedBuffer!char;
    buf.put('c');
    buf.put("str");
    assert(buf.data == "cstr");

    buf.popBackN(2);
    assert(buf.data == "cs");
}

/// immutable
@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto buf = scopedBuffer!(immutable char);
    buf.put('c');
    buf.put("str");
    assert(buf.data == "cstr");

    buf.popBackN(2);
    assert(buf.data == "cs");
}

@safe pure nothrow @nogc
version (mir_test) unittest
{
    auto buf = scopedBuffer!(char, 3);
    buf.put('c');
    buf.put("str");
    assert(buf.data == "cstr");

    buf.popBackN(2);
    assert(buf.data == "cs");
}

///
struct UnsafeArrayBuffer(T)
{
    import std.traits: isImplicitlyConvertible;

    ///
    T[] buffer;
    ///
    size_t length;

    ///
    void put(T a)
    {
        import core.lifetime: move;
        assert(length < buffer.length);
        buffer[length++] = move(a);
    }

    static if (isImplicitlyConvertible!(const T, T))
        private alias E = const T;
    else
        private alias E = T;

    ///
    void put(E[] a)
    {
        import core.lifetime: move;
        assert(buffer.length >= a.length + length);
        buffer[length .. length + a.length] = a;
        length += a.length;
    }

    ///
    inout(T)[] data() inout @property @safe scope
    {
        return buffer[0 .. length];
    }

    ///
    void popBackN(size_t n)
    {
        sizediff_t t = length - n;
        if (t < 0)
            assert(0, "UnsafeBuffer.popBackN: n is too large.");
        buffer[t .. length]._mir_destroy;
        length = t;
    }
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    char[4] array;
    auto buf = UnsafeArrayBuffer!char(array);
    buf.put('c');
    buf.put("str");
    assert(buf.data == "cstr");

    buf.popBackN(2);
    assert(buf.data == "cs");
}

version(mir_bignum_test) // for DIP1000
@safe pure nothrow
unittest
{
    import mir.conv: to;
    import mir.algebraic : Algebraic;
    static struct S
    {
    @safe pure nothrow @nogc:
        @property string toString() const
        {
            return "_";
        }
    }
    Algebraic!(int, string, double) x;
    x = 42;
    auto s = x.to!string;
    assert(s == "42");
    x = "abc";
    assert(x.to!string == "abc");
    x = 42.0;
    assert(x.to!string == "42.0");
    Algebraic!S y;
    y = S();
    assert(y.to!string == "_");
}
