/++
$(H1 Thread-safe reference-counted arrays and iterators).
+/
module mir.rc.array;

import mir.primitives: hasLength;
import mir.qualifier;
import mir.rc.context;
import mir.type_info;
import std.traits;

private static immutable allocationExcMsg = "mir_rcarray: out of memory error.";

version (D_Exceptions)
{
    import core.exception: OutOfMemoryError;
    private static immutable allocationError = new OutOfMemoryError(allocationExcMsg);
}

/++
Thread safe reference counting array.

`__xdtor` if any is used to destruct objects.

The implementation never adds roots into the GC.
+/
struct mir_rcarray(T)
{
    ///
    private T* _payload;
    private ref inout(mir_rc_context) context() inout scope return pure nothrow @nogc @trusted @property
    {
        assert(_payload);
        return (cast(inout(mir_rc_context)*)_payload)[-1];
    }
    private void _reset() { _payload = null; }

    private alias ThisTemplate = .mir_rcarray;
    private alias _thisPtr = _payload;

    ///
    void proxySwap(ref scope typeof(this) rhs) scope pure nothrow @nogc @trusted
    {
        auto t = this._payload;
        this._payload = rhs._payload;
        rhs._payload = t;
    }

    ///
    mixin CommonRCImpl;

    ///
    size_t length() @safe scope pure nothrow @nogc const @property
    {
        return _payload !is null ? context.length : 0;
    }

    ///
    inout(T)* ptr() @safe scope inout return
    {
        return _payload;
    }

    ///
    ref inout(T) opIndex(size_t i) @trusted scope inout return
    {
        assert(_payload);
        assert(i < context.length);
        return _payload[i];
    }

    ///
    inout(T)[] opIndex() @trusted scope inout return
    {
        return _payload !is null ?  _payload[0 .. context.length] : null;
    }

    ///
    size_t opDollar(size_t pos : 0)() @safe scope pure nothrow @nogc const
    {
        return length;
    }

    ///
    auto asSlice() @property @safe
    {
        import mir.ndslice.slice: mir_slice;
        alias It = mir_rci!T;
        return mir_slice!It([length], It(_payload, this));
    }

    /// ditto
    auto asSlice(size_t N)(size_t[N] lengths...) @safe
        if (N)
    {
        import mir.ndslice.internal: lengthsProduct;
        import mir.ndslice.slice: mir_slice;
        alias It = mir_rci!T;

        assert (lengths.lengthsProduct == length);

        auto _lengths = lengths;
        return mir_slice!(It, N)(_lengths, It(_payload, this));
    }

    private Unqual!T[] _init_(size_t length, scope Unqual!T* initValue, bool initialize, bool deallocate) @trusted pure nothrow @nogc
    {
        static if (is(T == class) || is(T == interface))
            auto ctx = mir_rc_create(mir_get_type_info!T, length, initValue, initialize, deallocate);
        else
            auto ctx = mir_rc_create(mir_get_type_info!T, length, initValue ? initValue : mir_get_payload_ptr!T, initialize, deallocate);
        if (!ctx)
        {
            version(D_Exceptions)
                throw allocationError;
            else
                assert(0, allocationExcMsg);
        }
        _payload = cast(T*)(ctx + 1);
        return cast(Unqual!T[])_payload[0 .. length];
    }

    /++
    Params:
        length = array length
        initialize = Flag, don't initialize memory with default value if `false`.
        deallocate = Flag, never deallocates memory if `false`.
    +/
    this(size_t length, bool initialize = true, bool deallocate = true) @safe @nogc pure nothrow
    {
        if (length == 0)
            return;
        _init_(length, null, initialize || hasElaborateAssign!T, deallocate);
    }

    /++
    Params:
        length = array length
        initValue = value to initialize with.
        deallocate = Flag, never deallocates memory if `false`.
    +/
    this(size_t length, scope Unqual!T* initValue, bool deallocate = true)
    {
        if (length == 0)
            return;
        auto ar = _init_(length, initValue, !hasElaborateDestructor!T, deallocate);
        static if (hasElaborateAssign!T)
        {
            foreach (ref e; ar)
            {
                import mir.conv: emplaceRef;
                emplaceRef!T(e, *initValue);
            }
        }
    }

    ///
    this(Range)(size_t length, ref Range range, bool deallocate = true)
        if (isIterable!Range && !isArray!Range)
    {
        if (length == 0)
            return;
        auto ar = _init_(length, null, !hasElaborateDestructor!T, deallocate);
        foreach (ref e; range)
        {
            import mir.conv: emplaceRef;
            assert(!ar.empty);
            emplaceRef!T(ar[0], e);
            ar = ar[1 .. $];
        }
        assert(ar.empty);
    }

    ///
    this(Range)(ref Range range, bool deallocate = true)
        if (isIterable!Range && !isArray!Range && hasLength!Range)
    {
        this(range.length, range, deallocate);
    }

    ///
    this(T[] array, bool deallocate = true)
    {
        if (length == 0)
            return;
        auto ar = _init_(length, null, !hasElaborateDestructor!T, deallocate);
        foreach (size_t i; 0 .. array.length)
        {
            import mir.conv: emplaceRef;
            emplaceRef!T(ar[i], array[i]);
        }
    }
}

/// ditto
alias RCArray = mir_rcarray;

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    auto a = RCArray!double(10);
    foreach(i, ref e; a)
        e = i;
    auto b = a;
    assert(b[$ - 1] == 9);
    foreach(i, ref e; b)
        assert(e == i);
    b[4] = 100;
    assert(a[4] == 100);

    import mir.ndslice.slice;

    auto s = a.asSlice; // as RC random access range (ndslice)
    static assert(is(typeof(s) == Slice!(RCI!double)));
    static assert(is(typeof(s) == mir_slice!(mir_rci!double)));

    auto r = a[]; // scope array
    static assert(is(typeof(r) == double[]));

    auto fs = r.sliced; // scope fast random access range (ndslice)
    static assert(is(typeof(fs) == Slice!(double*)));
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    RCArray!double a = rcarray!double(1.0, 2, 5, 3);
    assert(a[0] == 1);
    assert(a[$ - 1] == 3);

    auto s = rcarray!char("hello!");
    assert(s[0] == 'h');
    assert(s[$ - 1] == '!');

    alias rcstring = rcarray!(immutable char);
    auto r = rcstring("string");
    assert(r[0] == 's');
    assert(r[$ - 1] == 'g');
}

private template LikeArray(Range)
{
    static if (__traits(identifier, Range) == "mir_slice")
    {
        import mir.ndslice.slice;
        enum LikeArray = is(Range : Slice!(T*, N, kind), T, size_t N, SliceKind kind);
    }
    else
    {
        enum LikeArray = false;
    }
}

///
auto rcarray(T = void, Range)(ref Range range)
    if (is(T == void) && hasLength!Range && !is(Range == LightScopeOf!Range))
{
    return .rcarray(range.lightScope);
}

/// ditto
auto rcarray(T = void, Range)(Range range)
    if (is(T == void) && hasLength!Range && isIterable!Range && is(Range == LightScopeOf!Range) && !isArray!Range)
{
    static if (LikeArray!Range)
    {
        return .rcarray(range.field);
    }
    else
    {
        return .rcarray!(ForeachType!Range)(range);
    }
}

/// ditto
RCArray!V rcarray(T = void, V)(V[] values...)
    if (is(T == void) && hasIndirections!V)
{
    return .rcarray(values, true);
}

/// ditto
RCArray!V rcarray(T = void, V)(scope V[] values...)
    if (is(T == void) && !hasIndirections!V)
{
    return .rcarray(values, true);
}

/// ditto
RCArray!V rcarray(T = void, V)(V[] values, bool deallocate)
    if (is(T == void) && hasIndirections!V)
{
    return .rcarray!V(values);
}

/// ditto
RCArray!V rcarray(T = void, V)(scope V[] values, bool deallocate)
    if (is(T == void) && !hasIndirections!V)
{
    return .rcarray!V(values);
}

/++
+/
template rcarray(T)
    if(!is(T : E[], E) && !is(T == void))
{
    ///
    auto rcarray(Range)(ref Range range)
        if (hasLength!Range && !is(Range == LightScopeOf!Range))
    {
        return .rcarray!T(range.lightScope);
    }

    /// ditto
    auto rcarray(Range)(Range range)
        if (hasLength!Range && isIterable!Range && is(Range == LightScopeOf!Range) && !isArray!Range)
    {
        static if (LikeArray!Range)
        {
            return .rcarray!T(range.field);
        }
        else
        {
            auto ret = RCArray!T(range.length, false);
            import mir.conv: emplaceRef;
            static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move;
            size_t i;
            foreach(ref e; range)
                ret[i++].emplaceRef!T(e);
            return move(ret);
        }
    }

    /// ditto
    RCArray!T rcarray(V)(V[] values...)
        if (hasIndirections!V)
    {
        return .rcarray!T(values, true);
    }

    /// ditto
    RCArray!T rcarray(V)(scope V[] values...)
        if (!hasIndirections!V)
    {
        return .rcarray!T(values, true);
    }

    /// ditto
    RCArray!T rcarray(V)(V[] values, bool deallocate)
        if (hasIndirections!V)
    {
        auto ret = mir_rcarray!T(values.length, false, deallocate);
        static if (!hasElaborateAssign!T && is(Unqual!V == Unqual!T))
        {
            ()@trusted {
                import core.stdc.string: memcpy;
                memcpy(cast(void*)ret.ptr, cast(const void*)values.ptr, values.length * T.sizeof);
            }();
        }
        else
        {
            import  mir.conv: emplaceRef;
            auto lhs = ret[];
            foreach (i, ref e; values)
                lhs[i].emplaceRef!T(e);
        }
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        return move(ret);
    }

    /// ditto
    RCArray!T rcarray(V)(scope V[] values, bool deallocate)
        if (!hasIndirections!V)
    {
        auto ret = mir_rcarray!T(values.length, false);
        static if (!hasElaborateAssign!T && is(Unqual!V == Unqual!T))
        {
            ()@trusted {
                import core.stdc.string: memcpy;
                memcpy(cast(void*)ret.ptr, cast(const void*)values.ptr, values.length * T.sizeof);
            }();
        }
        else
        {
            import  mir.conv: emplaceRef;
            auto lhs = ret[];
            foreach (i, ref e; values)
                lhs[i].emplaceRef!T(e);
        }
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        return move(ret);
    }
}


/++
Params:
    length = array length
    deallocate = Flag, never deallocates memory if `false`.
Returns: minimally initialized rcarray.
+/
RCArray!T mininitRcarray(T)(size_t length, bool deallocate = true)
{
    return RCArray!T(length, false, deallocate);
}

///
@safe pure nothrow @nogc unittest
{
    auto a = mininitRcarray!double(5);
    assert(a.length == 5);
    assert(a._counter == 1);
    a[][] = 0; // a.opIndex()[] = 0;
}

/++
Thread safe reference counting iterator.
+/
struct mir_rci(T)
{
    ///
    T* _iterator;

    ///
    RCArray!T _array;

    ///
    inout(T)* lightScope() @safe scope return inout @property
    {
        debug {(() @trusted {
        {
            assert(_array._payload <= _iterator);
            assert(_iterator is null || _iterator <= _array._payload + _array.length);
        }})();}
        return _iterator;
    }

    ///
    ref opAssign(typeof(null)) @safe scope return nothrow
    {
        pragma(inline, true);
        _iterator = null;
        _array = null;
        return this;
    }

    ///
    ref opAssign(typeof(this) rhs) scope return
    {
        _iterator = rhs._iterator;
        _array.proxySwap(rhs._array);
        return this;
    }

    ///
    ref opAssign(Q)(mir_rci!Q rhs) scope return nothrow
        if (isImplicitlyConvertible!(Q*, T*))
    {
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        _iterator = rhs._iterator;
        _array = move(rhs._array);
        return this;
    }

    ///
    mir_rci!(const T) lightConst() @safe const nothrow @property
    { return typeof(return)(_iterator, _array.lightConst); }

    ///
    mir_rci!(immutable T) lightImmutable() @safe immutable nothrow @property
    { return typeof(return)(_iterator, _array.lightImmutable); }

    ///   
    ref inout(T) opUnary(string op : "*")() inout scope return
    {
        debug
        {
            assert(_iterator);
            assert(_array._payload);
            assert(_array._payload <= _iterator);
            assert(_iterator <= _array._payload + _array.length);
        }
        return *_iterator;
    }

    ///   
    ref inout(T) opIndex(ptrdiff_t index) inout scope return @trusted
    {
        debug
        {
            assert(_iterator);
            assert(_array._payload);
            assert(_array._payload <= _iterator + index);
            assert(_iterator + index <= _array._payload + _array.length);
        }
        return _iterator[index];
    }

    ///   
    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    { mixin(op ~ "_iterator;"); }

    ///   
    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index;"); }

    ///
    mir_rci!T opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    { return mir_rci!T(_iterator + index, _array); }

    ///   
    mir_rci!(const T) opBinary(string op)(ptrdiff_t index) const
        if (op == "+" || op == "-")
    { return mir_rci!T(_iterator + index, _array); }

    ///   
    mir_rci!(immutable T) opBinary(string op)(ptrdiff_t index) immutable
        if (op == "+" || op == "-")
    { return mir_rci!T(_iterator + index, _array); }

    ///   
    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return this._iterator - right._iterator; }

    ///   
    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterator == right._iterator; }

    ///   
    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    { return this._iterator - right._iterator; }
}

/// ditto
alias RCI = mir_rci;

///
version(mir_test)
@safe @nogc unittest
{
    import mir.ndslice.traits: isIterator;
    import mir.ndslice.slice;
    import mir.rc.array;
    auto array = mir_rcarray!double(10);
    auto slice = array.asSlice;
    static assert(isIterator!(RCI!double));
    static assert(is(typeof(slice) == Slice!(RCI!double)));
    auto matrix = slice.sliced(2, 5);
    static assert(is(typeof(matrix) == Slice!(RCI!double, 2)));
    array[7] = 44;
    assert(matrix[1, 2] == 44);
}

///
version(mir_test)
@safe @nogc unittest
{
    import mir.ndslice.slice;
    import mir.rc.array;

    alias rcvec = Slice!(RCI!double);

    RCI!double a, b;
    a = b;

    RCI!(const double) ca, cb;
    ca = cb;
    ca = cast(const) cb;

    void foo(scope ref rcvec x, scope ref rcvec y)
    {
        x[] = y[];
        x[1] = y[1];
        x[1 .. $] += y[1 .. $];
        x = x.save;
    }
}

version(mir_test)
@safe @nogc unittest
{
    import mir.ndslice;
    import mir.rc.array;
    import mir.series;

    @safe void bar(ref const mir_rcarray!(const double) a, ref mir_rcarray!(const double) b)
    {
        b = a;
    }

    @safe void bari(ref immutable mir_rcarray!(immutable double) a, ref mir_rcarray!(immutable double) b)
    {
        b = a;
    }

    @safe void foo(ref const RCI!(const double) a, ref RCI!(const double) b)
    {
        b = a;
    }

    @safe void fooi(ref immutable RCI!(immutable double) a, ref RCI!(immutable double) b)
    {
        b = a;
    }

    struct S
    {
        uint i;
        @safe pure:
        ~this() {}
    }

    @safe void goo(ref const Series!(RCI!(const double), RCI!(const S)) a, ref Series!(RCI!(const double), RCI!(const S)) b)
    {
        b = a;
    }

    @safe void gooi(ref immutable Series!(RCI!(immutable double), RCI!(const S)) a, ref Series!(RCI!(immutable double), RCI!(const S)) b)
    {
        b = a;
    }

    struct C
    {
        Series!(RCI!(const S), RCI!(const S)) a;
        Series!(RCI!(const S), RCI!(const S)) b;
    }

    C a, b;
    a = b;
    a = cast(const) b;
}

version(mir_test)
unittest
{
    import mir.ndslice.slice: Slice;
    static RCArray!int foo() @safe
    {
        auto ret = RCArray!int(10);
        return ret;
    }


    static Slice!(RCI!int) bat() @safe
    {
        auto ret = RCArray!int(10);
        return ret.asSlice;
    }

    static Slice!(RCI!int) bar() @safe
    {
        auto ret = RCArray!int(10);
        auto d = ret.asSlice;
        return d;
    }
}

version(mir_test)
@safe unittest
{
    import core.stdc.stdio;

    struct S
    {
        uint s;
        this(this) @nogc nothrow @safe
        {
            // () @trusted {
            //     puts("this(this)\n");
            // } ();
        }

        ~this() nothrow @nogc @safe
        {
            // () @trusted {
            // if (s)
            //     puts("~this()\n");
            // else
            //     puts("~this() - zero\n");
            // } ();
        }
    }

    struct C
    {
        S s;
    }

    S[1] d = [S(1)];
    auto r = rcarray(d);
}
