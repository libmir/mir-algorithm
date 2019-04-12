/++
$(H1 Thread-safe reference-counted arrays and iterators).
+/
module mir.rcarray;

import mir.shared_ptr:
    mir_rcarray_context,
    mir_rcarray_increase_counter,
    mir_rcarray_decrease_counter,
    cppSupport,
    _freeImpl,
    CommonRCImpl;

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
struct mir_rcarray(T, bool cppSupport = .cppSupport!T)
{
    import std.traits;
    import mir.ndslice.slice: Slice, SliceKind, Contiguous;

    ///
    private T* _payload;
    private ref inout(mir_rcarray_context) context() inout scope return pure nothrow @nogc @trusted @property
    {
        assert(_payload);
        return (cast(inout(mir_rcarray_context)*)_payload)[-1];
    }
    private void _reset() { _payload = null; }

    private alias ThisTemplate = .mir_rcarray;
    private alias _thisPtr = _payload;

    ///
    void proxySwap(ref typeof(this) rhs) pure nothrow @nogc @safe
    {
        auto t = this._payload;
        this._payload = rhs._payload;
        rhs._payload = t;
    }

    ///
    mixin CommonRCImpl;

    ///
    size_t length() @trusted scope pure nothrow @nogc const @property
    {
        return _payload !is null ? context.length : 0;
    }

    ///
    inout(T)* ptr() @system scope inout
    {
        return _payload;
    }

    ///
    ref opIndex(size_t i) @trusted scope inout
    {
        assert(_payload);
        assert(i < context.length);
        return _payload[i];
    }

    ///
    inout(T)[] opIndex() @trusted scope inout
    {
        return _payload !is null ?  _payload[0 .. context.length] : null;
    }

    size_t opDollar(size_t pos : 0)() @trusted scope pure nothrow @nogc const
    {
        return _payload !is null ? context.length : 0;
    }

    static if (cppSupport)
    {
    extern(C++):
        pragma(inline, false)
        private bool __initialize(size_t length, bool deallocate, bool initialize) scope @system nothrow @nogc
        {
            return initializeImpl(length, deallocate, initialize);
        }

        ///
        auto asSlice() scope return @property
        {
            alias It = mir_rci!T;
            static if (cppSupport != .cppSupport!T)
                return Slice!It([length], It((()@trusted => ptr)(), *cast(mir_rcarray!(T, false)*) &this));
            else
                return Slice!It([length], It((()@trusted => ptr)(), this));
        }
    }
    else
    {
        pragma(inline, false)
        private bool __initialize(size_t length, bool deallocate, bool initialize) scope @system nothrow @nogc
        {
            return initializeImpl(length, deallocate, initialize);
        }

        ///
        auto asSlice() scope return @property
        {
            alias It = mir_rci!T;
            return Slice!It([length], It((()@trusted => ptr)(), this));
        }
    }

    /++
    Params:
        length = array length
        deallocate = Flag, never deallocates memory if `false`.
        initialize = Flag, don't initialize memory with default value if `false`.
    +/
    this(size_t length, bool deallocate = true, bool initialize = true) @trusted @nogc
    {
        if (!this.__initialize(length, deallocate, initialize))
        {
            version(D_Exceptions)
            {
                throw allocationError;
            }
            else
            {
                assert(0, allocationExcMsg);
            }
        }
    }

    /++
    Params:
        length = array length
        deallocate = Flag, never deallocates memory if `false`.
    Returns: minimally initialized rcarray.
    +/
    static mir_rcarray mininit(size_t length, bool deallocate = true)
    {
        return mir_rcarray(length, deallocate, false);
    }

    static if (isImplicitlyConvertible!(const T, T))
        static if (isImplicitlyConvertible!(const Unqual!T, T))
            private alias V = const Unqual!T;
        else
            private alias V = const T;
    else
        private alias V = T;

    ///
    static typeof(this) create(Iterator, SliceKind kind)(Slice!(Iterator, 1, kind) values, bool deallocate = true)
    {
        auto ret = typeof(this)(values.length, deallocate, hasElaborateDestructor!T);
        static if (kind == Contiguous && is(Iterator : V*))
            return create(values.field);
        else
        {
            import mir.conv: emplaceRef;
            import core.lifetime: move;
            foreach (i, ref e; ret)
                e.emplaceRef!T(values[i]);
            return move(ret);
        }
    }

    static if (hasIndirections!T)
    /++
    Contructor is defined if `hasIndirections!T == true`.
    +/
    static typeof(this) create(V[] values...) @nogc
    {
        return create(values, true);
    }

    static if (hasIndirections!T)
    /// ditto
    static typeof(this) create(V[] values, bool deallocate) @nogc
    {
        auto ret = typeof(this)(values.length, deallocate, hasElaborateDestructor!T);
        static if (!hasElaborateAssign!T)
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
        import core.lifetime: move;
        return move(ret);
    }

    static if (!hasIndirections!T) // TODO: mark argument as scope (future!)
    /++
    Contructor is defined if `hasIndirections!T == false`.
    +/
    static typeof(this) create(scope V[] values...) @nogc
    {
        return create(values, true);
    }

    static if (!hasIndirections!T) // TODO: mark argument as scope (future!)
    /// ditto
    static typeof(this) create(scope V[] values, bool deallocate) @nogc
    {
        auto ret = typeof(this)(values.length, deallocate, hasElaborateDestructor!T);
        static if (!hasElaborateAssign!T)
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
        import core.lifetime: move;
        return move(ret);
    }

    private bool initializeImpl()(size_t length, bool deallocate, bool initialize) scope @trusted nothrow @nogc
    {
        if (length == 0)
        {
            _payload = null;
            return true;
        }
        import mir.internal.memory: malloc, alignedAllocate;
        auto p = cast(mir_rcarray_context*) malloc(length * T.sizeof + mir_rcarray_context.sizeof);
        if (p is null)
            return false;
        _payload = cast(T*)(p + 1);
        context = mir_rcarray_context.init;
        context.destroyAndDeallocate = &_freeImpl!T;
        context.length = length;
        context.counter = deallocate;
        // hasElaborateDestructor is required for safe destruction in case of exceptions
        if (initialize || hasElaborateDestructor!T)
        {
            import mir.conv: uninitializedFillDefault;
            uninitializedFillDefault((cast(Unqual!T*)_payload)[0 .. length]);
        }
        return true;
    }
}

/// ditto
alias RCArray = mir_rcarray;

/// ditto
alias rcarray(T) = RCArray!T.create;

alias mininit_rcarray(T) = RCArray!T.mininit;

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

/++
Thread safe reference counting iterator.
+/
struct mir_rci(T)
{
    import std.traits;

    ///
    T* _iterator;

    ///
    RCArray!T _array;

    ///
    inout(T)* lightScope()() scope return inout @property @trusted
    {
        debug
        {
            assert(_array._payload <= _iterator);
            assert(_iterator is null || _iterator <= _array._payload + _array.length);
        }
        return _iterator;
    }

    ///
    ref opAssign(typeof(null)) scope return pure nothrow @nogc @trusted
    {
        pragma(inline, true);
        _iterator = null;
        _array = null;
        return this;
    }

    ///
    ref opAssign(return typeof(this) rhs) scope return @trusted
    {
        _iterator = rhs._iterator;
        _array.proxySwap(rhs._array);
        return this;
    }

    ///
    ref opAssign(Q)(return mir_rci!Q rhs) scope return pure nothrow @nogc @trusted
        if (isImplicitlyConvertible!(Q*, T*))
    {
        import core.lifetime: move;
        _iterator = rhs._iterator;
        _array = move(rhs._array);
        return this;
    }

    ///
    mir_rci!(const T) lightConst()() scope return const @nogc nothrow @trusted @property
    { return typeof(return)(_iterator, _array.lightConst); }

    ///
    mir_rci!(immutable T) lightImmutable()() scope return immutable @nogc nothrow @trusted @property
    { return typeof(return)(_iterator, _array.lightImmutable); }

    ///   
    ref inout(T) opUnary(string op : "*")() inout scope return @trusted
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
    import mir.rcarray;
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
    import mir.rcarray;

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
    import mir.rcarray;
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
    auto r = RCArray!S.create(d[]);
}
