/++
$(H1 Thread-safe reference-counted arrays and iterators).
+/
module mir.rcarray;

private static immutable allocationExcMsg = "mir_rcarray: out of memory arror.";

version (D_Exceptions)
{
    static immutable allocationExc = new Exception(allocationExcMsg);
}

private template StripPointers(T)
{
    static if (is(T : U*, U))
        alias StripPointers = .StripPointers!U;
    else
        alias StripPointers = T;
}

private enum isImmutableOrShared(T) = is(T == immutable) || is(T == shared);

private template cppSupport(T) {

    static if (__VERSION__ < 2082)
        enum cppSupport = false;
    else
    {
        alias S = StripPointers!T;
        static if (isImmutableOrShared!S)
            enum cppSupport = false;
        else
        static if (is(T == class) || is(T == struct) || is(T == union) || is(T == interface))
            enum cppSupport = __traits(getLinkage, T) == "C++";
        else
            enum cppSupport = __traits(isScalar, T);
    }
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

    private struct Context
    {
        shared size_t counter;
        size_t length;
        union
        {
            pure nothrow @nogc bool function(void[]) _function;
            pure nothrow @nogc bool function(void* ctx, void[]) _delegate;
        }
        void* _delegateContext;
    }

    static assert(Context.sizeof % 16 == 0);

    ///
    private T* _payload;
    private ref inout(Context*) _context() inout scope return pure nothrow @nogc @trusted @property
    {
        return *cast(inout(Context*)*)&_payload;
    }

    pragma(inline, false)
    private void dec()() scope nothrow @nogc @safe
    {
        import core.atomic: atomicOp;
        with(*_context)
        {
            if (counter)
            {
                if (counter.atomicOp!"-="(1) == 0)
                {
                    import mir.conv: xdestroy;
                    Unqual!T[] array;
                    ()@trusted { array = (cast(Unqual!T*)(_context + 1))[0 .. length]; }();
                    xdestroy(array);
                    () @trusted {
                        auto p = cast(void*) _payload;
                        with(*_context)
                        {
                            if (_delegateContext !is null)
                            {
                                size_t size = length * T.sizeof + Context.sizeof;
                                _delegate(_delegateContext, p[0 .. size]);
                            }
                            else
                            if (_function !is null)
                            {
                                size_t size = length * T.sizeof + Context.sizeof;
                                _function(p[0 .. size]);
                            }
                            else
                            {
                                import mir.internal.memory: free;
                                free(p);
                            }
                        }
                    }();
                }
            }
        }
    }

    static if (cppSupport)
    {
    extern(C++):
        ///
        ~this() nothrow @nogc @safe
        {
            if (_context !is null)
                dec();
        }

        /// Extern constructor
        pragma(inline, false)
        bool initialize(size_t length, uint alignment, bool deallocate, bool initialize) scope @system nothrow @nogc
        {
            return initializeImpl(length, alignment, deallocate, initialize);
        }

        static if (is(T == const))
        {
            /// Defined if T is const
            this(ref const typeof(this) rhs) @trusted pure nothrow @nogc
            {
                this._payload = cast(T*) rhs._payload;
                this.__xpostblit;
            }

            /// ditto
            ref opAssign(ref const typeof(this) rhs) @trusted pure nothrow @nogc
            {
                if (_payload != rhs._payload)
                {
                    if (_payload) dec();
                    _payload = cast(T*) rhs._payload;
                    this.__xpostblit;
                }
                return this;
            }

            /// ditto
            ref opAssign(const typeof(this) rhs) @trusted pure nothrow @nogc
            {
                if (_payload != rhs._payload)
                {
                    if (_payload) dec();
                    _payload = cast(T*) rhs._payload;
                    *cast(T**)&rhs._payload = null;
                }
                return this;
            }
        }

        static if (!is(T == const))
        {
            /// Defined if T isn't const
            this(ref typeof(this) rhs) pure nothrow @nogc
            {
                this._payload = rhs._payload;
                this.__xpostblit;
            }

            /// ditto
            ref opAssign(ref typeof(this) rhs) pure nothrow @nogc
            {
                if (_payload != rhs._payload)
                {
                    if (_payload) dec();
                    _payload = rhs._payload;
                    this.__xpostblit;
                }
                return this;
            }

            ref opAssign(typeof(this) rhs) pure nothrow @nogc
            {
                if (_payload != rhs._payload)
                {
                    if (_payload) dec();
                    _payload = rhs._payload;
                    rhs._payload = null;
                }
                return this;
            }
        }

        ///
        auto asSlice() scope return @property
        {
            alias It = mir_rci!T;
            return Slice!It([length], It((()@trusted => ptr)(), this));
        }
    }
    else
    {
        ~this() nothrow @nogc @safe
        {
            if (_context !is null)
                dec();
        }
        
        /// Extern constructor
        pragma(inline, false)
        bool initialize(size_t length, uint alignment, bool deallocate, bool initialize) scope @system nothrow @nogc
        {
            return initializeImpl(length, alignment, deallocate, initialize);
        }

        ///
        auto asSlice()() scope return @property
        {
            import mir.ndslice.slice: Slice;
            alias It = mir_rci!T;
            return Slice!It([length], It((()@trusted => ptr)(), this));
        }
    }

    ///
    this(this) scope @trusted pure nothrow @nogc
    {
        import core.atomic: atomicOp;
        if (_context !is null) with(*_context)
        {
            if (counter)
            {
                counter.atomicOp!"+="(1);
            }
        }
    }

    /++
    Params:
        length = array length
        alignment = alignment, must be power of 2
        deallocate = Flag, never deallocates memory if `false`.
        initialize = Flag, don't initialize memory with default value if `false`.
    +/
    this(size_t length, uint alignment = T.alignof, bool deallocate = true, bool initialize = true) @trusted @nogc
    {
        if (!this.initialize(length, alignment, deallocate, initialize))
        {
            version(D_Exceptions)
            {
                throw allocationExc;
            }
            else
            {
                assert(0, allocationExcMsg);
            }
        }
    }

    static if (isImplicitlyConvertible!(const T, T))
        static if (isImplicitlyConvertible!(const Unqual!T, T))
            private alias V = const Unqual!T;
        else
            private alias V = const T;
    else
        private alias V = T;

    ///
    static typeof(this) create(Iterator, SliceKind kind)(Slice!(Iterator, 1, kind) values)
    {
        auto ret = typeof(this)(values.length, T.alignof, true, hasElaborateDestructor!T);
        static if (kind == Contiguous && is(Iterator : V*))
            return create(values.field);
        else
        {
            import  mir.conv: emplaceRef;
            foreach (i, ref e; ret)
                e.emplaceRef!T(values[i]);
            return ret;
        }
    }

    static if (hasIndirections!T)
    /++
    Contructor is defined if `hasIndirections!T == true`.
    +/
    static typeof(this) create(V[] values...) @safe @nogc
    {
        auto ret = typeof(this)(values.length, T.alignof, true, hasElaborateDestructor!T);
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
        return ret;
    }

    static if (!hasIndirections!T)
    /++
    Contructor is defined if `hasIndirections!T == false`.
    +/
    static typeof(this) create(scope V[] values...) @nogc
    {
        auto ret = typeof(this)(values.length, T.alignof, true, hasElaborateDestructor!T);
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
        return ret;
    }

    private bool initializeImpl()(size_t length, uint alignment, bool deallocate, bool initialize) scope @trusted nothrow @nogc
    {
        if (length == 0)
        {
            _context = null;
            return true;
        }
        import mir.internal.memory: malloc, alignedAllocate;
        if (alignment <= 16)
        {
            _context = cast(Context*) malloc(length * T.sizeof + Context.sizeof);
            *_context = Context.init;
            if (_context is null)
                return false;
        }
        else 
        {
            _context = cast(Context*) alignedAllocate(length * T.sizeof + Context.sizeof, alignment);
            *_context = Context.init;
            if (_context is null)
                return false;
            version(Posix) {} // common free
            else
            {
                import mir.internal.memory: alignedFree;
                static bool feeFun(void[] p)
                {
                    alignedFree(p.ptr);
                    return true;
                }
                _context._function = &feeFun;
            }
        }
        
        _context.length = length;
        _context.counter = deallocate; // 0
        // hasElaborateDestructor is required for safe destruction in case of exceptions
        if (initialize || hasElaborateDestructor!T)
        {
            import mir.conv: uninitializedFillDefault;
            import std.traits: Unqual;
            uninitializedFillDefault((cast(Unqual!T*)(_context + 1))[0 .. _context.length]);
        }
        return true;
    }

    ///
    size_t length() @trusted scope pure nothrow @nogc const @property
    {
        return _context !is null ? _context.length : 0;
    }

    ///
    size_t counter() @trusted scope pure nothrow @nogc const @property
    {
        return _context !is null ? _context.counter : 0;
    }

    ///
    inout(T)* ptr() @system scope inout
    {
        return _context !is null ? cast(inout(T)*)(_context + 1) : null;
    }

    ///
    ref opIndex(size_t i) @trusted scope inout
    {
        assert(_payload);
        assert(i < _context.length);
        return (cast(inout(T)*)(_context + 1))[i];
    }

    ///
    bool opEquals(typeof(null)) @safe scope pure nothrow @nogc @property
    {
        return _context is null;
    }

    ///
    inout(T)[] opIndex() @trusted scope inout
    {
        return _context !is null ?  (cast(inout(T)*)(_context + 1))[0 .. _context.length] : null;
    }

    ///
    mir_rcarray!(const T) lightConst()() scope return const @nogc nothrow @trusted @property
    { return cast(typeof(return)) this; }

    mir_rcarray!(immutable T) lightImmutable()() scope return immutable @nogc nothrow @trusted @property
    { return cast(typeof(return)) this; }

    size_t opDollar(size_t pos : 0)() @trusted scope pure nothrow @nogc const
    {
        return _context !is null ? _context.length : 0;
    }
}

/// ditto
alias RCArray = mir_rcarray;

///
version(mir_test)
@safe pure @nogc
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
@safe pure @nogc
unittest
{
    auto a = RCArray!double.create(1.0, 2, 5, 3);
    assert(a[0] == 1);
    assert(a[$ - 1] == 3);

    auto s = RCArray!char.create("hello!");
    assert(s[0] == 'h');
    assert(s[$ - 1] == '!');

    alias rcstring = RCArray!(immutable char).create;
    auto r = rcstring("string");
    assert(r[0] == 's');
    assert(r[$ - 1] == 'g');
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

    mir_rci!(const T) lightConst() scope return const @nogc nothrow @trusted @property
    { return typeof(return)(_iterator, _array.lightConst); }

    mir_rci!(immutable T) lightImmutable() scope return immutable @nogc nothrow @trusted @property
    { return typeof(return)(_iterator, _array.lightImmutable); }

    ///   
    ref inout(T) opUnary(string op : "*")() inout scope return
    { return *_iterator; }

    ///   
    ref inout(T) opIndex(ptrdiff_t index) inout scope return
    { return _iterator[index]; }

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
@nogc unittest
{
    import mir.ndslice.slice;
    import mir.rcarray;
    auto array = mir_rcarray!double(10);
    auto slice = array.asSlice;
    static assert(is(typeof(slice) == Slice!(RCI!double)));
    auto matrix = slice.sliced(2, 5);
    static assert(is(typeof(matrix) == Slice!(RCI!double, 2)));
    array[7] = 44;
    assert(matrix[1, 2] == 44);
}

///
version(mir_test)
@nogc unittest
{
    import mir.ndslice.slice;
    import mir.rcarray;

    alias rcvec = Slice!(RCI!double);

    RCI!double a, b;
    size_t c = a - b;

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
