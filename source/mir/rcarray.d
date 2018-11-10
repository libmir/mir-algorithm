/++
+/
module mir.rcarray;

private static immutable allocationExcMsg = "mir_rcarray: out of memory arror.";

version (D_Exceptions)
{
    static immutable allocationExc = new Exception(allocationExcMsg);
}

private template preferCppLinkage(T)
{
    static if (is(T == immutable) || is(T == shared))
        enum preferCppLinkage = false;
    else
    static if (is(T == class) || is(T == struct) || is(T == union) || is(T == interface))
        enum preferCppLinkage = __traits(getLinkage, T) == "C++";
    else
    static if (__traits(isScalar, T))
        static if (is(T : U*, U))
            enum preferCppLinkage = .preferCppLinkage!U;
        else
            enum preferCppLinkage = true;
    else
        enum preferCppLinkage = false;

}

///
version(mir_test)
unittest
{
    struct S {}
    extern(C++) struct C {}
    static assert (preferCppLinkage!double);
    static assert (preferCppLinkage!(const double));
    static assert (!preferCppLinkage!(immutable double));
    static assert (!preferCppLinkage!S);
    static assert (preferCppLinkage!C);
    static assert (preferCppLinkage!(const C));
    static assert (!preferCppLinkage!(immutable C));
}

// extern(C++)
// enum C {e, b}
// pragma(msg, __traits(getLinkage, C));

/++
Thread safe reference counting array.

`__xdtor` if any is used to destruct objects.

The implementation never adds roots into the GC.
+/
struct mir_rcarray(T)
    if (T.alignof <= 16)
{
    enum cppSupport = preferCppLinkage!T;

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
    private Context* _context;

    // private inout(Context)* _context() inout @trusted pure nothrow @nogc scope
    // {
    //     return cast(Context*) _contextCode;
    // }

    // private void _context(Context * context) @trusted pure nothrow @nogc scope
    // {
    //     _contextCode = cast(size_t) context;
    // }

    ///
    this(this) scope @safe pure nothrow @nogc
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

    private void dec()() scope
    {
        import core.atomic: atomicOp;
        if (_context !is null) with(*_context)
        {
            if (counter)
            {
                if (counter.atomicOp!"-="(1) == 0)
                {
                    import mir.conv: xdestroy;
                    T[] array;
                    ()@trusted { array = (cast(T*)(_context + 1))[0 .. length]; }();
                    xdestroy(array);
                    auto p = cast(void*) _context;
                    () @trusted {
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

    static if (cppSupport) extern(C++)
    {
        ///
        pragma(inline, false)
        ~this() scope nothrow @nogc
        {
            dec();
        }

        ///
        pragma(inline, false)
        bool initialize(size_t length, uint alignment = T.alignof, bool deallocate = true) scope @safe nothrow @nogc
        {
            return initializeImpl(length, alignment, deallocate);
        }

        // ///
        // this(ref typeof(this) rhs) @safe pure nothrow @nogc
        // {
        //     this._context = rhs._context;
        //     this.__xpostblit;
        // }
    }
    else
    {
        pragma(inline, false)
        ~this() scope nothrow @nogc
        {
            dec();
        }
        
        pragma(inline, false)
        bool initialize(size_t length, uint alignment = T.alignof, bool deallocate = true) scope @safe nothrow @nogc
        {
            return initializeImpl(length, alignment, deallocate);
        }
    }

    /++
    Params:
        length = array length
        alignment = alignment, must be power of 2
        deallocate = Flag, never deallocates memory if `false`.
    +/
    this(size_t length, uint alignment = T.alignof, bool deallocate = true) scope @trusted @nogc
    {
        if (!initialize(length, alignment, deallocate))
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

    private bool initializeImpl()(size_t length, uint alignment, bool deallocate) scope @trusted nothrow @nogc
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
        import mir.conv: uninitializedFillDefault;
        import std.traits: Unqual;
        uninitializedFillDefault((cast(Unqual!T*)(_context + 1))[0 .. _context.length]);
        return true;
    }

    ///
    size_t length() @safe scope pure nothrow @nogc @property
    {
        return _context !is null ? _context.length : 0;
    }

    ///
    size_t counter() @safe scope pure nothrow @nogc @property
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
        assert(_context);
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

    mir_rcarray!(const T) lightConst() const @nogc nothrow @trusted
    {
        return cast(typeof(return)) this;
    }

    mir_rcarray!(immutable T) lightImmutable() immutable @nogc nothrow @trusted
    {
        return cast(typeof(return)) this;
    }

    size_t opDollar(size_t pos : 0)() @safe scope pure nothrow @nogc
    {
        return _context !is null ? _context.length : 0;
    }

    auto asSlice()() scope return @property
    {
        import mir.ndslice.slice: mir_slice;
        alias It = mir_rci!T;
        return mir_slice!It([length], It((()@trusted => ptr)(), this));
    }
}

///
@safe pure @nogc
unittest
{
    auto a = mir_rcarray!double(10);
    foreach(i, ref e; a)
        e = i;
    auto b = a;
    assert(b[$ - 1] == 9);
    foreach(i, ref e; b)
        assert(e == i);
    b[4] = 100;
    assert(a[4] == 100);

    import mir.ndslice.slice;
    auto s = a.toSlice;
    static assert(is(typeof(s) == Slice!(RCI!double)));
    static assert(is(typeof(s) == mir_slice!(mir_rci!double)));
}

/++
Thread safe reference counting iterator.
+/
struct mir_rci(T)
{
    ///
    T* _iterator;

    // private inout(T)* _iterator() inout @trusted pure nothrow @nogc scope
    // {
    //     return cast(T*) _iteratorCode;
    // }

    // private void _iterator(T * iterator) @trusted pure nothrow @nogc scope
    // {
    //     _iteratorCode = cast(size_t) iterator;
    // }

    ///
    mir_rcarray!T _array;

    ///
    mir_rci!(const T) lightConst()() const @property
    { return typeof(return)(_iterator, _array.lightConst); }

    ///
    mir_rci!(immutable T) lightImmutable()() immutable @property
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
@nogc unittest
{
    import mir.ndslice;
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
@nogc unittest
{
    import mir.ndslice;
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
