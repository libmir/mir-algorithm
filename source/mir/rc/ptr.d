/++
$(H1 Thread-safe reference-counted shared pointers).
+/
module mir.rc.ptr;

import mir.rc.context;
import mir.type_info;

private static immutable allocationExcMsg = "mir_rcptr: out of memory error.";
private static immutable getExcMsg = "mir_rcptr: trying to use null value.";

version (D_Exceptions)
{
    import core.exception: OutOfMemoryError, InvalidMemoryOperationError;
    private static immutable allocationError = new OutOfMemoryError(allocationExcMsg);
}

/++
Thread safe reference counting array.

`__xdtor` if any is used to destruct objects.

The implementation never adds roots into the GC.
+/
struct mir_rcptr(T)
{
    import std.traits;

    static if (is(T == class) || is(T == interface) || is(T == struct) || is(T == union))
        static assert(!__traits(isNested, T), "mir_rcptr does not support nested types.");

    ///
    static if (is(T == class) || is(T == interface))
        private Unqual!T _value;
    else
        private T* _value;
    private mir_rc_context* _context;

    private ref inout(mir_rc_context) context() inout scope return @trusted @property
    {
        return *_context;
    }

    private void _reset()
    {
        _value = null;
        _context = null;
    }

    inout(void)* _thisPtr() inout scope return @trusted @property
    {
        return cast(inout(void)*) _value;
    }

    private alias ThisTemplate = .mir_rcptr;

    /// ditto
    alias opUnary(string op : "*") = _get_value;
    /// ditto
    alias _get_value this;

    static if (is(T == class) || is(T == interface))
    {
        ///
        pragma(inline, true)
        inout(T) _get_value() inout scope return @property
        {
            assert(this, getExcMsg);
            return _value;
        }
    }
    else
    {
        ///
        pragma(inline, true)
        ref inout(T) _get_value() scope return inout @property
        {
            assert(this, getExcMsg);
            return *_value;
        }
    }

    ///
    void proxySwap(ref typeof(this) rhs) pure nothrow @nogc @safe
    {
        auto t0 = this._value;
        auto t1 = this._context;
        this._value = rhs._value;
        this._context = rhs._context;
        rhs._value = t0;
        rhs._context = t1;
    }

    /++
    +/
    auto _shareMember(string member, Args...)(auto ref Args args)
    {
        void foo(A)(auto ref A) {}
        static if (args.length)
        {
            // breaks safaty
            if (false) foo(__traits(getMember, _get_value, member)(forward!args));

            return (()@trusted => _withContext(__traits(getMember, _get_value, member)(forward!args)))();
        }
        else
        {
            // breaks safaty
            if (false) foo(__traits(getMember, _get_value, member));

            return (()@trusted => _withContext(__traits(getMember, _get_value, member)))();
        }
    }

    /++
    Construct a shared pointer of a required type with a current context.
    Provides polymorphism abilities for classes and structures with `alias this` syntax.
    +/
    .mir_rcptr!R _shareAs(R)() @trusted
        if (isImplicitlyConvertible!(T, R))
    {
        return _withContext(cast(R)_get_value);
    }

    /// ditto
    .mir_rcptr!(const R) _shareAs(R)() @trusted const
        if (isImplicitlyConvertible!(const T, const R))
    {
        return _withContext(cast(const R)_get_value);
    }

    /// ditto
    .mir_rcptr!(immutable R) _shareAs(R)() @trusted immutable
        if (isImplicitlyConvertible!(immutable T, immutable R))
    {
        return _withContext(cast(immutable R)_get_value);
    }

    /++
    Returns: shared pointer constructed with current context. 
    +/
    @system .mir_rcptr!R _withContext(R)(return R value) return const
        if (is(R == class) || is(R == interface))
    {
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        typeof(return) ret;
        ret._value = cast()value;
        ret._context = cast(mir_rc_context*)_context;
        ret.__postblit;
        return ret.move;
    }

    ///ditto
    @system .mir_rcptr!R _withContext(R)(return ref R value) return const
        if (!is(R == class) && !is(R == interface))
    {
        import std.algorithm.mutation: move;
        typeof(return) ret;
        ret._value = &value;
        ret._context = cast(mir_rc_context*)_context;
        ret.__postblit;
        return ret.move;
    }

    ///
    mixin CommonRCImpl;

    static if (!is(T == interface) && !__traits(isAbstractClass, T))
    {
        private this(Args...)(auto ref Args args) @trusted
        {
            () @trusted {
                _context = mir_rc_create(mir_get_type_info!T, 1, mir_get_payload_ptr!T);
                if (!_context)
                {
                    version(D_Exceptions)
                        throw allocationError;
                    else
                        assert(0, allocationExcMsg);
                }
                _value = cast(typeof(_value))(_context + 1);
            } ();
            import mir.functional: forward;
            import mir.conv: emplace;
            emplace!T(_value, forward!args);
        }
    }
}

///
alias RCPtr = mir_rcptr;

///
template createRC(T)
{
    ///
    mir_rcptr!T createRC(Args...)(auto ref Args args)
    {
        import mir.functional: forward;
        return mir_rcptr!T(forward!args);
    }
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    auto a = createRC!double(10);
    auto b = a;
    assert(*b == 10);
    *b = 100;
    assert(*a == 100);
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    static interface I { ref double bar() return @safe pure nothrow @nogc; }
    static abstract class D { int index; }
    static class C : D, I
    {
        double value;
        ref double bar() { return value; }
        this(double d) { value = d; }
    }
    auto a = createRC!C(10);
    assert(a._counter == 1);
    auto b = a;
    assert(a._counter == 2);
    assert((*b).value == 10);
    b.value = 100; // access via alias this syntax
    assert(a.value == 100);

    auto d = a._shareAs!D; //RCPtr!D
    import std.stdio;
    assert(d._counter == 3);
    d.index = 234;
    assert(a.index == 234);
    auto i = a._shareAs!I; //RCPtr!I
    assert(i.bar == 100);
    assert(i._counter == 4);

    auto v = a._shareMember!"value"; //RCPtr!double
    auto w = a._shareMember!"bar"; //RCPtr!double
    assert(i._counter == 6);
    assert(*v == 100);
    ()@trusted{assert(&*w is &*v);}();
}

/// 'Alias This' support
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    struct S
    {
        double e;
    }
    struct C
    {
        int i;
        S s;
        // 'alias' should be accesable by reference
        // or a class/interface
        alias s this;
    }

    auto a = createRC!C(10, S(3));
    auto s = a._shareAs!S; // RCPtr!S
    assert(s._counter == 2);
    assert(s.e == 3);
    a.s.e = 4;
    assert(s.e == 4);
}

version(unittest):

package struct _test_unpure_system_dest_s__ {
    static int numStructs;
    int i;

    this(this This)(int i) {
        this.i = i;
        ++numStructs;
    }

    ~this() @system nothrow {
        auto d = new int[2];
        --numStructs;
    }
}

version(mir_test)
@system nothrow
unittest
{
    import mir.rc.array;
    auto ptr = createRC!_test_unpure_system_dest_s__(42);
    auto arr = rcarray!_test_unpure_system_dest_s__(3);
}
