/++
$(H1 Thread-safe slim reference-counted shared pointers).

This implementation does not support polymorphism.
+/
module mir.rc.slim_ptr;

import mir.rc.context;
import mir.type_info;
import std.traits;

private static immutable allocationExcMsg = "mir_slim_rcptr: out of memory error.";
private static immutable getExcMsg = "mir_slim_rcptr: trying to use null value.";

version (D_Exceptions)
{
    import core.exception: OutOfMemoryError, InvalidMemoryOperationError;
    private static immutable allocationError = new OutOfMemoryError(allocationExcMsg);
}

/++
Thread safe reference counting array.

This implementation does not support polymorphism.

`__xdtor` if any is used to destruct objects.

The implementation never adds roots into the GC.
+/
struct mir_slim_rcptr(T)
{
    static if (is(T == class) || is(T == interface) || is(T == struct) || is(T == union))
        static assert(!__traits(isNested, T), "mir_slim_rcptr does not support nested types.");

    ///
    static if (is(T == class) || is(T == interface))
        private Unqual!T _value;
    else
        private T* _value;

    private ref inout(mir_rc_context) context() inout scope return pure nothrow @nogc @trusted @property
    {
        assert(_value);
        return (cast(inout(mir_rc_context)*)_value)[-1];
    }

    private void _reset()
    {
        _value = null;
    }

    inout(void)* _thisPtr() inout scope return @trusted @property
    {
        return cast(inout(void)*) _value;
    }

    private alias ThisTemplate = .mir_slim_rcptr;

    /// ditto
    alias opUnary(string op : "*") = _get_value;
    /// ditto
    alias _get_value this;

    static if (is(T == class) || is(T == interface))
        ///
        pragma(inline, true)
        inout(T) _get_value() scope inout @property
        {
            assert(this, getExcMsg);
            return _value;
        }
    else
        ///
        pragma(inline, true)
        ref inout(T) _get_value() scope inout @property
        {
            assert(this, getExcMsg);
            return *_value;
        }

    ///
    void proxySwap(ref typeof(this) rhs) pure nothrow @nogc @safe
    {
        auto t = this._value;
        this._value = rhs._value;
        rhs._value = t;
    }

    ///
    mixin CommonRCImpl;

    ///
    ~this() nothrow
    {
        static if (hasDestructor!T)
        {
            if (false) // break @safe and pure attributes
            {
                Unqual!T* object;
                (*object).__xdtor();
            }
        }
        if (this)
        {
            (() @trusted { mir_rc_decrease_counter(context); })();
            debug _reset;
        }
    }

    ///
    this(this) scope @trusted pure nothrow @nogc
    {
        if (this)
        {
            mir_rc_increase_counter(context);
        }
    }

    static if (!is(T == interface) && !__traits(isAbstractClass, T))
    {
        private this(Args...)(auto ref Args args)
        {
            () @trusted {
                auto context = mir_rc_create(mir_get_type_info!T, 1, mir_get_payload_ptr!T);
                if (!context)
                {
                    version(D_Exceptions)
                        throw allocationError;
                    else
                        assert(0, allocationExcMsg);
                }
                _value = cast(typeof(_value))(context + 1);
            } ();
            import mir.functional: forward;
            import mir.conv: emplace;
            cast(void) emplace!T(_value, forward!args);
        }
    }
}

///
alias SlimRCPtr = mir_slim_rcptr;

///
template createSlimRC(T)
{
    ///
    mir_slim_rcptr!T createSlimRC(Args...)(auto ref Args args)
    {
        import mir.functional: forward;
        return mir_slim_rcptr!T(forward!args);
    }
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    auto a = createSlimRC!double(10);
    auto b = a;
    assert(*b == 10);
    *b = 100;
    assert(*a == 100);
}

/// Classes
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    static class C
    {
        int index;
        double value;
        ref double bar() @safe pure nothrow @nogc { return value; }
        this(double d) { value = d; }
    }
    auto a = createSlimRC!C(10);
    assert(a._counter == 1);
    auto b = a;
    assert(a._counter == 2);
    assert((*b).value == 10);
    b.value = 100; // access via alias this syntax
    assert(a.value == 100);
    assert(a._counter == 2);
}

/// Structs
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

    auto a = createSlimRC!C(10, S(3));
    auto s = a;
    assert(s._counter == 2);
    assert(s.e == 3);
}

version(unittest):

private struct _test_unpure_system_dest_s__ {
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
    auto ptr = createSlimRC!_test_unpure_system_dest_s__(42);
    auto arr = rcarray!_test_unpure_system_dest_s__(3);
}
