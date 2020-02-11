/++
$(H1 Thread-safe reference-counted shared pointers).

This implementation supports class and struct (`alias this`) polymorphism.
+/
module mir.rc.ptr;

import mir.rc.context;
import mir.type_info;
import std.traits;

package static immutable allocationExcMsg = "mir_rcptr: out of memory error.";
package static immutable getExcMsg = "mir_rcptr: trying to use null value.";

version (D_Exceptions)
{
    import core.exception: OutOfMemoryError, InvalidMemoryOperationError;
    package static immutable allocationError = new OutOfMemoryError(allocationExcMsg);
}

/++
Thread safe reference counting array.

This implementation supports class and struct (`alias this`) polymorphism.

`__xdtor` if any is used to destruct objects.

The implementation never adds roots into the GC.
+/
struct mir_rcptr(T)
{
    static if (is(T == class) || is(T == interface) || is(T == struct) || is(T == union))
        static assert(!__traits(isNested, T), "mir_rcptr does not support nested types.");

    ///
    static if (is(T == class) || is(T == interface))
        package Unqual!T _value;
    else
        package T* _value;
    package mir_rc_context* _context;

    package ref inout(mir_rc_context) context() inout scope return @trusted @property
    {
        return *_context;
    }

    package void _reset()
    {
        _value = null;
        _context = null;
    }

    inout(void)* _thisPtr() inout scope return @trusted @property
    {
        return cast(inout(void)*) _value;
    }

    package alias ThisTemplate = .mir_rcptr;

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
        auto t0 = this._value;
        auto t1 = this._context;
        this._value = rhs._value;
        this._context = rhs._context;
        rhs._value = t0;
        rhs._context = t1;
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
        package(mir) this(Args...)(auto ref Args args)
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
            cast(void) emplace!T(_value, forward!args);
        }
    }
}

///
alias RCPtr = mir_rcptr;

/++
Returns: shared pointer of the member and the context from the current pointer. 
+/
auto shareMember(string member, T, Args...)(return mir_rcptr!T context, auto ref Args args)
{
    import core.lifetime: move;
    void foo(A)(auto ref A) {}
    assert(context != null);
    static if (args.length)
    {
        // breaks safaty
        if (false) foo(__traits(getMember, context._get_value, member)(forward!args));
        return (()@trusted => createRCWithContext(__traits(getMember, context._get_value, member)(forward!args), context.move))();
    }
    else
    {
        // breaks safaty
        if (false) foo(__traits(getMember, context._get_value, member));
        return (()@trusted => createRCWithContext(__traits(getMember, context._get_value, member), context.move))();
    }
}

/++
Returns: shared pointer constructed with current context. 
+/
@system .mir_rcptr!R createRCWithContext(R, F)(return R value, return const mir_rcptr!F context)
    if (is(R == class) || is(R == interface))
{
    typeof(return) ret;
    ret._value = cast()value;
    ret._context = cast(mir_rc_context*)context._context;
    (*cast(mir_rcptr!F*)&context)._value = null;
    (*cast(mir_rcptr!F*)&context)._context = null;
    return ret;
}

///ditto
@system .mir_rcptr!R createRCWithContext(R, F)(return ref R value, return const mir_rcptr!F context)
    if (!is(R == class) && !is(R == interface))
{
    typeof(return) ret;
    ret._value = &value;
    ret._context = cast(mir_rc_context*)context._context;
    (*cast(mir_rcptr!F*)&context)._value = null;
    (*cast(mir_rcptr!F*)&context)._context = null;
    return ret;
}

/++
Construct a shared pointer of a required type with a current context.
Provides polymorphism abilities for classes and structures with `alias this` syntax.
+/
mir_rcptr!R castTo(R, T)(return mir_rcptr!T context) @trusted
    if (isImplicitlyConvertible!(T, R))
{
    import core.lifetime: move;
    return createRCWithContext(cast(R)context._get_value, move(context));
}

/// ditto
mir_rcptr!(const R) castTo(R, T)(return const mir_rcptr!T context) @trusted
    if (isImplicitlyConvertible!(const T, const R))
{
    import core.lifetime: move;
    return createRCWithContext(cast(const R)context._get_value, move(*cast(mir_rcptr!T*)&context));
}

/// ditto
mir_rcptr!(immutable R) castTo(R, T)(return immutable mir_rcptr!T context) @trusted
    if (isImplicitlyConvertible!(immutable T, immutable R))
{
    import core.lifetime: move;
    return createRCWithContext(cast(immutable R)context._get_value, move(*cast(mir_rcptr!T*)&context));
}


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
    static interface I { ref double bar() @safe pure nothrow @nogc; }
    static abstract class D { int index; }
    static class C : D, I
    {
        double value;
        ref double bar() @safe pure nothrow @nogc { return value; }
        this(double d) { value = d; }
    }
    auto a = createRC!C(10);
    assert(a._counter == 1);
    auto b = a;
    assert(a._counter == 2);
    assert((*b).value == 10);
    b.value = 100; // access via alias this syntax
    assert(a.value == 100);
    assert(a._counter == 2);

    auto d = a.castTo!D; //RCPtr!D
    import std.stdio;
    assert(d._counter == 3);
    d.index = 234;
    assert(a.index == 234);
    auto i = a.castTo!I; //RCPtr!I
    assert(i.bar == 100);
    assert(i._counter == 4);

    auto v = a.shareMember!"value"; //RCPtr!double
    auto w = a.shareMember!"bar"; //RCPtr!double
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
    auto s = a.castTo!S; // RCPtr!S
    assert(s._counter == 2);
    assert(s.e == 3);
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
