/++
$(H1 Thread-safe reference-counted shared pointers).
+/
module mir.shared_ptr;

private static immutable allocationExcMsg = "mir_shared_ptr: out of memory error.";
private static immutable getExcMsg = "mir_shared_ptr: trying to use null value.";

version (D_Exceptions)
{
    import core.exception: OutOfMemoryError, InvalidMemoryOperationError;
    private static immutable allocationError = new OutOfMemoryError(allocationExcMsg);
}

private template StripPointers(T)
{
    static if (is(T : U*, U))
        alias StripPointers = .StripPointers!U;
    else
        alias StripPointers = T;
}

private enum isImmutableOrShared(T) = is(T == immutable) || is(T == shared);

package template cppSupport(T) {

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
+/
struct mir_rcarray_context
{
    ///
    void* allocatorContext;
    ///
    extern(C)
    pure nothrow @nogc int function(void* allocatorContext, mir_rcarray_context* payload) destroyAndDeallocate;
    ///
    shared size_t counter;
    ///
    size_t length;
}

/++
Increase counter by 1.

Params:
    context = shared_ptr context (not null)
+/
extern(C)
void mir_rcarray_increase_counter(ref mir_rcarray_context context) @system nothrow @nogc pure
{
    import core.atomic: atomicOp;
    with(context)
    {
        if (counter)
        {
            counter.atomicOp!"+="(1);
        }
    }
}

/++
Decrease counter by 1.
Destroys data if counter decreased from 1 to 0.

Params:
    context = shared_ptr context (not null)
+/
extern(C)
void mir_rcarray_decrease_counter(ref mir_rcarray_context context) @system nothrow @nogc pure
{
    pragma(inline, false);
    import core.atomic: atomicOp;
    with(context)
    {
        if (counter)
        {
            if (counter.atomicOp!"-="(1) == 0)
            {
                destroyAndDeallocate(allocatorContext, &context);
            }
        }
    }
}

extern(C)
package static int _freeImpl(T, bool structLike = !is(T == class))(void*, mir_rcarray_context* context) @trusted pure nothrow @nogc
{
    import std.traits: Unqual;
    import mir.internal.memory: free;
    static if (is(T == class))
    {
        static if (structLike)
        {
            assert(context.length == 1);
            import mir.conv: xdestroy;
            auto value = cast(Unqual!T)(context + 1);
            static if (__traits(hasMember, Unqual!T, "__xdtor"))
            static if (__traits(isSame, Unqual!T, __traits(parent, value.__xdtor)))
                value.__xdtor();
        }
    }
    else
    {
        import mir.conv: xdestroy;
        xdestroy((cast(Unqual!T*)(context + 1))[0 .. context.length]);
    }
    free(context);
    return true;
}

///
mixin template CommonRCImpl()
{
    ///
    this(typeof(null))
    {
    }

    ///
    ~this() nothrow @nogc @trusted
    {
        if (this)
        {
            mir_rcarray_decrease_counter(context);
            debug _reset;
        }
    }

    ///
    this(this) scope @trusted pure nothrow @nogc
    {
        if (this)
        {
            mir_rcarray_increase_counter(context);
        }
    }

    ///
    ref opAssign(typeof(null)) scope return pure nothrow @nogc @trusted
    {
        this = typeof(this).init;
    }

    ///
    ref opAssign(return typeof(this) rhs) scope return @trusted
    {
        this.proxySwap(rhs);
        return this;
    }

    ///
    ref opAssign(Q, bool b)(return ThisTemplate!(Q, b) rhs) scope return pure nothrow @nogc @trusted
        if (isImplicitlyConvertible!(Q*, T*))
    {
        this.proxySwap(*cast(typeof(this)*)&rhs);
        return this;
    }

    ///
    ThisTemplate!(const T, cppSupport) lightConst()() scope return const @nogc nothrow @trusted @property
    { return *cast(typeof(return)*) &this; }

    /// ditto
    ThisTemplate!(immutable T) lightImmutable()() scope return immutable @nogc nothrow @trusted @property
    { return *cast(typeof(return)*) &this; }

    ///
    pragma(inline, true)
    size_t _counter() @trusted scope pure nothrow @nogc const @property
    {
        return cast(bool)this ? context.counter : 0;
    }

    ///
    bool opCast(C : bool)() const
    {
        return _thisPtr !is null;
    }

    ///
    ref C opCast(C : ThisTemplate!(Q, b), Q, bool b)() pure nothrow @nogc @trusted
        if (isImplicitlyConvertible!(T*, Q*))
    {
        return *cast(typeof(return)*)&this;
    }

    /// ditto
    C opCast(C : ThisTemplate!(Q, b), Q, bool b)() pure nothrow @nogc const @trusted
        if (isImplicitlyConvertible!(const(T)*, Q*))
    {
        return *cast(typeof(return)*)&this;
    }

    /// ditto
    C opCast(C : ThisTemplate!(Q, b), Q, bool b)() pure nothrow @nogc immutable @trusted
        if (isImplicitlyConvertible!(immutable(T)*, Q*))
    {
        return *cast(typeof(return)*)&this;
    }

    ///
    pragma(inline, true)
    bool opEquals(typeof(null)) @safe scope pure nothrow @nogc @property
    {
        return !this;
    }

    /// ditto
    bool opEquals(Y, bool b)(auto ref scope const ThisTemplate!(Y, b) rhs) @safe scope pure nothrow @nogc @property
    {
        return _thisPtr == _rhs._thisPtr;
    }

    ///
    sizediff_t opCmp(Y, bool b)(auto ref scope const ThisTemplate!(Y, b) rhs) @trusted scope pure nothrow @nogc @property
    {
        return cast(void*)_thisPtr - cast(void*)_rhs._thisPtr;
    }

    size_t toHash() @trusted scope pure nothrow @nogc @property
    {
        return cast(size_t) _thisPtr;
    }
}

/++
Thread safe reference counting array.

`__xdtor` if any is used to destruct objects.

The implementation never adds roots into the GC.
+/
struct mir_shared_ptr(T, bool cppSupport = .cppSupport!T)
{
    import std.traits;

    static if (is(T == class) || is(T == interface) || is(T == struct) || is(T == union))
        static assert(!__traits(isNested, T), "mir_shared_ptr does not support nested types.");

    ///
    static if (is(T == class) || is(T == interface))
        private Unqual!T _value;
    else
        private T* _value;
    private mir_rcarray_context* _context;

    private ref inout(mir_rcarray_context) context() inout scope return @trusted @property
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

    private alias ThisTemplate = .mir_shared_ptr;

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
    .mir_shared_ptr!R _shareAs(R)() @trusted
        if (isImplicitlyConvertible!(T, R))
    {
        return _withContext(cast(R)_get_value);
    }

    /// ditto
    .mir_shared_ptr!(const R) _shareAs(R)() @trusted const
        if (isImplicitlyConvertible!(const T, const R))
    {
        return _withContext(cast(const R)_get_value);
    }

    /// ditto
    .mir_shared_ptr!(immutable R) _shareAs(R)() @trusted immutable
        if (isImplicitlyConvertible!(immutable T, immutable R))
    {
        return _withContext(cast(immutable R)_get_value);
    }

    /++
    Returns: shared pointer constructed with current context. 
    +/
    @system .mir_shared_ptr!R _withContext(R)(return R value) return const
        if (is(R == class) || is(R == interface))
    {
        import core.lifetime: move;
        typeof(return) ret;
        ret._value = cast()value;
        ret._context = cast(mir_rcarray_context*)_context;
        ret.__postblit;
        return ret.move;
    }

    ///ditto
    @system .mir_shared_ptr!R _withContext(R)(return ref R value) return const
        if (!is(R == class) && !is(R == interface))
    {
        import std.algorithm.mutation: move;
        typeof(return) ret;
        ret._value = &value;
        ret._context = cast(mir_rcarray_context*)_context;
        ret.__postblit;
        return ret.move;
    }

    ///
    mixin CommonRCImpl;

    static if (!is(T == interface) && !__traits(isAbstractClass, T))
    {
        static if (cppSupport)
        {
        extern(C++):
            pragma(inline, false)
            private bool __initialize(bool deallocate, bool initialize) scope @system nothrow @nogc
            {
                return initializeImpl(deallocate, initialize);
            }
        }
        else
        {
            pragma(inline, false)
            private bool __initialize(bool deallocate, bool initialize) scope @system nothrow @nogc
            {
                return initializeImpl(deallocate, initialize);
            }
        }

        private this(Args...)(auto ref Args args) @trusted
        {
            if (!this.__initialize(true, true))
            {
                version(D_Exceptions)
                    throw allocationError;
                else
                    assert(0, allocationExcMsg);
            }
            import core.lifetime: emplace;
            import mir.functional: forward;
            emplace!T(_value, forward!args);
        }

        private bool initializeImpl()(bool deallocate, bool initialize) scope @trusted nothrow @nogc
        {
            import mir.internal.memory: malloc, alignedAllocate;
            static if (is(T == class))
                enum sizeof = __traits(classInstanceSize, T);
            else
                enum sizeof = T.sizeof;
                _context = cast(mir_rcarray_context*)malloc(sizeof + mir_rcarray_context.sizeof);

            if (_context is null)
                return false;

            _value = cast(typeof(_value))(_context + 1);

            context = mir_rcarray_context.init;
            context.destroyAndDeallocate = &_freeImpl!(T, true);
            context.counter = deallocate;
            context.length = 1;
            // hasElaborateDestructor is required for safe destruction in case of exceptions
            if (initialize || hasElaborateDestructor!T)
            {
                static if (!is(T == class))
                {
                    import core.lifetime: emplace;
                    emplace(cast(Unqual!T*)_value);
                }
            }
            return true;
        }
    }
}

///
alias SharedPtr = mir_shared_ptr;

///
template createShared(T)
{
    ///
    mir_shared_ptr!T createShared(Args...)(auto ref Args args)
    {
        import mir.functional: forward;
        return mir_shared_ptr!T(forward!args);
    }
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    auto a = createShared!double(10);
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
    auto a = createShared!C(10);
    assert(a._counter == 1);
    auto b = a;
    assert(a._counter == 2);
    assert((*b).value == 10);
    b.value = 100; // access via alias this syntax
    assert(a.value == 100);

    auto d = a._shareAs!D; //SharedPtr!D
    import std.stdio;
    assert(d._counter == 3);
    d.index = 234;
    assert(a.index == 234);
    auto i = a._shareAs!I; //SharedPtr!I
    assert(i.bar == 100);
    assert(i._counter == 4);

    auto v = a._shareMember!"value"; //SharedPtr!double
    auto w = a._shareMember!"bar"; //SharedPtr!double
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

    auto a = createShared!C(10, S(3));
    auto s = a._shareAs!S; // SharedPtr!S
    assert(s._counter == 2);
    assert(s.e == 3);
}
