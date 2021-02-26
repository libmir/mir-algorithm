/++
$(H1 Thread-safe reference-counted arrays and iterators).
+/
module mir.rc.array;

import mir.primitives: hasLength;
import mir.qualifier;
import mir.rc.context;
import mir.type_info;
import std.traits;

package static immutable allocationExcMsg = "mir_rcarray: out of memory error.";

version (D_Exceptions)
{
    import core.exception: OutOfMemoryError;
    package static immutable allocationError = new OutOfMemoryError(allocationExcMsg);
}

/++
Thread safe reference counting array.

The implementation never adds roots into the GC.
+/
struct mir_rcarray(T)
{
    ///
    package T* _payload;
    package ref mir_rc_context context() inout scope return pure nothrow @nogc @trusted @property
    {
        assert(_payload);
        return (cast(mir_rc_context*)_payload)[-1];
    }
    package void _reset() { _payload = null; }

    package alias ThisTemplate = .mir_rcarray;
    package alias _thisPtr = _payload;

    ///
    alias serdeKeysProxy = T;

    ///
    void proxySwap(ref typeof(this) rhs) pure nothrow @nogc @safe
    {
        auto t = this._payload;
        this._payload = rhs._payload;
        rhs._payload = t;
    }

    ///
    this(typeof(null))
    {
    }

    ///
    mixin CommonRCImpl;

    ///
    pragma(inline, true)
    bool opEquals(typeof(null)) @safe scope const pure nothrow @nogc
    {
        return !this;
    }

    /// ditto
    bool opEquals(Y)(auto ref scope const ThisTemplate!Y rhs) @safe scope const pure nothrow @nogc
    {
        return opIndex() == rhs.opIndex();
    }

    ///
    int opCmp(Y)(auto ref scope const ThisTemplate!Y rhs) @trusted scope const pure nothrow @nogc
    {
        return __cmp(opIndex(), rhs.opIndex());
    }

    ///
    size_t toHash() @trusted scope const pure nothrow @nogc
    {
        return hashOf(opIndex());
    }

    ///
    ~this() nothrow
    {
        static if (hasElaborateDestructor!T || hasDestructor!T)
        {
            if (false) // break @safe and pure attributes
            {
                Unqual!T* object;
                (*object).__xdtor;
            }
        }
        if (this)
        {
            (() @trusted { mir_rc_decrease_counter(context); })();
        }
    }

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

    ///
    size_t opDollar(size_t pos : 0)() @trusted scope pure nothrow @nogc const
    {
        return length;
    }

    ///
    auto asSlice() @property
    {
        import mir.ndslice.slice: mir_slice;
        alias It = mir_rci!T;
        return mir_slice!It([length], It(this));
    }

    ///
    auto asSlice() const @property
    {
        import mir.ndslice.slice: mir_slice;
        alias It = mir_rci!(const T);
        return mir_slice!It([length], It(this.lightConst));
    }

    ///
    auto asSlice() immutable @property
    {
        import mir.ndslice.slice: mir_slice;
        alias It = mir_rci!(immutable T);
        return mir_slice!It([length], It(this.lightImmutable));
    }

    ///
    auto moveToSlice() @property
    {
        import core.lifetime: move;
        import mir.ndslice.slice: mir_slice;
        alias It = mir_rci!T;
        return mir_slice!It([length], It(move(this)));
    }

    /++
    Params:
        length = array length
        initialize = Flag, don't initialize memory with default value if `false`.
        deallocate = Flag, never deallocates memory if `false`.
    +/
    this(size_t length, bool initialize = true, bool deallocate = true) @trusted @nogc
    {
        if (length == 0)
            return;
        Unqual!T[] ar;
        () @trusted {
            static if (is(T == class) || is(T == interface))
                auto ctx = mir_rc_create(mir_get_type_info!T, length, mir_get_payload_ptr!T, initialize, deallocate);
            else
                auto ctx = mir_rc_create(mir_get_type_info!T, length, mir_get_payload_ptr!T, initialize, deallocate);
            if (!ctx)
            {
                version(D_Exceptions)
                    throw allocationError;
                else
                    assert(0, allocationExcMsg);
            }
            _payload = cast(T*)(ctx + 1);
            ar = cast(Unqual!T[])_payload[0 .. length];
        } ();
        if (initialize || hasElaborateAssign!(Unqual!T))
        {
            import mir.conv: uninitializedFillDefault;
            uninitializedFillDefault(ar);
        }
    }

    static if (isImplicitlyConvertible!(const T, T))
        static if (isImplicitlyConvertible!(const Unqual!T, T))
            package alias V = const Unqual!T;
        else
            package alias V = const T;
    else
        package alias V = T;

    static if (is(T == const) || is(T == immutable))
    this(return ref scope const typeof(this) rhs) @trusted pure nothrow @nogc
    {
        if (rhs)
        {
            this._payload = cast(typeof(this._payload))rhs._payload;
            mir_rc_increase_counter(context);
        }
    }

    static if (is(T == immutable))
    this(return ref scope const typeof(this) rhs) immutable @trusted pure nothrow @nogc
    {
        if (rhs)
        {
            this._payload = cast(typeof(this._payload))rhs._payload;
            mir_rc_increase_counter(context);
        }
    }

    static if (is(T == immutable))
    this(return ref scope const typeof(this) rhs) const @trusted pure nothrow @nogc
    {
        if (rhs)
        {
            this._payload = cast(typeof(this._payload))rhs._payload;
            mir_rc_increase_counter(context);
        }
    }

    this(return ref scope inout typeof(this) rhs) inout @trusted pure nothrow @nogc
    {
        if (rhs)
        {
            this._payload = rhs._payload;
            mir_rc_increase_counter(context);
        }
    }

    ///
    ref opAssign(typeof(null)) return @trusted // pure nothrow @nogc
    {
        this = typeof(this).init;
    }

    ///
    ref opAssign(return typeof(this) rhs) return @trusted // pure nothrow @nogc
    {
        this.proxySwap(rhs);
        return this;
    }

    ///
    ref opAssign(Q)(return ThisTemplate!Q rhs) return @trusted // pure nothrow @nogc
        if (isImplicitlyConvertible!(Q*, T*))
    {
        this.proxySwap(*()@trusted{return cast(typeof(this)*)&rhs;}());
        return this;
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

package template LikeArray(Range)
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
    if (is(T == void) && !is(Range == LightScopeOf!Range))
{
    return .rcarray(range.lightScope);
}

/// ditto
auto rcarray(T = void, Range)(Range range)
    if (is(T == void) && isIterable!Range && is(Range == LightScopeOf!Range) && !isArray!Range)
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
    return .rcarray!V(values, deallocate);
}

/// ditto
RCArray!V rcarray(T = void, V)(scope V[] values, bool deallocate)
    if (is(T == void) && !hasIndirections!V)
{
    return .rcarray!V(values, deallocate);
}

/// ditto
template rcarray(T)
    if(!is(T == E[], E) && !is(T == void))
{
    import std.range.primitives: isInputRange, isInfinite;

    ///
    auto rcarray(Range)(ref Range range)
        if (!is(Range == LightScopeOf!Range))
    {
        return .rcarray!T(range.lightScope);
    }

    /// ditto
    auto rcarray(Range)(Range range)
        if ((isInputRange!Range || isIterable!Range) && !isInfinite!Range && !isArray!Range || isPointer!Range && (isInputRange!(PointerTarget!Range) || isIterable!(PointerTarget!Range)))
    {
        static if (LikeArray!Range)
        {
            return .rcarray!T(range.field);
        }
        else static if (hasLength!Range)
        {
            import mir.conv: emplaceRef;
            auto ret = RCArray!T(range.length, false);
            size_t i;
            static if (isInputRange!Range)
                for (; !range.empty; range.popFront)
                    ret[i++].emplaceRef!T(range.front);
            else
            static if (isPointer!Range)
                foreach (e; *range)
                    ret[i++].emplaceRef!T(e);
            else
                foreach (e; range)
                    ret[i++].emplaceRef!T(e);
            return ret;
        }
        else
        {
            import mir.appender: ScopedBuffer;
            import mir.conv: emplaceRef;
            ScopedBuffer!T a;
            static if (isInputRange!Range)
                for (; !range.empty; range.popFront)
                    a.put(range.front);
            else
            static if (isPointer!Range)
                foreach (e; *range)
                    a.put(e);
            else
                foreach (e; range)
                    a.put(e);
            scope values = a.data;
            auto ret = RCArray!T(values.length, false);
            ()@trusted {
                a.moveDataAndEmplaceTo(ret[]);
            }();
            return ret;
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
        static if (!hasElaborateAssign!(Unqual!T) && is(Unqual!V == Unqual!T))
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

    /// ditto
    RCArray!T rcarray(V)(scope V[] values, bool deallocate)
        if (!hasIndirections!V)
    {
        auto ret = mir_rcarray!T(values.length, false);
        static if (!hasElaborateAssign!(Unqual!T) && is(Unqual!V == Unqual!T))
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

/// With Input Ranges
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import mir.algorithm.iteration: filter;
    static immutable numbers = [3, 2, 5, 2, 3, 7, 3];
    static immutable filtered = [5.0, 7];
    auto result = numbers.filter!"a > 3".rcarray!(immutable double);
    static assert(is(typeof(result) == RCArray!(immutable double)));
    assert (result[] == filtered);
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
    import mir.ndslice.slice: Slice;
    import mir.ndslice.iterator: IotaIterator;

    ///
    T* _iterator;

    ///
    RCArray!T _array;

    ///
    this(RCArray!T array)
    {
        this._iterator = (()@trusted => array.ptr)();
        this._array.proxySwap(array);
    }

    ///
    this(T* _iterator, RCArray!T array)
    {
        this._iterator = _iterator;
        this._array.proxySwap(array);
    }

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
    ref opAssign(typeof(null)) scope return nothrow
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
    ref opAssign(Q)(return mir_rci!Q rhs) scope return nothrow
        if (isImplicitlyConvertible!(Q*, T*))
    {
        import core.lifetime: move;
        _iterator = rhs._iterator;
        _array = move(rhs._array);
        return this;
    }

    ///
    mir_rci!(const T) lightConst()() scope return const nothrow @property
    { return typeof(return)(_iterator, _array.lightConst); }

    ///
    mir_rci!(immutable T) lightImmutable()() scope return immutable nothrow @property
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

    /// Returns: slice type of `Slice!(IotaIterator!size_t)`
    Slice!(IotaIterator!size_t) opSlice(size_t dimension)(size_t i, size_t j) @safe scope const
        if (dimension == 0)
    in
    {
        assert(i <= j, "RCI!T.opSlice!0: the left opSlice boundary must be less than or equal to the right bound.");
    }
    do
    {
        return typeof(return)(j - i, typeof(return).Iterator(i));
    }

    /// Returns: ndslice on top of the refcounted iterator
    auto opIndex(Slice!(IotaIterator!size_t) slice)
    {
        import core.lifetime: move;
        auto it = this;
        it += slice._iterator._index;
        return Slice!(RCI!T)(slice.length, it.move);
    }

    /// ditto
    auto opIndex(Slice!(IotaIterator!size_t) slice) const
    {
        import core.lifetime: move;
        auto it = lightConst;
        it += slice._iterator._index;
        return Slice!(RCI!(const T))(slice.length,  it.move);
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
    auto slice = mir_rcarray!double(10).asSlice;
    static assert(isIterator!(RCI!double));
    static assert(is(typeof(slice) == Slice!(RCI!double)));
    auto matrix = slice.sliced(2, 5);
    static assert(is(typeof(matrix) == Slice!(RCI!double, 2)));
    slice[7] = 44;
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

version(mir_test)
unittest
{
    import mir.small_string;
    alias S = SmallString!32u;
    auto ars = [S("123"), S("422")];
    alias R = mir_rcarray!S;
    auto rc = ars.rcarray!S;

    RCArray!int value = null;
    value = null;
}

