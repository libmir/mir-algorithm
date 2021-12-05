/**
Functions and types that manipulate built-in arrays and associative arrays.

This module provides all kinds of functions to create, manipulate or convert arrays:

$(SCRIPT inhibitQuickIndex = 1;)
$(BOOKTABLE ,
$(TR $(TH Function Name) $(TH Description)
)
    $(TR $(TD $(LREF _array))
        $(TD Returns a copy of the input in a newly allocated dynamic _array.
    ))
)

Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)

Authors: $(HTTP erdani.org, Andrei Alexandrescu) and Jonathan M Davis

Source: $(PHOBOSSRC std/_array.d)
*/
module mir.array.allocation;

import mir.functional;
import mir.primitives;
import std.traits;

/**
 * Allocates an array and initializes it with copies of the elements
 * of range $(D r).
 *
 * Narrow strings are handled as a special case in an overload.
 *
 * Params:
 *      r = range (or aggregate with $(D opApply) function) whose elements are copied into the allocated array
 * Returns:
 *      allocated and initialized array
 */
auto array(Range)(Range r)
if ((isInputRange!Range || isIterable!Range) && !isInfinite!Range && !__traits(isStaticArray, Range) || isPointer!Range && (isInputRange!(PointerTarget!Range) || isIterable!(PointerTarget!Range)))
{
    static if (isIterable!Range)
        alias E = ForeachType!Range;
    else
    static if (isPointer!Range && isIterable!(PointerTarget!Range))
        alias E = ForeachType!(PointerTarget!Range);
    else
        alias E = ElementType!Range;

    if (__ctfe)
    {
        // Compile-time version to avoid memcpy calls.
        // Also used to infer attributes of array().
        E[] result;
        static if (isInputRange!Range)
            for (; !r.empty; r.popFront)
                result ~= r.front;
        else
        static if (isPointer!Range)
            foreach (e; *r)
                result ~= e;
        else
            foreach (e; r)
                result ~= e;
        return result;
    }

    import mir.primitives: hasLength;

    static if (hasLength!Range)
    {
        auto length = r.length;
        if (length == 0)
            return null;

        import mir.conv : emplaceRef;
        import std.array: uninitializedArray;

        auto result = (() @trusted => uninitializedArray!(Unqual!E[])(length))();

        static if (isInputRange!Range)
        {
            foreach(ref e; result)
            {
                emplaceRef!E(e, r.front);
                r.popFront;
            }
        }
        else
        static if (isPointer!Range)
        {
            auto it = result;
            foreach(ref f; *r)
            {
                emplaceRef!E(it[0], f);
                it = it[1 .. $];
            }
        }
        else
        {
            auto it = result;
            foreach (f; r)
            {
                import mir.functional: forward;
                emplaceRef!E(it[0], forward!f);
                it = it[1 .. $];
            }
        }

        return (() @trusted => cast(E[]) result)();
    }
    else
    {
        import std.array: std_appender = appender;

        auto a = std_appender!(E[]);

        static if (isInputRange!Range)
            for (; !r.empty; r.popFront)
                a.put(r.front);
        else
        static if (isPointer!Range)
        {
            foreach (e; *r)
                a.put(forward!e);
        }
        else
        {
            foreach (e; r)
                a.put(forward!e);
        }
        return a.data;
    }
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto a = array([1, 2, 3, 4, 5][]);
    assert(a == [ 1, 2, 3, 4, 5 ]);
}

@safe pure nothrow version(mir_test) unittest
{
    import mir.algorithm.iteration : equal;
    struct Foo
    {
        int a;
    }
    auto a = array([Foo(1), Foo(2), Foo(3), Foo(4), Foo(5)][]);
    assert(equal(a, [Foo(1), Foo(2), Foo(3), Foo(4), Foo(5)]));
}

@safe pure nothrow version(mir_test) unittest
{
    struct MyRange
    {
        enum front = 123;
        enum empty = true;
        void popFront() {}
    }

    auto arr = (new MyRange).array;
    assert(arr.empty);
}

@system pure nothrow version(mir_test) unittest
{
    immutable int[] a = [1, 2, 3, 4];
    auto b = (&a).array;
    assert(b == a);
}

@system version(mir_test) unittest
{
    import mir.algorithm.iteration : equal;
    struct Foo
    {
        int a;
        void opAssign(Foo)
        {
            assert(0);
        }
        auto opEquals(Foo foo)
        {
            return a == foo.a;
        }
    }
    auto a = array([Foo(1), Foo(2), Foo(3), Foo(4), Foo(5)][]);
    assert(equal(a, [Foo(1), Foo(2), Foo(3), Foo(4), Foo(5)]));
}

@safe version(mir_test) unittest
{
    // Issue 12315
    static struct Bug12315 { immutable int i; }
    enum bug12315 = [Bug12315(123456789)].array();
    static assert(bug12315[0].i == 123456789);
}

@safe version(mir_test) unittest
{
    import mir.ndslice.topology: repeat;
    static struct S{int* p;}
    auto a = array(immutable(S).init.repeat(5));
    assert(a.length == 5);
}

///
@safe version(mir_test) unittest
{
    assert("Hello D".array == "Hello D");
    assert("Hello D"w.array == "Hello D"w);
    assert("Hello D"d.array == "Hello D"d);
}

@system version(mir_test) unittest
{
    // @system due to array!string
    import std.conv : to;

    static struct TestArray { int x; string toString() @safe { return to!string(x); } }

    static struct OpAssign
    {
        uint num;
        this(uint num) { this.num = num; }

        // Templating opAssign to make sure the bugs with opAssign being
        // templated are fixed.
        void opAssign(T)(T rhs) { this.num = rhs.num; }
    }

    static struct OpApply
    {
        int opApply(scope int delegate(ref int) dg)
        {
            int res;
            foreach (i; 0 .. 10)
            {
                res = dg(i);
                if (res) break;
            }

            return res;
        }
    }

    auto a = array([1, 2, 3, 4, 5][]);
    assert(a == [ 1, 2, 3, 4, 5 ]);

    auto b = array([TestArray(1), TestArray(2)][]);
    assert(b == [TestArray(1), TestArray(2)]);

    class C
    {
        int x;
        this(int y) { x = y; }
        override string toString() const @safe { return to!string(x); }
    }
    auto c = array([new C(1), new C(2)][]);
    assert(c[0].x == 1);
    assert(c[1].x == 2);

    auto d = array([1.0, 2.2, 3][]);
    assert(is(typeof(d) == double[]));
    assert(d == [1.0, 2.2, 3]);

    auto e = [OpAssign(1), OpAssign(2)];
    auto f = array(e);
    assert(e == f);

    assert(array(OpApply.init) == [0,1,2,3,4,5,6,7,8,9]);
    assert(array("ABC") == "ABC");
    assert(array("ABC".dup) == "ABC");
}

//Bug# 8233
@safe version(mir_test) unittest
{
    assert(array("hello world"d) == "hello world"d);
    immutable a = [1, 2, 3, 4, 5];
    assert(array(a) == a);
    const b = a;
    assert(array(b) == a);

    //To verify that the opAssign branch doesn't get screwed up by using Unqual.
    //EDIT: array no longer calls opAssign.
    struct S
    {
        ref S opAssign(S)(const ref S rhs)
        {
            assert(0);
        }

        int i;
    }

    alias AliasSeq(T...) = T;
    foreach (T; AliasSeq!(S, const S, immutable S))
    {
        auto arr = [T(1), T(2), T(3), T(4)];
        assert(array(arr) == arr);
    }
}

@safe version(mir_test) unittest
{
    //9824
    static struct S
    {
        @disable void opAssign(S);
        int i;
    }
    auto arr = [S(0), S(1), S(2)];
    arr.array;
}

// Bugzilla 10220
@safe version(mir_test) unittest
{
    import mir.algorithm.iteration : equal;
    import std.exception;
    import mir.ndslice.topology: repeat;

    static struct S
    {
        int val;

        @disable this();
        this(int v) { val = v; }
    }
    static immutable r = S(1).repeat(2).array();
    assert(equal(r, [S(1), S(1)]));
}

@safe version(mir_test) unittest
{
    //Turn down infinity:
    static assert(!is(typeof(
        repeat(1).array()
    )));
}
