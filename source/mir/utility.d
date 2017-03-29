/++
Generic utilities.

$(BOOKTABLE Cheat Sheet,
$(TR $(TH Function Name) $(TH Description))
$(T2 swap, Swaps two values.)
$(T2 min, Minimum value.)
$(T2 max, Maximum value.)
)

Copyright: Andrei Alexandrescu 2008-2016, Ilya Yaroshenko 2016-.
License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: $(HTTP erdani.com, Andrei Alexandrescu) (original std.* modules), Ilya Yaroshenko
Macros:
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.utility;

import std.traits;

import mir.internal.utility;

@fastmath:

void swapStars(I1, I2)(auto ref I1 i1, auto ref I2 i2)
{
    static if (__traits(compiles, swap(*i1, *i2)))
    {
        swap(*i1, *i2);
    }
    else
    {
        auto e = *i1;
        i1[0] = *i2;
        i2[0] = e;
    }
}

/++
Swaps `lhs` and `rhs`. The instances `lhs` and `rhs` are moved in
memory, without ever calling `opAssign`, nor any other function. `T`
need not be assignable at all to be swapped.
If `lhs` and `rhs` reference the same instance, then nothing is done.
`lhs` and `rhs` must be mutable. If `T` is a struct or union, then
its fields must also all be (recursively) mutable.
Params:
    lhs = Data to be swapped with `rhs`.
    rhs = Data to be swapped with `lhs`.
+/
void swap(T)(ref T lhs, ref T rhs) @trusted pure nothrow @nogc
if (isBlitAssignable!T && !is(typeof(lhs.proxySwap(rhs))))
{
    static if (hasElaborateAssign!T || !isAssignable!T)
    {
        if (&lhs != &rhs)
        {
            // For structs with non-trivial assignment, move memory directly
            ubyte[T.sizeof] t = void;
            auto a = (cast(ubyte*) &lhs)[0 .. T.sizeof];
            auto b = (cast(ubyte*) &rhs)[0 .. T.sizeof];
            t[] = a[];
            a[] = b[];
            b[] = t[];
        }
    }
    else
    {
        //Avoid assigning overlapping arrays. Dynamic arrays are fine, because
        //it's their ptr and length properties which get assigned rather
        //than their elements when assigning them, but static arrays are value
        //types and therefore all of their elements get copied as part of
        //assigning them, which would be assigning overlapping arrays if lhs
        //and rhs were the same array.
        static if (isStaticArray!T)
        {
            if (lhs.ptr == rhs.ptr)
                return;
        }

        // For non-struct types, suffice to do the classic swap
        auto tmp = lhs;
        lhs = rhs;
        rhs = tmp;
    }
}


///
@safe unittest
{
    // Swapping POD (plain old data) types:
    int a = 42, b = 34;
    swap(a, b);
    assert(a == 34 && b == 42);

    // Swapping structs with indirection:
    static struct S { int x; char c; int[] y; }
    S s1 = { 0, 'z', [ 1, 2 ] };
    S s2 = { 42, 'a', [ 4, 6 ] };
    swap(s1, s2);
    assert(s1.x == 42);
    assert(s1.c == 'a');
    assert(s1.y == [ 4, 6 ]);

    assert(s2.x == 0);
    assert(s2.c == 'z');
    assert(s2.y == [ 1, 2 ]);

    // Immutables cannot be swapped:
    immutable int imm1, imm2;
    static assert(!__traits(compiles, swap(imm1, imm2)));
}

///
@safe unittest
{
    // Non-copyable types can still be swapped.
    static struct NoCopy
    {
        this(this) { assert(0); }
        int n;
        string s;
    }
    NoCopy nc1, nc2;
    nc1.n = 127; nc1.s = "abc";
    nc2.n = 513; nc2.s = "uvwxyz";

    swap(nc1, nc2);
    assert(nc1.n == 513 && nc1.s == "uvwxyz");
    assert(nc2.n == 127 && nc2.s == "abc");

    swap(nc1, nc1);
    swap(nc2, nc2);
    assert(nc1.n == 513 && nc1.s == "uvwxyz");
    assert(nc2.n == 127 && nc2.s == "abc");

    // Types containing non-copyable fields can also be swapped.
    static struct NoCopyHolder
    {
        NoCopy noCopy;
    }
    NoCopyHolder h1, h2;
    h1.noCopy.n = 31; h1.noCopy.s = "abc";
    h2.noCopy.n = 65; h2.noCopy.s = null;

    swap(h1, h2);
    assert(h1.noCopy.n == 65 && h1.noCopy.s == null);
    assert(h2.noCopy.n == 31 && h2.noCopy.s == "abc");

    swap(h1, h1);
    swap(h2, h2);
    assert(h1.noCopy.n == 65 && h1.noCopy.s == null);
    assert(h2.noCopy.n == 31 && h2.noCopy.s == "abc");

    // Const types cannot be swapped.
    const NoCopy const1, const2;
    static assert(!__traits(compiles, swap(const1, const2)));
}

@safe unittest
{
    //Bug# 4789
    int[1] s = [1];
    swap(s, s);

    int[3] a = [1, 2, 3];
    swap(a[1], a[2]);
    assert(a == [1, 3, 2]);
}

@safe unittest
{
    static struct NoAssign
    {
        int i;
        void opAssign(NoAssign) @disable;
    }
    auto s1 = NoAssign(1);
    auto s2 = NoAssign(2);
    swap(s1, s2);
    assert(s1.i == 2);
    assert(s2.i == 1);
}

@safe unittest
{
    struct S
    {
        const int i;
    }
    S s;
    static assert(!__traits(compiles, swap(s, s)));
}

unittest
{
    static struct A
    {
        int* x;
        this(this) { x = new int; }
    }
    A a1, a2;
    swap(a1, a2);

    static struct B
    {
        int* x;
        void opAssign(B) { x = new int; }
    }
    B b1, b2;
    swap(b1, b2);
}

/// ditto
void swap(T)(ref T lhs, ref T rhs)
    if (is(typeof(lhs.proxySwap(rhs))))
{
    lhs.proxySwap(rhs);
}

// Equivalent with TypeStruct::isAssignable in compiler code.
package template isBlitAssignable(T)
{
    static if (is(OriginalType!T U) && !is(T == U))
    {
        enum isBlitAssignable = isBlitAssignable!U;
    }
    else static if (isStaticArray!T && is(T == E[n], E, size_t n))
    // Workaround for issue 11499 : isStaticArray!T should not be necessary.
    {
        enum isBlitAssignable = isBlitAssignable!E;
    }
    else static if (is(T == struct) || is(T == union))
    {
        enum isBlitAssignable = isMutable!T &&
        {
            size_t offset = 0;
            bool assignable = true;
            foreach (i, F; FieldTypeTuple!T)
            {
                static if (i == 0)
                {
                }
                else
                {
                    if (T.tupleof[i].offsetof == offset)
                    {
                        if (assignable)
                            continue;
                    }
                    else
                    {
                        if (!assignable)
                            return false;
                    }
                }
                assignable = isBlitAssignable!(typeof(T.tupleof[i]));
                offset = T.tupleof[i].offsetof;
            }
            return assignable;
        }();
    }
    else
        enum isBlitAssignable = isMutable!T;
}

@safe unittest
{
    static assert( isBlitAssignable!int);
    static assert(!isBlitAssignable!(const int));

    class C{ const int i; }
    static assert( isBlitAssignable!C);

    struct S1{ int i; }
    struct S2{ const int i; }
    static assert( isBlitAssignable!S1);
    static assert(!isBlitAssignable!S2);

    struct S3X { union {       int x;       int y; } }
    struct S3Y { union {       int x; const int y; } }
    struct S3Z { union { const int x; const int y; } }
    static assert( isBlitAssignable!(S3X));
    static assert( isBlitAssignable!(S3Y));
    static assert(!isBlitAssignable!(S3Z));
    static assert(!isBlitAssignable!(const S3X));
    static assert(!isBlitAssignable!(inout S3Y));
    static assert(!isBlitAssignable!(immutable S3Z));
    static assert( isBlitAssignable!(S3X[3]));
    static assert( isBlitAssignable!(S3Y[3]));
    static assert(!isBlitAssignable!(S3Z[3]));
    enum ES3X : S3X { a = S3X() }
    enum ES3Y : S3Y { a = S3Y() }
    enum ES3Z : S3Z { a = S3Z() }
    static assert( isBlitAssignable!(ES3X));
    static assert( isBlitAssignable!(ES3Y));
    static assert(!isBlitAssignable!(ES3Z));
    static assert(!isBlitAssignable!(const ES3X));
    static assert(!isBlitAssignable!(inout ES3Y));
    static assert(!isBlitAssignable!(immutable ES3Z));
    static assert( isBlitAssignable!(ES3X[3]));
    static assert( isBlitAssignable!(ES3Y[3]));
    static assert(!isBlitAssignable!(ES3Z[3]));

    union U1X {       int x;       int y; }
    union U1Y {       int x; const int y; }
    union U1Z { const int x; const int y; }
    static assert( isBlitAssignable!(U1X));
    static assert( isBlitAssignable!(U1Y));
    static assert(!isBlitAssignable!(U1Z));
    static assert(!isBlitAssignable!(const U1X));
    static assert(!isBlitAssignable!(inout U1Y));
    static assert(!isBlitAssignable!(immutable U1Z));
    static assert( isBlitAssignable!(U1X[3]));
    static assert( isBlitAssignable!(U1Y[3]));
    static assert(!isBlitAssignable!(U1Z[3]));
    enum EU1X : U1X { a = U1X() }
    enum EU1Y : U1Y { a = U1Y() }
    enum EU1Z : U1Z { a = U1Z() }
    static assert( isBlitAssignable!(EU1X));
    static assert( isBlitAssignable!(EU1Y));
    static assert(!isBlitAssignable!(EU1Z));
    static assert(!isBlitAssignable!(const EU1X));
    static assert(!isBlitAssignable!(inout EU1Y));
    static assert(!isBlitAssignable!(immutable EU1Z));
    static assert( isBlitAssignable!(EU1X[3]));
    static assert( isBlitAssignable!(EU1Y[3]));
    static assert(!isBlitAssignable!(EU1Z[3]));

    struct SA
    {
        @property int[3] foo() { return [1,2,3]; }
        alias foo this;
        const int x;    // SA is not blit assignable
    }
    static assert(!isStaticArray!SA);
    static assert(!isBlitAssignable!(SA[3]));
}

/++
Iterates the passed arguments and returns the minimum value.
Params: args = The values to select the minimum from. At least two arguments
    must be passed, and they must be comparable with `<`.
Returns: The minimum of the passed-in values.
+/
auto min(T...)(T args)
    if (T.length >= 2)
{
    //Get "a"
    static if (T.length <= 2)
        alias a = args[0];
    else
        auto a = min(args[0 .. ($+1)/2]);
    alias T0 = typeof(a);

    //Get "b"
    static if (T.length <= 3)
        alias b = args[$-1];
    else
        auto b = min(args[($+1)/2 .. $]);
    alias T1 = typeof(b);

    static assert (is(typeof(a < b)), "Invalid arguments: Cannot compare types " ~ T0.stringof ~ " and " ~ T1.stringof ~ ".");

    static if ((isFloatingPoint!T0 && isNumeric!T1) || (isFloatingPoint!T1 && isNumeric!T0))
    {
        version (LDC)
        {
            import ldc.intrinsics: llvm_minnum;
            return llvm_minnum(a, b);
        }
        else
        {
            import std.math: fmin;
            return cast(CommonType!(T0, T1))fmin(a, b);
        }
    }
    else
    {
        static if (isIntegral!T0 && isIntegral!T1)
            static assert(isSigned!T0 == isSigned!T1, 
                "mir.utility.min is not defined for signed + unsigned pairs because of security reasons."
                ~ "Please unify type or use a Phobos analog.");
        //Do the "min" proper with a and b
        return a < b ? a : b;
    }
}

@safe unittest
{
    int a = 5;
    short b = 6;
    double c = 2;
    auto d = min(a, b);
    static assert(is(typeof(d) == int));
    assert(d == 5);
    auto e = min(a, b, c);
    static assert(is(typeof(e) == double));
    assert(e == 2);
}

/++
`min` is not defined for arguments of mixed signedness because of security reasons.
Please unify type or use a Phobos analog.
+/
unittest
{
    int a = -10;
    uint b = 10;
    static assert(!is(typeof(min(a, b))));
}


/++
Iterates the passed arguments and returns the minimum value.
Params: args = The values to select the minimum from. At least two arguments
    must be passed, and they must be comparable with `<`.
Returns: The minimum of the passed-in values.
+/
auto max(T...)(T args)
    if (T.length >= 2)
{
    //Get "a"
    static if (T.length <= 2)
        alias a = args[0];
    else
        auto a = max(args[0 .. ($+1)/2]);
    alias T0 = typeof(a);

    //Get "b"
    static if (T.length <= 3)
        alias b = args[$-1];
    else
        auto b = max(args[($+1)/2 .. $]);
    alias T1 = typeof(b);

    static assert (is(typeof(a < b)), "Invalid arguments: Cannot compare types " ~ T0.stringof ~ " and " ~ T1.stringof ~ ".");

    static if ((isFloatingPoint!T0 && isNumeric!T1) || (isFloatingPoint!T1 && isNumeric!T0))
    {
        version (LDC)
        {
            import ldc.intrinsics: llvm_maxnum;
            return llvm_maxnum(a, b);
        }
        else
        {
            import std.math: fmax;
            return cast(CommonType!(T0, T1))fmax(a, b);
        }
    }
    else
    {
        static if (isIntegral!T0 && isIntegral!T1)
            static assert(isSigned!T0 == isSigned!T1, 
                "mir.utility.max is not defined for signed + unsigned pairs because of security reasons."
                ~ "Please unify type or use a Phobos analog.");
        //Do the "max" proper with a and b
        return a > b ? a : b;
    }
}

///
@safe unittest
{
    int a = 5;
    short b = 6;
    double c = 2;
    auto d = max(a, b);
    static assert(is(typeof(d) == int));
    assert(d == 6);
    auto e = min(a, b, c);
    static assert(is(typeof(e) == double));
    assert(e == 2);
}

/++
`max` is not defined for arguments of mixed signedness because of security reasons.
Please unify type or use a Phobos analog.
+/
unittest
{
    int a = -10;
    uint b = 10;
    static assert(!is(typeof(max(a, b))));
}
