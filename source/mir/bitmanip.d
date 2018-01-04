/++
Bit-level manipulation facilities.

$(SCRIPT inhibitQuickIndex = 1;)
$(BOOKTABLE,
$(TR $(TH Category) $(TH Functions))
$(TR $(TD Bit constructs) $(TD
    $(LREF bitfields)
))
$(TR $(TD Tagging) $(TD
    $(LREF taggedClassRef)
    $(LREF taggedPointer)
))
)

Copyright: Copyright Digital Mars 2007 - 2011.
License:   $(HTTP www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors:   $(HTTP digitalmars.com, Walter Bright),
           $(HTTP erdani.org, Andrei Alexandrescu),
           Amaury SECHET
+/
module mir.bitmanip;

import std.traits;

private string myToString()(ulong n)
{
    UnsignedStringBuf buf;
    auto s = unsignedToTempString(n, buf);
    return s ~ (n > uint.max ? "UL" : "U");
}

private alias UnsignedStringBuf = char[20];

private string unsignedToTempString()(ulong value, char[] buf, uint radix = 10) @safe
{
    size_t i = buf.length;
    do
    {
        ubyte x = cast(ubyte)(value % radix);
        value = value / radix;
        buf[--i] = cast(char)((x < 10) ? x + '0' : x - 10 + 'a');
    } while (value);
    return buf[i .. $].idup;
}

private template createAccessors(
    string store, T, string name, size_t len, size_t offset)
{
    static if (!name.length)
    {
        // No need to create any accessor
        enum result = "";
    }
    else static if (len == 0)
    {
        // Fields of length 0 are always zero
        enum result = "enum "~T.stringof~" "~name~" = 0;\n";
    }
    else
    {
        enum ulong
            maskAllElse = ((~0uL) >> (64 - len)) << offset,
            signBitCheck = 1uL << (len - 1);

        static if (T.min < 0)
        {
            enum long minVal = -(1uL << (len - 1));
            enum ulong maxVal = (1uL << (len - 1)) - 1;
            alias UT = Unsigned!(T);
            enum UT extendSign = cast(UT)~((~0uL) >> (64 - len));
        }
        else
        {
            enum ulong minVal = 0;
            enum ulong maxVal = (~0uL) >> (64 - len);
            enum extendSign = 0;
        }

        static if (is(T == bool))
        {
            static assert(len == 1);
            enum result =
            // getter
                "@property bool " ~ name ~ "()() @safe pure nothrow @nogc const { return "
                ~"("~store~" & "~myToString(maskAllElse)~") != 0;}\n"
            // setter
                ~"@property void " ~ name ~ "()(bool v) @safe pure nothrow @nogc { "
                ~"if (v) "~store~" |= "~myToString(maskAllElse)~";"
                ~"else "~store~" &= cast(typeof("~store~"))(-1-cast(typeof("~store~"))"~myToString(maskAllElse)~");}\n";
        }
        else
        {
            // getter
            enum result = "@property "~T.stringof~" "~name~"()() @safe pure nothrow @nogc const { auto result = "
                ~"("~store~" & "
                ~ myToString(maskAllElse) ~ ") >>"
                ~ myToString(offset) ~ ";"
                ~ (T.min < 0
                   ? "if (result >= " ~ myToString(signBitCheck)
                   ~ ") result |= " ~ myToString(extendSign) ~ ";"
                   : "")
                ~ " return cast("~T.stringof~") result;}\n"
            // setter
                ~"@property void "~name~"()("~T.stringof~" v) @safe pure nothrow @nogc { "
                ~"assert(v >= "~name~`_min, "Value is smaller than the minimum value of bitfield '`~name~`'"); `
                ~"assert(v <= "~name~`_max, "Value is greater than the maximum value of bitfield '`~name~`'"); `
                ~store~" = cast(typeof("~store~"))"
                ~" (("~store~" & (-1-cast(typeof("~store~"))"~myToString(maskAllElse)~"))"
                ~" | ((cast(typeof("~store~")) v << "~myToString(offset)~")"
                ~" & "~myToString(maskAllElse)~"));}\n"
            // constants
                ~"enum "~T.stringof~" "~name~"_min = cast("~T.stringof~")"
                ~myToString(minVal)~"; "
                ~" enum "~T.stringof~" "~name~"_max = cast("~T.stringof~")"
                ~myToString(maxVal)~"; ";
        }
    }
}

private template createStoreName(Ts...)
{
    static if (Ts.length < 2)
        enum createStoreName = "";
    else
        enum createStoreName = "_" ~ Ts[1] ~ createStoreName!(Ts[3 .. $]);
}

private template createStorageAndFields(Ts...)
{
    enum Name = createStoreName!Ts;
    enum Size = sizeOfBitField!Ts;
    static if (Size == ubyte.sizeof * 8)
        alias StoreType = ubyte;
    else static if (Size == ushort.sizeof * 8)
        alias StoreType = ushort;
    else static if (Size == uint.sizeof * 8)
        alias StoreType = uint;
    else static if (Size == ulong.sizeof * 8)
        alias StoreType = ulong;
    else
    {
        static assert(false, "Field widths must sum to 8, 16, 32, or 64");
        alias StoreType = ulong; // just to avoid another error msg
    }
    enum result
        = "private " ~ StoreType.stringof ~ " " ~ Name ~ ";"
        ~ createFields!(Name, 0, Ts).result;
}

private template createFields(string store, size_t offset, Ts...)
{
    static if (Ts.length > 0)
        enum result
            = createAccessors!(store, Ts[0], Ts[1], Ts[2], offset).result
            ~ createFields!(store, offset + Ts[2], Ts[3 .. $]).result;
    else
        enum result = "";
}

private ulong getBitsForAlign()(ulong a)
{
    ulong bits = 0;
    while ((a & 0x01) == 0)
    {
        bits++;
        a >>= 1;
    }
    assert(a == 1, "alignment is not a power of 2");
    return bits;
}

private template createReferenceAccessor(string store, T, ulong bits, string name)
{
    enum storage = "private void* " ~ store ~ "_ptr;\n";
    enum storage_accessor = "@property ref size_t " ~ store ~ "()() return @trusted pure nothrow @nogc const { "
        ~ "return *cast(size_t*) &" ~ store ~ "_ptr;}\n"
        ~ "@property void " ~ store ~ "()(size_t v) @trusted pure nothrow @nogc { "
        ~ "" ~ store ~ "_ptr = cast(void*) v;}\n";

    enum mask = (1UL << bits) - 1;
    // getter
    enum ref_accessor = "@property "~T.stringof~" "~name~"()() @trusted pure nothrow @nogc const { auto result = "
        ~ "("~store~" & "~myToString(~mask)~"); "
        ~ "return cast("~T.stringof~") cast(void*) result;}\n"
    // setter
        ~"@property void "~name~"()("~T.stringof~" v) @trusted pure nothrow @nogc { "
        ~"assert(((cast(typeof("~store~")) cast(void*) v) & "~myToString(mask)
        ~`) == 0, "Value not properly aligned for '`~name~`'"); `
        ~store~" = cast(typeof("~store~"))"
        ~" (("~store~" & (cast(typeof("~store~")) "~myToString(mask)~"))"
        ~" | ((cast(typeof("~store~")) cast(void*) v) & (cast(typeof("~store~")) "~myToString(~mask)~")));}\n";

    enum result = storage ~ storage_accessor ~ ref_accessor;
}

private template sizeOfBitField(T...)
{
    static if (T.length < 2)
        enum sizeOfBitField = 0;
    else
        enum sizeOfBitField = T[2] + sizeOfBitField!(T[3 .. $]);
}

private template createTaggedReference(T, ulong a, string name, Ts...)
{
    static assert(
        sizeOfBitField!Ts <= getBitsForAlign(a),
        "Fields must fit in the bits know to be zero because of alignment."
    );
    enum StoreName = createStoreName!(T, name, 0, Ts);
    enum result
        = createReferenceAccessor!(StoreName, T, sizeOfBitField!Ts, name).result
        ~ createFields!(StoreName, 0, Ts, size_t, "", T.sizeof * 8 - sizeOfBitField!Ts).result;
}

/**
Allows creating bit fields inside $(D_PARAM struct)s and $(D_PARAM
class)es.

Example:

----
struct A
{
    int a;
    mixin(bitfields!(
        uint, "x",    2,
        int,  "y",    3,
        uint, "z",    2,
        bool, "flag", 1));
}
A obj;
obj.x = 2;
obj.z = obj.x;
----

The example above creates a bitfield pack of eight bits, which fit in
one $(D_PARAM ubyte). The bitfields are allocated starting from the
least significant bit, i.e. x occupies the two least significant bits
of the bitfields storage.

The sum of all bit lengths in one $(D_PARAM bitfield) instantiation
must be exactly 8, 16, 32, or 64. If padding is needed, just allocate
one bitfield with an empty name.

Example:

----
struct A
{
    mixin(bitfields!(
        bool, "flag1",    1,
        bool, "flag2",    1,
        uint, "",         6));
}
----

The type of a bit field can be any integral type or enumerated
type. The most efficient type to store in bitfields is $(D_PARAM
bool), followed by unsigned types, followed by signed types.
*/

template bitfields(T...)
{
    enum { bitfields = createStorageAndFields!T.result }
}

/**
This string mixin generator allows one to create tagged pointers inside $(D_PARAM struct)s and $(D_PARAM class)es.

A tagged pointer uses the bits known to be zero in a normal pointer or class reference to store extra information.
For example, a pointer to an integer must be 4-byte aligned, so there are 2 bits that are always known to be zero.
One can store a 2-bit integer there.

The example above creates a tagged pointer in the struct A. The pointer is of type
$(D uint*) as specified by the first argument, and is named x, as specified by the second
argument.

Following arguments works the same way as $(D bitfield)'s. The bitfield must fit into the
bits known to be zero because of the pointer alignment.
*/

template taggedPointer(T : T*, string name, Ts...) {
    enum taggedPointer = createTaggedReference!(T*, T.alignof, name, Ts).result;
}

///
@safe version(mir_test) unittest
{
    struct A
    {
        int a;
        mixin(taggedPointer!(
            uint*, "x",
            bool, "b1", 1,
            bool, "b2", 1));
    }
    A obj;
    obj.x = new uint;
    obj.b1 = true;
    obj.b2 = false;
}

/**
This string mixin generator allows one to create tagged class reference inside $(D_PARAM struct)s and $(D_PARAM class)es.

A tagged class reference uses the bits known to be zero in a normal class reference to store extra information.
For example, a pointer to an integer must be 4-byte aligned, so there are 2 bits that are always known to be zero.
One can store a 2-bit integer there.

The example above creates a tagged reference to an Object in the struct A. This expects the same parameters
as $(D taggedPointer), except the first argument which must be a class type instead of a pointer type.
*/

template taggedClassRef(T, string name, Ts...)
if (is(T == class))
{
    enum taggedClassRef = createTaggedReference!(T, 8, name, Ts).result;
}

///
@safe version(mir_test) unittest
{
    struct A
    {
        int a;
        mixin(taggedClassRef!(
            Object, "o",
            uint, "i", 2));
    }
    A obj;
    obj.o = new Object();
    obj.i = 3;
}

@safe pure nothrow @nogc
version(mir_test) unittest
{
    // Degenerate bitfields (#8474 / #11160) tests mixed with range tests
    struct Test1
    {
        mixin(bitfields!(uint, "a", 32,
                        uint, "b", 4,
                        uint, "c", 4,
                        uint, "d", 8,
                        uint, "e", 16,));

        static assert(Test1.b_min == 0);
        static assert(Test1.b_max == 15);
    }

    struct Test2
    {
        mixin(bitfields!(bool, "a", 0,
                        ulong, "b", 64));

        static assert(Test2.b_min == ulong.min);
        static assert(Test2.b_max == ulong.max);
    }

    struct Test1b
    {
        mixin(bitfields!(bool, "a", 0,
                        int, "b", 8));
    }

    struct Test2b
    {
        mixin(bitfields!(int, "a", 32,
                        int, "b", 4,
                        int, "c", 4,
                        int, "d", 8,
                        int, "e", 16,));

        static assert(Test2b.b_min == -8);
        static assert(Test2b.b_max == 7);
    }

    struct Test3b
    {
        mixin(bitfields!(bool, "a", 0,
                        long, "b", 64));

        static assert(Test3b.b_min == long.min);
        static assert(Test3b.b_max == long.max);
    }

    struct Test4b
    {
        mixin(bitfields!(long, "a", 32,
                        int, "b", 32));
    }

    // Sign extension tests
    Test2b t2b;
    Test4b t4b;
    t2b.b = -5; assert(t2b.b == -5);
    t2b.d = -5; assert(t2b.d == -5);
    t2b.e = -5; assert(t2b.e == -5);
    t4b.a = -5; assert(t4b.a == -5L);
}

@system version(mir_test) unittest
{
    struct Test5
    {
        mixin(taggedPointer!(
            int*, "a",
            uint, "b", 2));
    }

    Test5 t5;
    t5.a = null;
    t5.b = 3;
    assert(t5.a is null);
    assert(t5.b == 3);

    int myint = 42;
    t5.a = &myint;
    assert(t5.a is &myint);
    assert(t5.b == 3);

    struct Test6
    {
        mixin(taggedClassRef!(
            Object, "o",
            bool, "b", 1));
    }

    Test6 t6;
    t6.o = null;
    t6.b = false;
    assert(t6.o is null);
    assert(t6.b == false);

    auto o = new Object();
    t6.o = o;
    t6.b = true;
    assert(t6.o is o);
    assert(t6.b == true);
}

@safe version(mir_test) unittest
{
    static assert(!__traits(compiles,
        taggedPointer!(
            int*, "a",
            uint, "b", 3)));

    static assert(!__traits(compiles,
        taggedClassRef!(
            Object, "a",
            uint, "b", 4)));

    struct S {
        mixin(taggedClassRef!(
            Object, "a",
            bool, "b", 1));
    }

    const S s;
    void bar(S s) {}

    static assert(!__traits(compiles, bar(s)));
}

@safe version(mir_test) unittest
{
    // Bug #6686
    union  S {
        ulong bits = ulong.max;
        mixin (bitfields!(
            ulong, "back",  31,
            ulong, "front", 33)
        );
    }
    S num;

    num.bits = ulong.max;
    num.back = 1;
    assert(num.bits == 0xFFFF_FFFF_8000_0001uL);
}

@safe version(mir_test) unittest
{
    // Bug #5942
    struct S
    {
        mixin(bitfields!(
            int, "a" , 32,
            int, "b" , 32
        ));
    }

    S data;
    data.b = 42;
    data.a = 1;
    assert(data.b == 42);
}

@safe version(mir_test) unittest
{
    struct Test
    {
        mixin(bitfields!(bool, "a", 1,
                         uint, "b", 3,
                         short, "c", 4));
    }

    @safe void test() pure nothrow
    {
        Test t;

        t.a = true;
        t.b = 5;
        t.c = 2;

        assert(t.a);
        assert(t.b == 5);
        assert(t.c == 2);
    }

    test();
}

@safe version(mir_test) unittest
{
    {
        static struct Integrals {
            bool checkExpectations(bool eb, int ei, short es) { return b == eb && i == ei && s == es; }

            mixin(bitfields!(
                      bool, "b", 1,
                      uint, "i", 3,
                      short, "s", 4));
        }
        Integrals i;
        assert(i.checkExpectations(false, 0, 0));
        i.b = true;
        assert(i.checkExpectations(true, 0, 0));
        i.i = 7;
        assert(i.checkExpectations(true, 7, 0));
        i.s = -8;
        assert(i.checkExpectations(true, 7, -8));
        i.s = 7;
        assert(i.checkExpectations(true, 7, 7));
    }

    //Bug# 8876
    {
        struct MoreIntegrals {
            bool checkExpectations(uint eu, ushort es, uint ei) { return u == eu && s == es && i == ei; }

            mixin(bitfields!(
                  uint, "u", 24,
                  short, "s", 16,
                  int, "i", 24));
        }

        MoreIntegrals i;
        assert(i.checkExpectations(0, 0, 0));
        i.s = 20;
        assert(i.checkExpectations(0, 20, 0));
        i.i = 72;
        assert(i.checkExpectations(0, 20, 72));
        i.u = 8;
        assert(i.checkExpectations(8, 20, 72));
        i.s = 7;
        assert(i.checkExpectations(8, 7, 72));
    }

    enum A { True, False }
    enum B { One, Two, Three, Four }
    static struct Enums {
        bool checkExpectations(A ea, B eb) { return a == ea && b == eb; }

        mixin(bitfields!(
                  A, "a", 1,
                  B, "b", 2,
                  uint, "", 5));
    }
    Enums e;
    assert(e.checkExpectations(A.True, B.One));
    e.a = A.False;
    assert(e.checkExpectations(A.False, B.One));
    e.b = B.Three;
    assert(e.checkExpectations(A.False, B.Three));

    static struct SingleMember {
        bool checkExpectations(bool eb) { return b == eb; }

        mixin(bitfields!(
                  bool, "b", 1,
                  uint, "", 7));
    }
    SingleMember f;
    assert(f.checkExpectations(false));
    f.b = true;
    assert(f.checkExpectations(true));
}

// Issue 12477
@system version(mir_test) unittest
{
    import std.algorithm.searching : canFind;
    import mir.bitmanip : bitfields;
    import core.exception : AssertError;

    static struct S
    {
        mixin(bitfields!(
            uint, "a", 6,
            int, "b", 2));
    }

    S s;

    try { s.a = uint.max; assert(0); }
    catch (AssertError ae)
    { assert(ae.msg.canFind("Value is greater than the maximum value of bitfield 'a'"), ae.msg); }

    try { s.b = int.min;  assert(0); }
    catch (AssertError ae)
    { assert(ae.msg.canFind("Value is smaller than the minimum value of bitfield 'b'"), ae.msg); }
}
