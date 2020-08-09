module mir.serde;

import mir.functional: naryFun;
import mir.reflection: getUDA;
import std.traits: hasUDA, TemplateArgsOf;

/++
Attribute for key overloading during Serialization and Deserialization.
The first argument overloads the key value during serialization unless `serdeKeyOut` is given.
+/
struct serdeKeys
{
    ///
    immutable(char[])[] keys;

@safe pure nothrow:
    ///
    this(string[] keys...) { this.keys = keys.idup; }
    ///
    @disable this();
}

/++
Attribute for key overloading during serialization.
+/
struct serdeKeyOut
{
    ///
    string key;

@safe pure nothrow @nogc:
    ///
    this(string key) { this.key = key; }
}

/++
+/
template serdeGetKeysIn(alias symbol)
{
    static if (hasUDA!(symbol, serdeIgnore) || hasUDA!(symbol, serdeIgnoreIn))
        enum immutable(char[])[] serdeGetKeysIn = null;
    else
    static if (hasUDA!(symbol, serdeKeys))
        enum immutable(char[])[] serdeGetKeysIn = getUDA!(symbol, serdeKeys).keys;
    else
        enum immutable(char[])[] serdeGetKeysIn = [__traits(identifier, symbol)];
}

///
immutable(char[])[] serdeGetKeysIn(T)(T value)
    if (is(T == enum))
{
    import std.traits: EnumMembers;
    foreach (i, member; EnumMembers!T)
    {
        alias all = __traits(getAttributes, EnumMembers!T[i]);
        if (value == member)
            return .serdeGetKeysIn!(EnumMembers!T[i]);
    }
    assert(0);
}

///
version(mir_test)
unittest
{
    struct S
    {
        int f;

        @serdeKeys("D", "t")
        int d;

        @serdeIgnore
        int i;

        @serdeIgnoreIn
        int ii;

        @serdeIgnoreOut
        int io;

        void p(int) @property {}
    }

    static assert(serdeGetKeysIn!(S.f) == ["f"]);
    static assert(serdeGetKeysIn!(S.d) == ["D", "t"]);
    static assert(serdeGetKeysIn!(S.i) == null);
    static assert(serdeGetKeysIn!(S.ii) == null);
    static assert(serdeGetKeysIn!(S.io) == ["io"]);
    static assert(serdeGetKeysIn!(S.p) == ["p"]);
}

///
unittest
{
    enum E
    {
        @serdeKeys("A", "alpha")
        a,
        @serdeKeys("B", "beta")
        b,
        c,
    }

    static assert (serdeGetKeysIn(E.a) == ["A", "alpha"]);
    static assert (serdeGetKeysIn(E.c) == ["c"]);
}

/++
+/
template serdeGetKeyOut(alias symbol)
{
    static if (hasUDA!(symbol, serdeIgnore) || hasUDA!(symbol, serdeIgnoreOut))
        enum string serdeGetKeyOut = null;
    else
    static if (hasUDA!(symbol, serdeKeyOut))
        enum string serdeGetKeyOut = getUDA!(symbol, serdeKeyOut).key;
    else
    static if (hasUDA!(symbol, serdeKeys))
        enum string serdeGetKeyOut = getUDA!(symbol, serdeKeys).keys[0];
    else
        enum string serdeGetKeyOut = __traits(identifier, symbol);
}

///ditto
immutable(char)[] serdeGetKeyOut(T)(T value)
    if (is(T == enum))
{
    import std.traits: EnumMembers;
    foreach (i, member; EnumMembers!T)
    {
        alias all = __traits(getAttributes, EnumMembers!T[i]);
        if (value == member)
            return .serdeGetKeyOut!(EnumMembers!T[i]);
    }
    assert(0);
}

///
version(mir_test)
unittest
{
    struct S
    {
        int f;

        @serdeKeys("D", "t")
        int d;

        @serdeIgnore
        int i;

        @serdeIgnoreIn
        int ii;

        @serdeIgnoreOut
        int io;

        @serdeKeys("P")
        @serdeKeyOut("")
        void p(int) @property {}
    }

    static assert(serdeGetKeyOut!(S.f) == "f");
    static assert(serdeGetKeyOut!(S.d) == "D");
    static assert(serdeGetKeyOut!(S.i) is null);
    static assert(serdeGetKeyOut!(S.ii) == "ii");
    static assert(serdeGetKeyOut!(S.io) is null);
    static assert(serdeGetKeyOut!(S.p) !is null);
    static assert(serdeGetKeyOut!(S.p) == "");
}

///
unittest
{
    enum E
    {
        @serdeKeys("A", "alpha")
        a,
        @serdeKeys("B", "beta")
        @serdeKeyOut("o")
        b,
        c,
    }

    static assert (serdeGetKeyOut(E.a) == "A");
    static assert (serdeGetKeyOut(E.b) == "o");
    static assert (serdeGetKeyOut(E.c) == "c");
}

/++
Attribute to ignore field.
+/
enum serdeIgnore;

/++
Attribute to ignore field during deserialization.
+/
enum serdeIgnoreIn;

/++
Attribute to ignore field during serialization.
+/
enum serdeIgnoreOut;

/++
Attribute to ignore a field during deserialization when equals to its default value.
Do not use it on void initialized fields or aggregates with void initialized fields, recursively.
+/
enum serdeIgnoreDefault;

///
version(mir_test)
unittest
{
    struct S
    {
        @serdeIgnoreDefault
        double d = 0; // skips field if 0 during deserialization
    }

    import std.traits: hasUDA;

    static assert(hasUDA!(S.d, serdeIgnoreDefault));
}

/++
+/

/++
Serialization proxy.
+/
struct serdeProxy(T);

///
version(mir_test)
unittest
{
    import mir.small_string;

    struct S
    {
        @serdeProxy!(SmallString!32)
        double d;
    }

    import std.traits: hasUDA;

    static assert(hasUDA!(S.d, serdeProxy));
    static assert(hasUDA!(S.d, serdeProxy!(SmallString!32)));
    static assert(is(serdeGetProxy!(S.d) == SmallString!32));
}

/++
+/
alias serdeGetProxy(alias symbol) = TemplateArgsOf!(getUDA!(symbol, serdeProxy))[0];

/++
Can be applied only to fields that can be constructed from strings.
Does not allocate new data when deserializeing. Raw data is used for strings instead of new memory allocation.
Use this attributes only for strings that would not be used after the input data deallocation.
+/
enum serdeScopeStringProxy;

/++
Attributes to out conditional ignore field during serialization.

The predicate should be aplied to the aggregate type itself, not to the member.
+/
struct serdeIgnoreOutIf(alias pred);

/++
+/
alias serdeGetIgnoreOutIf(alias symbol) = naryFun!(TemplateArgsOf!(getUDA!(symbol, serdeIgnoreOutIf))[0]);

/++
Allows to use flexible deserialization rules such as conversion from input string to numeric types.
+/
enum serdeFlexible;

/++
Allows serialize / deserialize fields like arrays.

A range or a container should be iterable for serialization.
Following code should compile:
------
foreach(ref value; yourRangeOrContainer)
{
    ...
}
------

`put(value)` method is used for deserialization.

See_also: $(MREF serdeIgnoreOut), $(MREF serdeIgnoreIn)
+/
enum serdeLikeList;

/++
Allows serialize / deserialize fields like objects.

Object should have `opApply` method to allow serialization.
Following code should compile:
------
foreach(key, value; yourObject)
{
    ...
}
------
Object should have only one `opApply` method with 2 argument to allow automatic value type deduction.

`opIndexAssign` or `opIndex` is used for deserialization to support required syntax:
-----
yourObject["key"] = value;
-----
Multiple value types is supported for deserialization.

See_also: $(MREF serdeIgnoreOut), $(MREF serdeIgnoreIn)
+/
enum serdeLikeStruct;

/++
Ignore keys for object and enum members.
Should be applied to members or enum type itself.
+/
enum serdeIgnoreCase;

///
bool hasSerdeIgnoreCase(T)(T value)
    if (is(T == enum))
{
    static if (hasUDA!(T, serdeIgnoreCase))
    {
        return true;
    }
    else
    {
        import std.traits: EnumMembers;
        foreach (i, member; EnumMembers!T)
        {
            alias all = __traits(getAttributes, EnumMembers!T[i]);
            if (value == member)
                return hasUDA!(EnumMembers!T[i], serdeIgnoreCase);
        }
        assert(0);
    }
}

///
unittest
{
    enum E
    {
        @serdeIgnoreCase
        a,
        b,
        @serdeIgnoreCase
        c,
        d,
    }

    static assert(hasSerdeIgnoreCase(E.a));
    static assert(!hasSerdeIgnoreCase(E.b));
    static assert(hasSerdeIgnoreCase(E.c));
    static assert(!hasSerdeIgnoreCase(E.d));
}

///
unittest
{
    @serdeIgnoreCase
    enum E
    {
        a,
        b,
        c,
        d,
    }

    static assert(hasSerdeIgnoreCase(E.a));
    static assert(hasSerdeIgnoreCase(E.b));
    static assert(hasSerdeIgnoreCase(E.c));
    static assert(hasSerdeIgnoreCase(E.d));
}

/++
Can be applied only to strings fields.
Does not allocate new data when deserializeing. Raw ASDF data is used for strings instead of new memory allocation.
Use this attributes only for strings that would not be used after ASDF deallocation.
+/
enum serdeScoped;

/++
Attribute that force deserializer to throw an exception that the field was not found in the input.
+/
enum serdeRequired;


/++
Attributes for in transformation.
Return type of in transformation must be implicitly convertable to the type of the field.
In transformation would be applied after serialization proxy if any.

+/
struct serdeTransformIn(alias fun) {}

/++
Returns: unary function of underlaying alias of $(LREF serdeTransformIn)
+/
alias serdeGetTransformIn(alias value) = naryFun!(TemplateArgsOf!(getUDA!(value, serdeTransformIn))[0]);

/++
Attributes for out transformation.
Return type of out transformation may be differ from the type of the field.
Out transformation would be applied before serialization proxy if any.
+/
struct serdeTransformOut(alias fun) {}

/++
Returns: unary function of underlaying alias of $(LREF serdeTransformOut)
+/
alias serdeGetTransformOut(alias value) = naryFun!(TemplateArgsOf!(getUDA!(value, serdeTransformOut))[0]);
