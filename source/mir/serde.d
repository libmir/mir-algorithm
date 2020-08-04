module mir.serde;

import std.traits: getUDAs, hasUDA;

private template getUDA(alias symbol, alias attribute)
{
    private alias all = getUDAs!(symbol, attribute);
    static assert(all.length == 1, "Exactly one " ~ attribute.stringof ~ " attribute is allowed");
    enum getUDA = all[0];
}

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
template getSerdeKeysIn(alias symbol)
{
    static if (hasUDA!(symbol, serdeIgnore) || hasUDA!(symbol, serdeIgnoreIn))
        enum immutable(char[])[] getSerdeKeysIn = null;
    else
    static if (hasUDA!(symbol, serdeKeys))
        enum immutable(char[])[] getSerdeKeysIn = getUDA!(symbol, serdeKeys).keys;
    else
        enum immutable(char[])[] getSerdeKeysIn = [__traits(identifier, symbol)];
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

    static assert(getSerdeKeysIn!(S.f) == ["f"]);
    static assert(getSerdeKeysIn!(S.d) == ["D", "t"]);
    static assert(getSerdeKeysIn!(S.i) == null);
    static assert(getSerdeKeysIn!(S.ii) == null);
    static assert(getSerdeKeysIn!(S.io) == ["io"]);
    static assert(getSerdeKeysIn!(S.p) == ["p"]);
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

    import std.traits: hasUDA, getUDAs;

    static assert(hasUDA!(S.d, serdeProxy));
    static assert(hasUDA!(S.d, serdeProxy!(SmallString!32)));
    static assert(getUDAs!(S.d, serdeProxy).length == 1);
}

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
