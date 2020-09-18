module mir.serde;

import mir.functional: naryFun;
import mir.reflection;
import std.traits: TemplateArgsOf, EnumMembers, hasUDA;

version (D_Exceptions)
{
    /++
    Serde Exception
    +/
    class SerdeException : Exception
    {
        ///
        this(
            string msg,
            string file = __FILE__,
            size_t line = __LINE__,
            Throwable next = null) pure nothrow @nogc @safe 
        {
            super(msg, file, line, next);
        }

        ///
        this(
            string msg,
            Throwable next,
            string file = __FILE__,
            size_t line = __LINE__,
            ) pure nothrow @nogc @safe 
        {
            this(msg, file, line, next);
        }

        SerdeException toMutable() @trusted pure nothrow @nogc const
        {
            return cast() this;
        }

        alias toMutable this;
    }
}

/++
Attribute for key overloading during Serialization and Deserialization.
The first argument overloads the key value during serialization unless `serdeKeyOut` is given.
+/
struct serdeKeys
{
    ///
    immutable(string)[] keys;

@system pure nothrow @nogc:
    ///
    this(immutable(string)[] keys...) { this.keys = keys; }
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
        enum immutable(string)[] serdeGetKeysIn = null;
    else
    static if (hasUDA!(symbol, serdeKeys))
        enum immutable(string)[] serdeGetKeysIn = getUDA!(symbol, serdeKeys).keys;
    else
        enum immutable(string)[] serdeGetKeysIn = [__traits(identifier, symbol)];
}

/// ditto
immutable(string)[] serdeGetKeysIn(T)(const T value) @trusted pure nothrow @nogc
    if (is(T == enum))
{
    foreach (i, member; EnumMembers!T)
    {{
        alias all = __traits(getAttributes, EnumMembers!T[i]);
    }}

    import std.meta: staticMap;
    static immutable ret = [staticMap!(.serdeGetKeysIn, EnumMembers!T)];
    final switch (value)
    {
        foreach (i, member; EnumMembers!T)
        {
            case member:
                return ret[i];
        }
    }
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
version(mir_test)
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

///ditto
@trusted pure nothrow @nogc
string serdeGetKeyOut(T)(const T value)
    if (is(T == enum))
{
    foreach (i, member; EnumMembers!T)
    {{
        alias all = __traits(getAttributes, EnumMembers!T[i]);
    }}

    import std.meta: staticMap;
    static immutable ret = [staticMap!(.serdeGetKeyOut, EnumMembers!T)];
    final switch (value)
    {
        foreach (i, member; EnumMembers!T)
        {
            case member:
                return ret[i];
        }
    }
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

///
version(mir_test)
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
deprecated("use @serdeScoped @serdeProxy!(const(char)[]) instead") enum serdeScopeStringProxy;

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
version(mir_test)
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
version(mir_test)
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
Attribute that force deserializer to throw an exception that the field hasn't been not found in the input.
+/
enum serdeRequired;

/++
Attribute that allow deserializer to do not throw an exception if the field hasn't been not found in the input.
+/
enum serdeOptional;

/++
Attribute that allow deserializer to don't throw an exception that the field matches multiple keys in the object.
+/
enum serdeAllowMultiple;

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

/++
+/
bool serdeParseEnum(E)(const char[] str, out E res)
{
    static if (hasUDA!(E, serdeIgnoreCase))
    {
        import mir.format: stringBuf;
        stringBuf buf;
        buf << str;
        auto ustr = buf.data.fastToUpperInPlace;
    }
    else
    {
        alias ustr = str;
    }
    switch(ustr)
    {
        foreach(i, member; EnumMembers!E)
        {{
            enum initKeys = serdeGetKeysIn(EnumMembers!E[i]);
            static if (hasUDA!(E, serdeIgnoreCase))
            {
                import mir.ndslice.topology: map;
                import mir.array.allocation: array;
                enum keys = initKeys.map!fastLazyToUpper.map!array.array;
            }
            else
            {
                enum keys = initKeys;
            }
            static assert (keys.length, "At least one input enum key is required");
            static foreach (key; keys)
            {
                case key:
            }
            res = member;
            return true;
        }}
        default:
            return false;
    }
}

///
version(mir_test)
unittest
{
    @serdeIgnoreCase // supported for the whole type
    enum E
    {
        @serdeKeys("A", "alpha")
        a,
        @serdeKeys("B", "beta")
        b,
        c,
    }

    auto e = E.c;
    assert(serdeParseEnum("a", e));
    assert(e == E.a);
    assert(serdeParseEnum("alpha", e));
    assert(e == E.a);
    assert(serdeParseEnum("BETA", e));
    assert(e == E.b);
    assert(serdeParseEnum("b", e));
    assert(e == E.b);
    assert(serdeParseEnum("C", e));
    assert(e == E.c);
}

/++
Deserialization member type
+/
template serdeDeserializationMemberType(T, string member)
{
    import std.traits: Unqual, Parameters;
    T* aggregate;
    static if (isField!(T, member))
    {
        alias serdeDeserializationMemberType = typeof(__traits(getMember, *aggregate, member));
    }
    else
    static if (__traits(compiles, &__traits(getMember, *aggregate, member)()))
    {
        alias serdeDeserializationMemberType = typeof(__traits(getMember, *aggregate, member)());
    }
    else
    {
        alias serdeDeserializationMemberType = Unqual!(Parameters!(__traits(getMember, *aggregate, member))[0]);
    }
}

/// ditto
template serdeDeserializationMemberType(T)
{
    ///
    alias serdeDeserializationMemberType(string member) = .serdeDeserializationMemberType!(T, member);
}


/++
Is deserializable member
+/
template serdeIsDeserializable(T)
{
    ///
    enum bool serdeIsDeserializable(string member) = serdeGetKeysIn!(__traits(getMember, T, member)).length > 0;
}

///
unittest
{

    static struct S
    {
        @serdeIgnore
        int i;

        @serdeKeys("a", "b")
        int a;
    }

    alias serdeIsDeserializableInS = serdeIsDeserializable!S;
    static assert (!serdeIsDeserializableInS!"i");
    static assert (serdeIsDeserializableInS!"a");
}

/++
Final proxy type
+/
template serdeGetFinalProxy(T)
{
    import std.traits: hasUDA;
    static if (is(T == class) || is(T == struct) || is(T == union) || is(T == interface))
    {
        static if (hasUDA!(T, serdeProxy))
        {
            alias serdeGetFinalProxy = .serdeGetFinalProxy!(serdeGetProxy!T);
        }
        else
        {
            alias serdeGetFinalProxy = T;
        }
    }
    else
    {
        alias serdeGetFinalProxy = T;
    }
}

///
unittest
{

    @serdeProxy!string
    static struct A {}

    @serdeProxy!A
    static struct B {}

    @serdeProxy!B
    static struct C {}

    static assert (is(serdeGetFinalProxy!C == string), serdeGetFinalProxy!C.stringof);
    static assert (is(serdeGetFinalProxy!string == string));
}

/++
Final proxy type deserializable members
+/
template serdeFinalProxyDeserializableMembers(T)
{
    import std.meta: Filter, aliasSeqOf;
    alias P = serdeGetFinalProxy!T;
    static if (is(P == struct) || is(P == class) || is(P == interface) || is(P == union))
        enum string[] serdeFinalProxyDeserializableMembers = [Filter!(serdeIsDeserializable!P, aliasSeqOf!(DeserializableMembers!P))];
    else
        enum string[] serdeFinalProxyDeserializableMembers = null;
}

///
unittest
{

    static struct A
    {
        @serdeIgnore
        int i;

        @serdeKeys("a", "b")
        int m;
    }

    @serdeProxy!A
    static struct B {}

    @serdeProxy!B
    static struct C {}

    static assert (serdeFinalProxyDeserializableMembers!C == ["m"]);
}

/++
Deserialization member final proxy type
+/
template serdeFinalDeserializationMemberType(T, string member)
{
    import std.traits: hasUDA;
    static if (hasUDA!(__traits(getMember, T, member), serdeProxy))
    {
        alias serdeFinalDeserializationMemberType = serdeGetFinalProxy!(serdeGetProxy!(__traits(getMember, T, member)));
    }
    else
    {
        alias serdeFinalDeserializationMemberType = serdeGetFinalProxy!(serdeDeserializationMemberType!(T, member));
    }
}

/// ditto
template serdeFinalDeserializationMemberType(T)
{
    ///
    alias serdeFinalDeserializationMemberType(string member) = .serdeFinalDeserializationMemberType!(T, member);
}

///
unittest
{

    static struct A
    {
        
    }

    @serdeProxy!A
    static struct B {}

    @serdeProxy!B
    static struct C {}


    @serdeProxy!double
    struct E {}

    struct D
    {
        C c;

        @serdeProxy!E
        int d;
    }

    static assert (is(serdeFinalDeserializationMemberType!(D, "c") == A));
    static assert (is(serdeFinalDeserializationMemberType!(D, "d") == double));
}

/++
Deserialization members final proxy types
+/
template serdeDeserializationFinalProxyMemberTypes(T)
{
    import std.meta: NoDuplicates, staticMap, aliasSeqOf;
    alias serdeDeserializationFinalProxyMemberTypes = NoDuplicates!(staticMap!(serdeGetFinalProxy, staticMap!(serdeFinalDeserializationMemberType!T, aliasSeqOf!(serdeFinalProxyDeserializableMembers!T))));
}

///
unittest
{

    static struct A {}

    @serdeProxy!A
    static struct B {}

    @serdeProxy!B
    static struct C {}

    @serdeProxy!B
    static struct E {}

    static struct D
    {
        C c;

        @serdeProxy!E
        int d;
    }

    import std.meta: AliasSeq;
    static assert (is(serdeDeserializationFinalProxyMemberTypes!D == AliasSeq!A));
}

private template serdeDeserializationFinalProxyMemberTypesRecurseImpl(T...)
{
    import std.meta: NoDuplicates, staticMap;
    alias F = NoDuplicates!(T, staticMap!(serdeDeserializationFinalProxyMemberTypes, T));
    static if (F.length == T.length)
        alias serdeDeserializationFinalProxyMemberTypesRecurseImpl = T;
    else
        alias serdeDeserializationFinalProxyMemberTypesRecurseImpl  = .serdeDeserializationFinalProxyMemberTypesRecurseImpl!F;
}

/++
Deserialization members final proxy types (recursive)
+/
alias serdeDeserializationFinalProxyMemberTypesRecurse(T) = serdeDeserializationFinalProxyMemberTypesRecurseImpl!(serdeGetFinalProxy!T);

///
unittest
{

    static struct A { double g; }

    @serdeProxy!A
    static struct B {}

    @serdeProxy!B
    static struct C {}

    @serdeProxy!B
    static struct E {}

    static struct D
    {
        C c;

        @serdeProxy!E
        int d;
    }

    @serdeProxy!D
    static struct F {}

    import std.meta: AliasSeq;
    static assert (is(serdeDeserializationFinalProxyMemberTypesRecurse!F == AliasSeq!(D, A, double)));
}

/++
Deserialization members final proxy keys (recursive)
+/
template serdeGetDeserializatinKeysRecurse(T)
{
    import mir.algorithm.iteration: uniq, equal;
    import mir.array.allocation: array;
    import mir.ndslice.sorting: sort;
    import std.meta: staticMap, aliasSeqOf;
    enum string[] serdeGetDeserializatinKeysRecurse = [staticMap!(aliasSeqOf, staticMap!(serdeFinalProxyDeserializableMembers, serdeDeserializationFinalProxyMemberTypesRecurse!T))].sort.uniq!equal.array;
}

///
unittest
{

    static struct A { double g; float d; }

    @serdeProxy!A
    static struct B {  int f; }

    @serdeProxy!B
    static struct C {  int f; }

    @serdeProxy!B
    static struct E {  int f; }

    static struct D
    {
        C c;

        @serdeProxy!E
        int d;
    }

    @serdeProxy!D
    static struct F { int f; }

    static assert (serdeGetDeserializatinKeysRecurse!F == ["c", "d", "g"]);
}

/++
UDA used to force deserializer to initilize members in the order of their definition in the target object/structure.

The attribute force deserializer to create a dummy type (recursively), initializer its fields and then assign them to
to the object members (fields and setters) in the order of their definition.

See_also: $(LREF SerdeOrderedDummy), $(LREF serdeRealOrderedIn).
+/
enum serdeOrderedIn;

/++
UDA used to force deserializer to initilize members in the order of their definition in the target object/structure.

Unlike $(LREF serdeOrderedIn) `serdeRealOrderedDummy` force deserialzier to iterate all DOM keys for each object deserialization member.
It is slower but more universal approach.

See_also: $(LREF serdeOrderedIn).
+/
enum serdeRealOrderedIn;

/++
UDA used to force deserializer to skip the member final deserialization.
A user should finalize the member deserialize using the dummy object provided in `serdeFinalizeWithDummy(ref SerdeOrderedDummy!(typeof(this)) dummy)` struct method
and dummy method `serdeFinalizeTargetMember`.
+/
enum serdeFromDummyByUser;

/++
UDA used to force serializer to output members in the alphabetical order of their output keys.
+/
enum serdeAlphabetOut;

private enum isCompositeType(T) = is(T == class) || is(T == struct) || is(T == union) || is(T == interface);

/++
A dummy structure usefull $(LREF serdeOrderedIn) support.
+/
struct SerdeOrderedDummy(T, bool __optionalByDefault = false)
    if (is(serdeGetFinalProxy!T == T) && (is(T == class) || is(T == struct) || is(T == union) || is(T == interface)))
{
    import std.traits: hasUDA;

    @serdeIgnore
    SerdeFlags!(typeof(this)) __serdeFlags;

    static if (__optionalByDefault)
        alias __serdeOptionalRequired = serdeRequired;
    else
        alias __serdeOptionalRequired = serdeOptional;

    this()(T value)
    {
        static foreach (member; serdeFinalProxyDeserializableMembers!T)
        {
            static if (isField!(T, member))
            {
                static if (__traits(compiles, {__traits(getMember, this, member) = __traits(getMember, value, member);}))
                    __traits(getMember, this, member) = __traits(getMember, value, member);
            }
        }
    }

public:

    static foreach (i, member; serdeFinalProxyDeserializableMembers!T)
    {
        static if (isField!(T, member))
        {
            static if (hasUDA!(__traits(getMember, T, member), serdeProxy))
            {
                mixin("@(__traits(getAttributes, T." ~ member ~ ")) serdeDeserializationMemberType!(T, `" ~ member ~ "`) " ~ member ~ ";");
            }
            else
            static if (isCompositeType!(typeof(__traits(getMember, T, member))))
            {
                static if (hasUDA!(typeof(__traits(getMember, T, member)), serdeProxy))
                {
                    mixin("@(__traits(getAttributes, T." ~ member ~ ")) serdeDeserializationMemberType!(T, `" ~ member ~ "`) " ~ member ~ " = T.init." ~ member ~ ";");
                }
                else
                static if (__traits(compiles, {
                    mixin("enum SerdeOrderedDummy!(serdeDeserializationMemberType!(T, `" ~ member ~ "`)) " ~ member ~ " = SerdeOrderedDummy!(serdeDeserializationMemberType!(T, `" ~ member ~ "`))(T.init." ~ member ~ ");");
                }))
                {
                    mixin("@(__traits(getAttributes, T." ~ member ~ ")) SerdeOrderedDummy!(serdeDeserializationMemberType!(T, `" ~ member ~ "`)) " ~ member ~ " = SerdeOrderedDummy!(serdeDeserializationMemberType!(T, `" ~ member ~ "`))(T.init." ~ member ~ ");");
                }
                else
                {
                    mixin("@(__traits(getAttributes, T." ~ member ~ ")) SerdeOrderedDummy!(serdeDeserializationMemberType!(T, `" ~ member ~ "`)) " ~ member ~ ";");
                }
            }
            else
            {
                mixin("@(__traits(getAttributes, T." ~ member ~ ")) serdeDeserializationMemberType!(T, `" ~ member ~ "`) " ~ member ~ " = T.init." ~ member ~ ";");
            }
        }
        else
        {
            mixin("@(__traits(getAttributes, T." ~ member ~ ")) serdeDeserializationMemberType!(T, `" ~ member ~ "`) " ~ member ~ ";");
        }
    }

    /// Initialize target members
    void serdeFinalizeWithFlags(ref scope const SerdeFlags!(typeof(this)) flags)
    {
        __serdeFlags = flags;
    }

    /// Initialize target members
    void serdeFinalizeTarget(ref T value, ref scope SerdeFlags!T flags)
    {
        import std.traits: hasElaborateAssign;
        static foreach (member; serdeFinalProxyDeserializableMembers!T)
            __traits(getMember, flags, member) = __traits(getMember, __serdeFlags, member);
        static foreach (member; serdeFinalProxyDeserializableMembers!T)
            static if (!hasUDA!(__traits(getMember, T, member), serdeFromDummyByUser))
        {{
            if (hasUDA!(__traits(getMember, T, member), __serdeOptionalRequired) == __optionalByDefault || __traits(getMember, __serdeFlags, member))
            {
                static if (is(typeof(__traits(getMember, this, member)) : SerdeOrderedDummy!I, I))
                {
                    alias M = typeof(__traits(getMember, value, member));
                    SerdeFlags!M memberFlags;
                    __traits(getMember, this, member).serdeFinalizeTarget(__traits(getMember, value, member), memberFlags);
                    static if(__traits(hasMember, M, "serdeFinalizeWithFlags"))
                    {
                        __traits(getMember, value, member).serdeFinalizeWithFlags(memberFlags);
                    }
                    static if(__traits(hasMember, M, "serdeFinalize"))
                    {
                        __traits(getMember, value, member).serdeFinalize();
                    }
                }
                else
                {
                    static if (hasElaborateAssign!(typeof(__traits(getMember, this, member))))
                    {
                        import core.lifetime: move;
                        __traits(getMember, value, member) = move(__traits(getMember, this, member));
                    }
                    else
                        __traits(getMember, value, member) = __traits(getMember, this, member);
                }
            }
        }}
        static if(__traits(hasMember, T, "serdeFinalizeWithDummy"))
        {
            value.serdeFinalizeWithDummy(this);
        }
    }

    /// Initialize target member
    void serdeFinalizeTargetMember(string member)(ref T value)
    {
            if (hasUDA!(__traits(getMember, T, member), __serdeOptionalRequired) == __optionalByDefault || __traits(getMember, __serdeFlags, member))
            {
                static if (is(typeof(__traits(getMember, this, member)) : SerdeOrderedDummy!I, I))
                {
                    alias M = typeof(__traits(getMember, value, member));
                    SerdeFlags!M memberFlags;
                    __traits(getMember, this, member).serdeFinalizeTarget(__traits(getMember, value, member), memberFlags);
                    static if(__traits(hasMember, M, "serdeFinalizeWithFlags"))
                    {
                        __traits(getMember, value, member).serdeFinalizeWithFlags(memberFlags);
                    }
                    static if(__traits(hasMember, M, "serdeFinalize"))
                    {
                        __traits(getMember, value, member).serdeFinalize();
                    }
                }
                else
                {
                    static if (hasElaborateAssign!(typeof(__traits(getMember, this, member))))
                    {
                        import core.lifetime: move;
                        __traits(getMember, value, member) = move(__traits(getMember, this, member));
                    }
                    else
                        __traits(getMember, value, member) = __traits(getMember, this, member);
                }
            }
    }
}

///
unittest
{
    import std.traits;

    static struct S
    {
        private double _d;

        @serdeProxy!int
        void d(double v) @property { _d = v; }

        string s;
    }

    static assert(is(typeof(SerdeOrderedDummy!S.init.d) == double), SerdeOrderedDummy!S.init.d);
    static assert(is(typeof(SerdeOrderedDummy!S.init.s) == string));
    static assert(hasUDA!(S.d, serdeProxy));
    static assert(hasUDA!(SerdeOrderedDummy!S.d, serdeProxy));
}

/++
A dummy structure passed to `.serdeFinalizeWithFlags` finalizer method.
+/
struct SerdeFlags(T)
{
    static if (is(T : SerdeOrderedDummy!I, I))
        static foreach(member; serdeFinalProxyDeserializableMembers!I)
            mixin("bool " ~ member ~ ";");
    else
        static foreach(member; serdeFinalProxyDeserializableMembers!T)
            mixin("bool " ~ member ~ ";");
}

/++
+/
template deserializeValueMemberImpl(alias deserializeValue, alias deserializeScoped)
{
    ///
    SerdeException deserializeValueMemberImpl(string member, Data, T, Context...)(Data data, ref T value, ref SerdeFlags!T requiredFlags, ref Context args)
    {
        import mir.conv: to;
        import std.traits: Select, Unqual, Parameters;

        static immutable excm(string member) = new SerdeException("ASDF deserialisation: multiple keys for member '" ~ member ~ "' in " ~ T.stringof ~ " are not allowed.");

        static if (!hasUDA!(__traits(getMember, value, member), serdeAllowMultiple))
            if (__traits(getMember, requiredFlags, member))
                return excm!member;

        __traits(getMember, requiredFlags, member) = true;

        static if(!__traits(compiles, {__traits(getMember, value, member) = __traits(getMember, value, member);}))
        {
            alias Type = Unqual!(Parameters!(__traits(getMember, value, member)));
        }
        else
        {
            alias Type = typeof(__traits(getMember, value, member));
        }

        static if(hasUDA!(__traits(getMember, value, member), serdeLikeList))
        {
            static assert(hasUDA!(__traits(getMember, value, member), serdeProxy), V.stringof ~ "." ~ member ~ " should have a Proxy type for deserialization");
            serdeGetProxy!(__traits(getMember, value, member)) proxy;
            enum S = hasUDA!(__traits(getMember, value, member), serdeScoped) && __traits(compiles, deserializeScoped(data, proxy));
            alias Fun = Select!(S, deserializeScoped, deserializeValue);
            foreach(v; data.byElement)
            {
                proxy = proxy.init;
                if (auto exc = Fun(v, proxy, args))
                    return exc;
                __traits(getMember, value, member).put(proxy);
            }
        }
        else
        static if(hasUDA!(__traits(getMember, value, member), serdeLikeStruct))
        {
            static assert(hasUDA!(__traits(getMember, value, member), serdeProxy), V.stringof ~ "." ~ member ~ " should have a Proxy type for deserialization");
            serdeGetProxy!(__traits(getMember, value, member)) proxy;
            enum S = hasUDA!(__traits(getMember, value, member), serdeScoped) && __traits(compiles, deserializeScoped(data, proxy));
            alias Fun = Select!(S, deserializeScoped, deserializeValue);
            foreach(v; data.byKeyValue)
            {
                proxy = proxy.init;
                if (auto exc = Fun(v.value, proxy, args))
                    return exc;
                __traits(getMember, value, member)[v.key.idup] = proxy;
            }
        }
        else
        static if(hasUDA!(__traits(getMember, value, member), serdeProxy))
        {
            serdeGetProxy!(__traits(getMember, value, member)) proxy;
            enum S = hasUDA!(__traits(getMember, value, member), serdeScoped) && __traits(compiles, deserializeScoped(data, proxy));
            alias Fun = Select!(S, deserializeScoped, deserializeValue);

            if (auto exc = Fun(data, proxy))
                return exc;
            __traits(getMember, value, member) = proxy.to!Type;
        }
        else
        static if(__traits(compiles, {__traits(getMember, value, member) = __traits(getMember, value, member);}) && __traits(compiles, {auto ptr = &__traits(getMember, value, member); }))
        {
            enum S = hasUDA!(__traits(getMember, value, member), serdeLikeStruct) && __traits(compiles, deserializeScoped(data, __traits(getMember, value, member)));
            alias Fun = Select!(S, deserializeScoped, deserializeValue);

            if (auto exc = Fun(data, __traits(getMember, value, member)))
                return exc;
        }
        else
        {
            Type val;

            enum S = hasUDA!(__traits(getMember, value, member), serdeScoped) && __traits(compiles, deserializeScoped(data, val));
            alias Fun = Select!(S, deserializeScoped, deserializeValue);

            if (auto exc = Fun(data, val))
                return exc;
            __traits(getMember, value, member) = val;
        }

        static if(hasUDA!(__traits(getMember, value, member), serdeTransformIn))
        {
            alias f = serdeGetTransformIn!(__traits(getMember, value, member));
            f(__traits(getMember, value, member));
        }

        return null;
    }
}

private:

auto fastLazyToUpper()(const(char)[] name)
{
    import mir.ndslice.topology: map;
    return name.map!fastToUpper;
}

auto fastToUpper()(char a)
{   // std.ascii may not be inlined
    return 'a' <= a && a <= 'z' ? cast(char)(a ^ 0x20) : a;
}

@safe pure nothrow @nogc
char[] fastToUpperInPlace()(scope return char[] a)
{
    foreach(ref char e; a)
        e = e.fastToUpper;
    return a;
}
