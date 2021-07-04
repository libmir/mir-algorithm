/++
This implements common de/serialization routines.

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilya Yaroshenko

Macros:
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
+/
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

    /++
    Serde Exception with formatting support
    +/
    class SerdeMirException : SerdeException
    {
        import mir.exception: MirThrowableImpl, mirExceptionInitilizePayloadImpl;

        enum maxMsgLen = 447;

        ///
        mixin MirThrowableImpl;
    }
}

/++
Helper enumeration for for serializer .
Use negative `int` values for user defined targets.
+/
enum SerdeTarget : int
{
    ///
    ion,
    ///
    json,
    ///
    cbor,
    ///
    msgpack,
    ///
    yaml,
    ///
    csv,
    ///
    excel,
}

/++
Attribute for key overloading during Serialization and Deserialization.
The first argument overloads the key value during serialization unless `serdeKeyOut` is given.
+/
struct serdeKeys
{
    ///
    immutable(string)[] keys;

@trusted pure nothrow @nogc:
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
The attribute should be applied to a string-like member that should be de/serialized as an annotation / attribute.

This feature is used in $(MIR_PACKAGE mir-ion).
+/
enum serdeAnnotation;


private template serdeIsAnnotationMemberIn(T)
{
    enum bool serdeIsAnnotationMemberIn(string member)
          = hasUDA!(__traits(getMember, T, member), serdeAnnotation) 
        && !hasUDA!(__traits(getMember, T, member), serdeIgnore) 
        && !hasUDA!(__traits(getMember, T, member), serdeIgnoreIn);
}

/++
+/
template serdeGetAnnotationMembersIn(T)
{
    import std.meta: aliasSeqOf, Filter;
    static if (isSomeStruct!T)
        enum string[] serdeGetAnnotationMembersIn = [Filter!(serdeIsAnnotationMemberIn!T, aliasSeqOf!(DeserializableMembers!T))];
    else
        enum string[] serdeGetAnnotationMembersIn = null;
}


///
version(mir_test) unittest
{
    struct S
    {
        double data;

        @serdeAnnotation
        string a;
        @serdeAnnotation @serdeIgnoreIn
        string b;
        @serdeAnnotation @serdeIgnoreOut
        string c;
        @serdeAnnotation @serdeIgnore
        string d;
    }

    static assert(serdeGetAnnotationMembersIn!int == []);
    static assert(serdeGetAnnotationMembersIn!S == ["a", "c"]);
}

private template serdeIsAnnotationMemberOut(T)
{
    enum bool serdeIsAnnotationMemberOut(string member)
          = hasUDA!(__traits(getMember, T, member), serdeAnnotation) 
        && !hasUDA!(__traits(getMember, T, member), serdeIgnore) 
        && !hasUDA!(__traits(getMember, T, member), serdeIgnoreOut);
}

/++
+/
template serdeGetAnnotationMembersOut(T)
{
    import std.meta: aliasSeqOf, Filter;
    static if (isSomeStruct!T)
        enum string[] serdeGetAnnotationMembersOut = [Filter!(serdeIsAnnotationMemberOut!T, aliasSeqOf!(DeserializableMembers!T))];
    else
        enum string[] serdeGetAnnotationMembersOut = null;
}

///
version(mir_test) unittest
{
    struct S
    {
        double data;

        @serdeAnnotation
        string a;
        @serdeAnnotation @serdeIgnoreIn
        string b;
        @serdeAnnotation @serdeIgnoreOut
        string c;
        @serdeAnnotation @serdeIgnore
        string d;
    }

    static assert(serdeGetAnnotationMembersOut!int == []);
    static assert(serdeGetAnnotationMembersOut!S == ["a", "b"]);
}

/++
An annotation / attribute for algebraic types deserialization.

This feature is used in $(MIR_PACKAGE mir-ion) for $(GMREF mir-core, mir,algebraic).
+/
struct serdeAlgebraicAnnotation
{
    ///
    string annotation;

@safe pure nothrow @nogc:
    ///
    this(string annotation) { this.annotation = annotation; }
}

/++
+/
template serdeHasAlgebraicAnnotation(T)
{
    static if (isSomeStruct!T || is(T == enum))
    {
        static if (hasUDA!(T, serdeAlgebraicAnnotation))
        {
            enum serdeHasAlgebraicAnnotation = true;
        }
        else
        static if (__traits(getAliasThis, T).length)
        {
            T* aggregate;
            alias A = typeof(__traits(getMember, aggregate, __traits(getAliasThis, T)));
            enum serdeHasAlgebraicAnnotation = .serdeHasAlgebraicAnnotation!A;
        }
        else
        {
            enum serdeHasAlgebraicAnnotation = false;
        }
    }
    else
    {
        enum serdeHasAlgebraicAnnotation = false;
    }
}

/++
+/
template serdeGetAlgebraicAnnotation(T)
{
    static if (hasUDA!(T, serdeAlgebraicAnnotation))
    {
        enum string serdeGetAlgebraicAnnotation = getUDA!(T, serdeAlgebraicAnnotation).annotation;
    }
    else
    {
        T* aggregate;
        alias A = typeof(__traits(getMember, aggregate, __traits(getAliasThis, T)));
        enum serdeGetAlgebraicAnnotation = .serdeGetAlgebraicAnnotation!A;
    }
}

/++
Returns:
    immutable array of the input keys for the symbol or enum value
+/
template serdeGetKeysIn(alias symbol)
{
    static if (hasUDA!(symbol, serdeAnnotation) || hasUDA!(symbol, serdeIgnore) || hasUDA!(symbol, serdeIgnoreIn))
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
    static if (__VERSION__ < 2093)
    {
        final switch (value)
        {
            foreach (i, member; EnumMembers!T)
            {
                case member:
                    return ret[i];
            }
        }
    }
    else
    {
    import mir.enums: getEnumIndex;
    uint index = void;
    if (getEnumIndex(value, index))
        return ret[index];
    assert(0);
    }
}

///
version(mir_test) unittest
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
version(mir_test) unittest
{
    enum E
    {
        @serdeKeys("A", "alpha")
        a,
        @serdeKeys("B", "beta")
        b,
        c,
    }

    static assert (serdeGetKeysIn(E.a) == ["A", "alpha"], serdeGetKeysIn(E.a));
    static assert (serdeGetKeysIn(E.c) == ["c"]);
}

/++
Returns:
    output key for the symbol or enum value
+/
template serdeGetKeyOut(alias symbol)
{
    static if (hasUDA!(symbol, serdeAnnotation) || hasUDA!(symbol, serdeIgnore) || hasUDA!(symbol, serdeIgnoreOut))
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
@safe pure nothrow @nogc
string serdeGetKeyOut(T)(const T value)
    if (is(T == enum))
{
    foreach (i, member; EnumMembers!T)
    {{
        alias all = __traits(getAttributes, EnumMembers!T[i]);
    }}

    static if (__VERSION__ < 2093)
    {
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
    else
    {
    import std.meta: staticMap;
    import mir.enums: getEnumIndex;
    static immutable ret = [staticMap!(.serdeGetKeyOut, EnumMembers!T)];
    uint index = void;
    if (getEnumIndex(value, index))
        return ret[index];
    assert(0);
    }
}

///
version(mir_test) unittest
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
version(mir_test) unittest
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

See_also: $(LREF serdeIgnoreIn) $(LREF serdeIgnoreOut)
+/
enum serdeIgnore;

/++
Attribute to ignore field during deserialization.

See_also: $(LREF serdeIgnoreInIfAggregate)
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
version(mir_test) unittest
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
version(mir_test) unittest
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
Attributes to conditional ignore field during serialization.

The predicate should be aplied to the member, to the aggregate type.

See_also: $(LREF serdeIgnoreOutIfAggregate)
+/
struct serdeIgnoreOutIf(alias pred);

/++
+/
alias serdeGetIgnoreOutIf(alias symbol) = naryFun!(TemplateArgsOf!(getUDA!(symbol, serdeIgnoreOutIf))[0]);

/++
Attributes to conditional ignore field during serialization.

The predicate should be aplied to the aggregate value, not to the member.

See_also: $(LREF serdeIgnoreIfAggregate) $(LREF serdeIgnoreOutIf), $(LREF serdeIgnoreInIfAggregate)
+/
struct serdeIgnoreOutIfAggregate(alias pred);

/++
+/
alias serdeGetIgnoreOutIfAggregate(alias symbol) = naryFun!(TemplateArgsOf!(getUDA!(symbol, serdeIgnoreOutIfAggregate))[0]);

/++
Attributes to conditional ignore field during deserialization.

The attribute should be combined with $(LREF serdeRealOrderedIn) applied on the aggregate.

See_also: $(LREF serdeIgnoreIfAggregate) $(LREF serdeIgnoreOutIfAggregate) $(LREF serdeIgnoreIn)
+/
struct serdeIgnoreInIfAggregate(alias pred);

/++
+/
alias serdeGetIgnoreInIfAggregate(alias symbol) = naryFun!(TemplateArgsOf!(getUDA!(symbol, serdeIgnoreInIfAggregate))[0]);

/++
Attributes to conditional ignore field during serialization and deserialization.

The attribute should be combined with $(LREF serdeRealOrderedIn) applied on the aggregate.

The predicate should be aplied to the aggregate value, not to the member.

See_also: $(LREF serdeIgnoreOutIfAggregate) $(LREF serdeIgnoreInIfAggregate) $ $(LREF serdeIgnore)
+/
struct serdeIgnoreIfAggregate(alias pred);

/++
+/
alias serdeGetIgnoreIfAggregate(alias symbol) = naryFun!(TemplateArgsOf!(getUDA!(symbol, serdeIgnoreIfAggregate))[0]);

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
version(mir_test) unittest
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
version(mir_test) unittest
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
Does not allocate new data when deserializeing. Raw data is used for strings instead of new memory allocation.
Use this attributes only for strings or arrays that would not be used after deallocation.
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
bool serdeParseEnum(E)(const char[] str, ref E res)
    @safe pure nothrow @nogc
{
    static if (__VERSION__ < 2093)
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
    else
    {
    import mir.enums: getEnumIndexFromKey, unsafeEnumFromIndex;
    import mir.utility: _expect;

    uint index = void;
    if (getEnumIndexFromKey!(E, hasUDA!(E, serdeIgnoreCase), serdeGetKeysIn)(str, index)._expect(true))
    {
        res = unsafeEnumFromIndex!E(index);
        return true;
    }
    return false;
    }
}

///
version(mir_test) unittest
{
    enum E
    {
        @serdeKeys("A", "alpha")
        a,
        @serdeKeys("B", "beta")
        b,
        c,
    }

    auto e = E.c;
    assert(serdeParseEnum("A", e));
    assert(e == E.a);
    assert(serdeParseEnum("alpha", e));
    assert(e == E.a);
    assert(serdeParseEnum("beta", e));
    assert(e == E.b);
    assert(serdeParseEnum("B", e));
    assert(e == E.b);
    assert(serdeParseEnum("c", e));
    assert(e == E.c);

    assert(!serdeParseEnum("C", e));
    assert(!serdeParseEnum("Alpha", e));
}

/// Case insensitive
version(mir_test) unittest
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
    static if (hasField!(T, member))
    {
        alias serdeDeserializationMemberType = typeof(__traits(getMember, *aggregate, member));
    }
    else
    static if (__traits(compiles, &__traits(getMember, *aggregate, member)()) || __traits(getOverloads, *aggregate, member).length > 1)
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
version(mir_test) unittest
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
Serialization member type
+/
template serdeSerializationMemberType(T, string member)
{
    import std.traits: Unqual, Parameters;
    T* aggregate;
    static if (hasField!(T, member))
    {
        alias serdeSerializationMemberType = typeof(__traits(getMember, *aggregate, member));
    }
    else
    {
        alias serdeSerializationMemberType = typeof(__traits(getMember, *aggregate, member)());
    }
}

/// ditto
template serdeSerializationMemberType(T)
{
    ///
    alias serdeSerializationMemberType(string member) = .serdeSerializationMemberType!(T, member);
}


/++
Is deserializable member
+/
template serdeIsSerializable(T)
{
    ///
    enum bool serdeIsSerializable(string member) = serdeGetKeyOut!(__traits(getMember, T, member)) !is null;
}

///
version(mir_test) unittest
{

    static struct S
    {
        @serdeIgnore
        int i;

        @serdeKeys("a", "b")
        int a;
    }

    alias serdeIsSerializableInS = serdeIsSerializable!S;
    static assert (!serdeIsSerializableInS!"i");
    static assert (serdeIsSerializableInS!"a");
}

/++
Final proxy type
+/
template serdeGetFinalProxy(T)
{
    import std.traits: hasUDA, isAggregateType;
    static if (isAggregateType!T || is(T == enum))
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
version(mir_test) unittest
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
Final deep proxy type
+/
template serdeGetFinalDeepProxy(T)
{
    import std.traits: Unqual, hasUDA, isAggregateType, isArray, ForeachType;
    static if (isAggregateType!T || is(T == enum))
    {
        static if (hasUDA!(T, serdeProxy))
        {
            alias serdeGetFinalDeepProxy = .serdeGetFinalDeepProxy!(serdeGetProxy!T);
        }
        else
        static if (__traits(hasMember, T, "serdeKeysProxy"))
        {
            alias serdeGetFinalDeepProxy = .serdeGetFinalDeepProxy!(T.serdeKeysProxy);
        }
        else
        static if (is(T == enum))
        {
            alias serdeGetFinalDeepProxy = typeof(null);
        }
        else
        {
            alias serdeGetFinalDeepProxy = T;
        }
    }
    else
    static if (isArray!T)
    {
        alias E = Unqual!(ForeachType!T);
        static if (isAggregateType!E || is(E == enum))
            alias serdeGetFinalDeepProxy = .serdeGetFinalDeepProxy!E;
        else
            alias serdeGetFinalDeepProxy = T;
    }
    else
    static if (is(T == V[K], K, V))
    {
        alias E = Unqual!V;
        static if (isAggregateType!E || is(E == enum))
            alias serdeGetFinalDeepProxy = .serdeGetFinalDeepProxy!E;
        else
            alias serdeGetFinalDeepProxy = T;
    }
    else
    {
        alias serdeGetFinalDeepProxy = T;
    }
}

///
version(mir_test) unittest
{

    @serdeProxy!string
    static struct A {}

    enum E {a,b,c}

    @serdeProxy!(A[E])
    static struct B {}

    @serdeProxy!(B[])
    static struct C {}

    static assert (is(serdeGetFinalDeepProxy!C == string), serdeGetFinalDeepProxy!C.stringof);
    static assert (is(serdeGetFinalDeepProxy!string == string));
}

/++
Final proxy type deserializable members
+/
template serdeFinalProxyDeserializableMembers(T)
{
    import std.meta: Filter, aliasSeqOf;
    alias P = serdeGetFinalProxy!T;
    static if (isSomeStruct!P)
        enum string[] serdeFinalProxyDeserializableMembers = [Filter!(serdeIsDeserializable!P, aliasSeqOf!(DeserializableMembers!P))];
    else
        enum string[] serdeFinalProxyDeserializableMembers = null;
}

///
version(mir_test) unittest
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
Final deep proxy type serializable members
+/
template serdeFinalDeepProxySerializableMembers(T)
{
    import std.traits: isAggregateType;
    import std.meta: Filter, aliasSeqOf;
    alias P = serdeGetFinalDeepProxy!T;
    static if (isSomeStruct!P)
        enum string[] serdeFinalDeepProxySerializableMembers = [Filter!(serdeIsSerializable!P, aliasSeqOf!(SerializableMembers!P))];
    else
        enum string[] serdeFinalDeepProxySerializableMembers = null;
}

///
version(mir_test) unittest
{

    static struct A
    {
        @serdeIgnore
        int i;

        @serdeKeys("a", "b")
        int m;
    }

    @serdeProxy!(A[string])
    static struct B {}

    @serdeProxy!(B[])
    static struct C {}

    static assert (serdeFinalDeepProxySerializableMembers!C == ["m"]);
}

/++
Final proxy type deserializable members
+/
template serdeFinalProxySerializableMembers(T)
{
    import std.meta: Filter, aliasSeqOf;
    alias P = serdeGetFinalProxy!T;
    static if (isSomeStruct!P)
        enum string[] serdeFinalProxySerializableMembers = [Filter!(serdeIsSerializable!P, aliasSeqOf!(SerializableMembers!P))];
    else
        enum string[] serdeFinalProxySerializableMembers = null;
}

///
version(mir_test) unittest
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

    static assert (serdeFinalProxySerializableMembers!C == ["m"]);
}

/++
Final deep proxy type serializable members
+/
template serdeFinalDeepProxyDeserializableMembers(T)
{
    import std.traits: isAggregateType;
    import std.meta: Filter, aliasSeqOf;
    alias P = serdeGetFinalDeepProxy!T;
    static if (isAggregateType!P)
        enum string[] serdeFinalDeepProxyDeserializableMembers = [Filter!(serdeIsDeserializable!P, aliasSeqOf!(DeserializableMembers!P))];
    else
        enum string[] serdeFinalDeepProxyDeserializableMembers = null;
}

///
version(mir_test) unittest
{

    static struct A
    {
        @serdeIgnore
        int i;

        @serdeKeys("a", "b")
        int m;
    }

    @serdeProxy!(A[string])
    static struct B {}

    @serdeProxy!(B[])
    static struct C {}

    static assert (serdeFinalDeepProxyDeserializableMembers!C == ["m"]);
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
version(mir_test) unittest
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
version(mir_test) unittest
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

/++
Serialization member final proxy type
+/
template serdeFinalSerializationMemberType(T, string member)
{
    import std.traits: hasUDA;
    static if (hasUDA!(__traits(getMember, T, member), serdeProxy))
    {
        alias serdeFinalSerializationMemberType = serdeGetFinalProxy!(serdeGetProxy!(__traits(getMember, T, member)));
    }
    else
    {
        alias serdeFinalSerializationMemberType = serdeGetFinalProxy!(serdeSerializationMemberType!(T, member));
    }
}

/// ditto
template serdeFinalSerializationMemberType(T)
{
    ///
    alias serdeFinalSerializationMemberType(string member) = .serdeFinalSerializationMemberType!(T, member);
}

///
version(mir_test) unittest
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

    static assert (is(serdeFinalSerializationMemberType!(D, "c") == A), serdeFinalSerializationMemberType!(D, "c"));
    static assert (is(serdeFinalSerializationMemberType!(D, "d") == double));
}

/++
Serialization members final proxy types
+/
template serdeSerializationFinalProxyMemberTypes(T)
{
    import std.meta: NoDuplicates, staticMap, aliasSeqOf;
    alias serdeSerializationFinalProxyMemberTypes = NoDuplicates!(staticMap!(serdeGetFinalProxy, staticMap!(serdeFinalSerializationMemberType!T, aliasSeqOf!(serdeFinalProxySerializableMembers!T))));
}

///
version(mir_test) unittest
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
    static assert (is(serdeSerializationFinalProxyMemberTypes!D == AliasSeq!A));
}

/++
Deserialization members final deep proxy types
+/
template serdeDeserializationFinalDeepProxyMemberTypes(T)
{
    import std.meta: NoDuplicates, staticMap, aliasSeqOf;
    import mir.algebraic: isVariant;
    static if (isVariant!T)
        alias serdeDeserializationFinalDeepProxyMemberTypes = NoDuplicates!(T, staticMap!(serdeGetFinalDeepProxy, T.AllowedTypes));
    else
    static if (isAlgebraicAliasThis!T)
    {
        T* aggregate;
        alias A = typeof(__traits(getMember, aggregate, __traits(getAliasThis, T)));
        alias serdeDeserializationFinalDeepProxyMemberTypes = .serdeDeserializationFinalDeepProxyMemberTypes!A;
    }
    else
        alias serdeDeserializationFinalDeepProxyMemberTypes = NoDuplicates!(staticMap!(serdeGetFinalDeepProxy, staticMap!(serdeFinalDeserializationMemberType!T, aliasSeqOf!(serdeFinalDeepProxyDeserializableMembers!T))));
}

///
version(mir_test) unittest
{

    static struct A {}

    @serdeProxy!(A[])
    static struct B {}

    enum R {a, b, c}

    @serdeProxy!(B[R])
    static struct C {}

    @serdeProxy!(B[string])
    static struct E {}

    static struct D
    {
        C c;

        @serdeProxy!E
        int d;
    }

    import std.meta: AliasSeq;
    static assert (is(serdeDeserializationFinalDeepProxyMemberTypes!D == AliasSeq!A), serdeDeserializationFinalDeepProxyMemberTypes!D);
}

/++
Serialization members final deep proxy types
+/
template serdeSerializationFinalDeepProxyMemberTypes(T)
{
    import std.meta: NoDuplicates, staticMap, aliasSeqOf;
    import mir.algebraic: isVariant;
    static if (isVariant!T)
        alias serdeSerializationFinalDeepProxyMemberTypes = NoDuplicates!(T, staticMap!(serdeGetFinalDeepProxy, T.AllowedTypes));
    else
    static if (isAlgebraicAliasThis!T)
    {
        T* aggregate;
        alias A = typeof(__traits(getMember, aggregate, __traits(getAliasThis, T)));
        alias serdeSerializationFinalDeepProxyMemberTypes = .serdeSerializationFinalDeepProxyMemberTypes!A;
    }
    else
        alias serdeSerializationFinalDeepProxyMemberTypes = NoDuplicates!(staticMap!(serdeGetFinalDeepProxy, staticMap!(serdeFinalSerializationMemberType!T, aliasSeqOf!(serdeFinalDeepProxySerializableMembers!T))));
}

///
version(mir_test) unittest
{

    static struct A {}

    @serdeProxy!(A[])
    static struct B {}

    enum R {a, b, c}

    @serdeProxy!(B[R])
    static struct C {}

    @serdeProxy!(B[string])
    static struct E {}

    static struct D
    {
        C c;

        @serdeProxy!E
        int d;
    }

    import std.meta: AliasSeq;
    static assert (is(serdeSerializationFinalDeepProxyMemberTypes!D == AliasSeq!A), serdeSerializationFinalDeepProxyMemberTypes!D);
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
version(mir_test) unittest
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

private template serdeSerializationFinalDeepProxyMemberTypesRecurseImpl(T...)
{
    import std.meta: NoDuplicates, staticMap;
    alias F = NoDuplicates!(T, staticMap!(serdeSerializationFinalDeepProxyMemberTypes, T));
    static if (F.length == T.length)
        alias serdeSerializationFinalDeepProxyMemberTypesRecurseImpl = T;
    else
        alias serdeSerializationFinalDeepProxyMemberTypesRecurseImpl  = .serdeSerializationFinalDeepProxyMemberTypesRecurseImpl!F;
}

private template serdeDeserializationFinalDeepProxyMemberTypesRecurseImpl(T...)
{
    import std.meta: NoDuplicates, staticMap;
    alias F = NoDuplicates!(T, staticMap!(serdeDeserializationFinalDeepProxyMemberTypes, T));
    static if (F.length == T.length)
        alias serdeDeserializationFinalDeepProxyMemberTypesRecurseImpl = T;
    else
        alias serdeDeserializationFinalDeepProxyMemberTypesRecurseImpl  = .serdeDeserializationFinalDeepProxyMemberTypesRecurseImpl!F;
}

/++
Deserialization members final deep proxy types (recursive)
+/
alias serdeDeserializationFinalDeepProxyMemberTypesRecurse(T) = serdeDeserializationFinalDeepProxyMemberTypesRecurseImpl!(serdeGetFinalDeepProxy!T);

///
version(mir_test) unittest
{

    static struct A { double g; }

    @serdeProxy!(A[])
    static struct B {}

    @serdeProxy!(B[string])
    static struct C {}

    @serdeProxy!B
    static struct E {}

    static struct D
    {
        C c;

        @serdeProxy!(E[])
        int d;
    }

    @serdeProxy!D
    static struct F {}

    import std.meta: AliasSeq;
    static assert (is(serdeDeserializationFinalDeepProxyMemberTypesRecurse!F == AliasSeq!(D, A, double)));
}

/++
Serialization members final deep proxy types (recursive)
+/
alias serdeSerializationFinalDeepProxyMemberTypesRecurse(T) = serdeSerializationFinalDeepProxyMemberTypesRecurseImpl!(serdeGetFinalDeepProxy!T);

///
version(mir_test) unittest
{

    static struct A { double g; }

    @serdeProxy!(A[])
    static struct B {}

    @serdeProxy!(B[string])
    static struct C {}

    @serdeProxy!B
    static struct E {}

    static struct D
    {
        C c;

        @serdeProxy!(E[])
        int d;
    }

    @serdeProxy!D
    static struct F {}

    import std.meta: AliasSeq;
    static assert (is(serdeSerializationFinalDeepProxyMemberTypesRecurse!F == AliasSeq!(D, A, double)), serdeSerializationFinalDeepProxyMemberTypesRecurse!F);
}

package string[] sortUniqKeys()(string[] keys)
    @safe pure nothrow
{
    import mir.algorithm.iteration: uniq;
    import mir.array.allocation: array;
    import mir.ndslice.sorting: sort;

    return keys
        .sort!((a, b) {
            if (sizediff_t d = a.length - b.length)
                return d < 0;
            return a < b;
        })
        .uniq
        .array;
}


private template serdeGetKeysIn2(T)
{
    // T* value;
    enum string[] serdeGetKeysIn2(string member) = serdeGetKeysIn!(__traits(getMember, T, member));
}

private template serdeGetKeyOut2(T)
{
    enum string[] serdeGetKeyOut2(string member) = serdeGetKeyOut!(__traits(getMember, T, member)) is null ? null : [serdeGetKeyOut!(__traits(getMember, T, member))];
}

private template serdeFinalDeepProxyDeserializableMemberKeys(T)
{
    import std.meta: staticMap, aliasSeqOf;
    import std.traits: isAggregateType;

    static if (isAggregateType!T)
    {
        import mir.algebraic: isVariant;
        static if (isVariant!T)
            enum string[] serdeFinalDeepProxyDeserializableMemberKeys = getAlgebraicAnnotationsOfVariant!T;
        else
            enum string[] serdeFinalDeepProxyDeserializableMemberKeys = [staticMap!(aliasSeqOf, staticMap!(serdeGetKeysIn2!T, aliasSeqOf!(serdeFinalDeepProxyDeserializableMembers!T)))];
    }
    else
        enum string[] serdeFinalDeepProxyDeserializableMemberKeys = null;
}

package template getAlgebraicAnnotationsOfVariant(T)
{
    import std.meta: staticMap, Filter;
    enum string[] getAlgebraicAnnotationsOfVariant = [staticMap!(serdeGetAlgebraicAnnotation, Filter!(serdeHasAlgebraicAnnotation, T.AllowedTypes))];
}

private template serdeFinalDeepProxySerializableMemberKeys(T)
{
    import std.meta: staticMap, aliasSeqOf;
    import std.traits: isAggregateType;

    static if (isAggregateType!T)
    {
        import mir.algebraic: isVariant;
        static if (isVariant!T)
            enum string[] serdeFinalDeepProxySerializableMemberKeys = getAlgebraicAnnotationsOfVariant!T;
        else
            enum string[] serdeFinalDeepProxySerializableMemberKeys = [staticMap!(aliasSeqOf, staticMap!(serdeGetKeyOut2!T, aliasSeqOf!(serdeFinalDeepProxySerializableMembers!T)))];
    }
    else
        enum string[] serdeFinalDeepProxySerializableMemberKeys = null;
}

private template serdeGetAlgebraicAnnotations(T)
{
    static if (isSomeStruct!T || is(T == enum))
        static if (hasUDA!(T, serdeAlgebraicAnnotation))
            enum string[] serdeGetAlgebraicAnnotations = [getUDA!(T, serdeAlgebraicAnnotation).annotation];
        else
            enum string[] serdeGetAlgebraicAnnotations = null;
    else
        enum string[] serdeGetAlgebraicAnnotations = null;
}

package template serdeIsComplexVariant(T)
{
    import mir.algebraic: isVariant, isNullable;
    static if (isVariant!T)
    {
        enum serdeIsComplexVariant = (T.AllowedTypes.length - isNullable!T) > 1;
    }
    else
    {
        enum bool serdeIsComplexVariant = false;
    }
}

package template isAlgebraicAliasThis(T)
{
    static if (__traits(getAliasThis, T).length)
    {
        import mir.algebraic: isVariant;
        T* aggregate;
        alias A = typeof(__traits(getMember, aggregate, __traits(getAliasThis, T)));
        enum isAlgebraicAliasThis = isVariant!A;
    }
    else
    {
        enum isAlgebraicAliasThis = false;
    }
}

/++
Serialization members final proxy keys (recursive)
+/
template serdeGetSerializationKeysRecurse(T)
{
    import std.meta: staticMap, aliasSeqOf;
    enum string[] serdeGetSerializationKeysRecurse = [staticMap!(aliasSeqOf, staticMap!(serdeFinalDeepProxySerializableMemberKeys, serdeSerializationFinalDeepProxyMemberTypesRecurse!T))].sortUniqKeys;
}

///
version(mir_test) unittest
{
    enum Y
    {
        a,
        b,
        c,
    }

    static struct A { double g; float d; }

    @serdeProxy!A
    static struct B {  int f; }

    @serdeProxy!(B[Y][string])
    static union C {  int f; }

    @serdeProxy!(B[])
    static interface E {  int f() @property; }

    static class D
    {
        C c;

        @serdeProxy!(E[])
        int d;
    }

    @serdeAlgebraicAnnotation("$F")
    @serdeProxy!D
    static struct F { int f; }

    static assert (serdeGetSerializationKeysRecurse!F == ["c", "d", "g"]);

    import mir.algebraic;
    static assert (serdeGetSerializationKeysRecurse!(Nullable!(F, int)) == ["c", "d", "g", "$F"]);
}

/++
Deserialization members final proxy keys (recursive)
+/
template serdeGetDeserializationKeysRecurse(T)
{
    import std.meta: staticMap, aliasSeqOf;
    enum string[] serdeGetDeserializationKeysRecurse = [staticMap!(aliasSeqOf, staticMap!(serdeFinalDeepProxyDeserializableMemberKeys, serdeDeserializationFinalDeepProxyMemberTypesRecurse!T))].sortUniqKeys;
}

///
version(mir_test) unittest
{

    static struct A { double g; float d; }

    @serdeProxy!A
    static struct B {  int f; }

    @serdeProxy!(B[string])
    static union C {  int f; }

    @serdeProxy!(B[])
    static interface E {  int f() @property; }

    static class D
    {
        C c;

        @serdeProxy!(E[])
        int d;
    }

    @serdeAlgebraicAnnotation("$F")
    @serdeProxy!D
    static struct F { int f; }

    static assert (serdeGetDeserializationKeysRecurse!F == ["c", "d", "g"]);

    import mir.algebraic;
    static assert (serdeGetDeserializationKeysRecurse!(Nullable!(F, int)) == ["c", "d", "g", "$F"]);
}

/++
UDA used to force deserializer to initilize members in the order of their definition in the target object/structure.

The attribute force deserializer to create a dummy type (recursively), initializer its fields and then assign them to
to the object members (fields and setters) in the order of their definition.

See_also: $(LREF SerdeOrderedDummy), $(LREF serdeRealOrderedIn), $(LREF serdeIgnoreInIfAggregate).
+/
enum serdeOrderedIn;

/++
UDA used to force deserializer to initilize members in the order of their definition in the target object/structure.

Unlike $(LREF serdeOrderedIn) `serdeRealOrderedDummy` force deserialzier to iterate all DOM keys for each object deserialization member.
It is slower but more universal approach.

See_also: $(LREF serdeOrderedIn), $(LREF serdeIgnoreInIfAggregate)
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

/++
A dummy structure usefull $(LREF serdeOrderedIn) support.
+/
struct SerdeOrderedDummy(T, bool __optionalByDefault = false)
    if (is(serdeGetFinalProxy!T == T) && isSomeStruct!T)
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
            static if (hasField!(T, member))
            {
                static if (__traits(compiles, {__traits(getMember, this, member) = __traits(getMember, value, member);}))
                    __traits(getMember, this, member) = __traits(getMember, value, member);
            }
        }
    }

public:

    static foreach (i, member; serdeFinalProxyDeserializableMembers!T)
    {
        static if (hasField!(T, member))
        {
            static if (hasUDA!(__traits(getMember, T, member), serdeProxy))
            {
                mixin("@(__traits(getAttributes, T." ~ member ~ ")) serdeDeserializationMemberType!(T, `" ~ member ~ "`) " ~ member ~ ";");
            }
            else
            static if (isSomeStruct!(typeof(__traits(getMember, T, member))))
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
                    static if (__traits(hasMember, M, "serdeFinalizeWithFlags"))
                    {
                        __traits(getMember, value, member).serdeFinalizeWithFlags(memberFlags);
                    }
                    static if (__traits(hasMember, M, "serdeFinalize"))
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
        static if (__traits(hasMember, T, "serdeFinalizeWithDummy"))
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
                    static if (__traits(hasMember, M, "serdeFinalizeWithFlags"))
                    {
                        __traits(getMember, value, member).serdeFinalizeWithFlags(memberFlags);
                    }
                    static if (__traits(hasMember, M, "serdeFinalize"))
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
version(mir_test) unittest
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
        
template deserializeValueMemberImpl(alias deserializeValue, alias deserializeScoped)
{
    ///
    SerdeException deserializeValueMemberImpl(string member, Data, T, Context...)(Data data, ref T value, ref SerdeFlags!T requiredFlags, ref Context context)
    {
        import core.lifetime: move;
        import mir.conv: to;

        enum likeList = hasUDA!(__traits(getMember, value, member), serdeLikeList);
        enum likeStruct  = hasUDA!(__traits(getMember, value, member), serdeLikeStruct);
        enum hasProxy = hasUDA!(__traits(getMember, value, member), serdeProxy);
        enum hasScoped = hasUDA!(__traits(getMember, value, member), serdeScoped);

        static assert (likeList + likeStruct <= 1, T.stringof ~ "." ~ member ~ " can't have both @serdeLikeStruct and @serdeLikeList attributes");
        static assert (hasProxy >= likeStruct, T.stringof ~ "." ~ member ~ " should have a Proxy type for deserialization");
        static assert (hasProxy >= likeList, T.stringof ~ "." ~ member ~ " should have a Proxy type for deserialization");

        alias Member = serdeDeserializationMemberType!(T, member);

        static if (hasProxy)
            alias Temporal = serdeGetProxy!(__traits(getMember, value, member));
        else
            alias Temporal = Member;

        static if (hasScoped)
            static if (__traits(compiles, { Temporal temporal; deserializeScoped(data, temporal); }))
                alias impl = deserializeScoped;
            else
                alias impl = deserializeValue;
        else
            alias impl = deserializeValue;

        static immutable excm(string member) = new SerdeException("ASDF deserialisation: multiple keys for member '" ~ member ~ "' in " ~ T.stringof ~ " are not allowed.");

        static if (!hasUDA!(__traits(getMember, value, member), serdeAllowMultiple))
            if (__traits(getMember, requiredFlags, member))
                return excm!member;

        __traits(getMember, requiredFlags, member) = true;

        static if (likeList)
        {
            foreach(elem; data.byElement)
            {
                Temporal temporal;
                if (auto exc = impl(elem, temporal, context))
                    return exc;
                __traits(getMember, value, member).put(move(temporal));
            }
        }
        else
        static if (likeStruct)
        {
            foreach(v; data.byKeyValue(context))
            {
                Temporal temporal;
                if (auto exc = impl(v.value, temporal, context))
                    return exc;
                __traits(getMember, value, member)[v.key.idup] = move(temporal);
            }
        }
        else
        static if (hasProxy)
        {
            Temporal temporal;
            if (auto exc = impl(data, temporal, context))
                return exc;
            __traits(getMember, value, member) = to!(serdeDeserializationMemberType!(T, member))(move(temporal));
        }
        else
        static if (hasField!(T, member))
        {
            if (auto exc = impl(data, __traits(getMember, value, member), context))
                return exc;
        }
        else
        {
            Member temporal;
            if (auto exc = impl(data, temporal, context))
                return exc;
            __traits(getMember, value, member) = move(temporal);
        }

        static if (hasUDA!(__traits(getMember, value, member), serdeTransformIn))
        {
            alias transform = serdeGetTransformIn!(__traits(getMember, value, member));
            static if (hasField!(T, member))
            {
                transform(__traits(getMember, value, member));
            }
            else
            {
                auto temporal = __traits(getMember, value, member);
                transform(temporal);
                __traits(getMember, value, member) = move(temporal);
            }
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
