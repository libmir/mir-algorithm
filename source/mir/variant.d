/++
This module implements a generic variant type.
+/
module mir.variant;

import mir.functional: naryFun;

private static immutable variantExceptionMsg = "mir.variant: the variant stores other type then requested.";
private static immutable variantNullExceptionMsg = "mir.variant: the variant is empty and doesn't store any value.";
private static immutable variantMemberExceptionMsg = "mir.variant: the variant is stores the type that isn't compatible with the user provided visitor and arguments.";

version (D_Exceptions)
{
    private static immutable variantException = new Exception(variantExceptionMsg);
    private static immutable variantNullException = new Exception(variantNullExceptionMsg);
    private static immutable variantMemberException = new Exception(variantMemberExceptionMsg);
}

private enum hasToHash(T) = __traits(hasMember, T, "toHash");
private enum hasOpEquals(T) = __traits(hasMember, T, "opEquals");
private enum isPOD(T) = __traits(isPOD, T);
private enum Sizeof(T) = T.sizeof;

/++
Variant Type (aka Algebraic Type) with clever member access.

Compatible with BetterC mode.
+/
struct Variant(Types...)
    if (Types.length)
{
    import mir.conv: emplaceRef;
    import mir.utility: max, swap;
    import std.meta: anySatisfy, allSatisfy, templateOr, staticMap;
    import std.traits: Largest, hasElaborateDestructor, hasElaborateAssign, hasElaborateCopyConstructor, isEqualityComparable, isOrderingComparable;

    private alias _Types = Types;

    union
    {
        private ubyte[Largest!Types.sizeof] bytes;
        private Types payload;
    }

    private uint type; // 0 for unininit value, index = type - 1

    private enum hasDestructor = anySatisfy!(hasElaborateDestructor, Types);

    static if (hasDestructor)
    ~this() @safe
    {
        S: switch (type)
        {
            static foreach (i, T; Types) static if (hasElaborateDestructor!T)
            {
                case i + 1:
                    .destroy!false(trustedGet!T);
                    break S;
            }
            default: break;
        }
    }

    static if (anySatisfy!(hasElaborateCopyConstructor, Types))
    this(this)
    {
        S: switch (type)
        {
            static foreach (i, T; Types) static if (hasElaborateCopyConstructor!T)
            {
                case i + 1:
                    trustedGet!T.__xpostblit();
                    break S;
            }
            default: break;
        }
    }

    ///
    this(typeof(null))
    {
    }

    ///
    void opAssign(typeof(null))
    {
        static if (hasDestructor)
            __dtor;
        bytes[] = 0;
        type = 0;
    }

    static foreach (i, T; Types)
    ///
    void opAssign(T value)
    {
        static if (hasDestructor)
            __dtor;
        type = i + 1;
        static if (__traits(isZeroInit, T))
        {
            bytes[] = 0;
        }
        else
        {
            emplaceRef(trustedGet!T);
            bytes[T.sizeof .. $] = 0;
        }
        swap(trustedGet!T, value);
    }

    static foreach (i, T; Types)
    ///
    this(T value)
    {
        type = i + 1;
        static if (!__traits(isZeroInit, T))
            emplaceRef(trustedGet!T);
        swap(trustedGet!T, value);
    }

    static foreach (i, T; Types)
    ///
    ref inout(T) get(E)() @property return inout
        if (is(E == T))
    {
        import mir.utility: _expect;
        if (_expect(i + 1 != type, false))
        {
            if (i == 0)
            {
                version(D_Exceptions)
                    throw variantNullException;
                else
                    assert(0, variantNullExceptionMsg);
            }
            else
            {
                version(D_Exceptions)
                    throw variantException;
                else
                    assert(0, variantExceptionMsg);
            }
        }
        return trustedGet!T;
    }

    static foreach (i, T; Types)
    /// Zero cost always nothrow `get` alternative
    ref inout(T) trustedGet(E)() @trusted @property return inout nothrow
        if (is(E == T))
    {
        assert (i + 1 == type);
        return payload[i];
    }

    /++
    Returns: true for the unassigned instance.
    +/
    bool empty() nothrow const @property
    {
        return type == 0;
    }

    /++
    Returns: zero if the instance is unassigned and type index starting with 1 otherwise.
    +/
    uint typeId() nothrow const @property
    {
        return type;
    }

    static if (allSatisfy!(templateOr!(isPOD, hasToHash), Types))
    /++
    +/
    size_t toHash()
    {
        static if (allSatisfy!(isPOD, Types))
        {
            static if (this.sizeof <= 16)
            {
                return hashOf(bytes, type);
            }
            else
            {
                static if (this.sizeof <= ubyte.max)
                    alias UInt = ubyte;
                else
                static if (this.sizeof <= ushort.max)
                    alias UInt = ushort;
                else
                    alias UInt = uint;

                static immutable UInt[Types.length + 1] sizes = [0, staticMap!(Sizeof, Types)];
                return hashOf(bytes[0 .. sizes[type]], type);
            }
        }
        else
        switch (type)
        {
            static foreach (i, T; Types)
            {
                case i + 1:
                    return hashOf(trustedGet!T, type);
            }
            default:
                return 0;
        }
    }

    static if (allSatisfy!(templateOr!(isPOD, hasOpEquals), Types))
    /++
    +/
    auto opEquals(ref const typeof(this) rhs) const
    {
        if (this.type != rhs.type)
            return false;
        switch (type)
        {
            static foreach (i, T; Types)
            {
                case i + 1:
                    return this.trustedGet!T == rhs.trustedGet!T;
            }
            default:
                return true;
        }
    } 

    static if (allSatisfy!(isOrderingComparable, Types))
    /++
    +/
    auto opCmp(ref const typeof(this) rhs) const
    {
        if (int d = this.type - rhs.type)
            return d;
        switch (type)
        {
            static foreach (i, T; Types)
            {
                case i + 1:
                    static if (__traits(hasMember, T, "opCmp"))
                        return this.trustedGet!T.opCmp(rhs.trustedGet!T);
                    else
                        return this.trustedGet!T < rhs.trustedGet!T ? -1 :
                               this.trustedGet!T > rhs.trustedGet!T ? +1 : 0;
            }
            default:
                return 0;
        }
    }
}

/// Test for opCmp, opEqual, toHash
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import core.stdc.string: memcmp;

    static struct C(ubyte payloadSize, bool isPOD, bool hasToHash = true, bool hasOpEquals = true)
    {
        ubyte[payloadSize] payload;

    const:

        static if (!isPOD)
        {
            this(this) {}
            ~this() {}
        }

    @safe pure nothrow @nogc:


    static if (hasToHash)
        size_t toHash() { return hashOf(payload); }

    static if (hasOpEquals)
        auto opEquals(ref const typeof(this) rhs) @trusted { return memcmp(payload.ptr, rhs.payload.ptr, payload.length); }
        auto opCmp(ref const typeof(this) rhs) { return payload == rhs.payload; }
    }

    static foreach (size1; [1, 2, 4, 8, 10, 16, 20])
    static foreach (size2; [1, 2, 4, 8, 10, 16, 20])
    static if (size1 != size2)
    static foreach (isPOD; [true, false])
    static foreach (hasToHash; [true, false])
    static foreach (hasOpEquals; [true, false])
    {{
        alias T = Variant!(
                double,
                C!(size1, isPOD, hasToHash, hasOpEquals),
                C!(size2, isPOD, hasToHash, hasOpEquals));
        static assert (__traits(hasMember, T, "toHash") == isPOD || hasToHash);
        static assert (__traits(hasMember, T, "opEquals") == isPOD || hasOpEquals);
        static assert (__traits(hasMember, T, "opCmp"));
    }}
}

/++
Applies a delegate or function to the given Variant depending on the held type,
ensuring that all types are handled by the visiting functions.
+/
alias match(visitors...) = visit!(naryFun!visitors, true);

///
@safe pure @nogc
unittest
{
    alias Number = Variant!(int, double);

    Number x = 23;
    Number y = 1.0;

    assert(x.match!((int v) => true, (float v) => false));
    assert(y.match!((int v) => false, (float v) => true));
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the visiting functions.
+/
alias tryMatch(visitors...) = visit!(naryFun!visitors, false);

///
@safe pure @nogc
unittest
{
    alias Number = Variant!(int, double);

    Number x = 23;

    assert(x.tryMatch!((int v) => true));
}

/++
Applies a member handler to the given Variant depending on the held type,
ensuring that all types are handled by the visiting handler.
+/
alias getMember(string member) = visit!(getMemberHandler!member, true);

///
@safe pure @nogc
unittest
{
    static struct S { int bar(int a) { return a; }}
    static struct C { alias bar = (double a) => a * 2; }

    alias V = Variant!(S, C);

    V x = S();
    V y = C();

    assert(x.getMember!"bar"(2) == 2);
    assert(y.getMember!"bar"(2) == 4);
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the member visitor.
Throws: Exception
+/
alias tryGetMember(string member) = visit!(getMemberHandler!member, false);

///
version(mir_test)
@safe pure @nogc
unittest
{
    static struct S { int bar(int a) { return a; }}
    static struct C { alias Bar = (double a) => a * 2; }

    alias V = Variant!(S, C);

    V x = S();
    V y = C();

    assert(x.tryGetMember!"bar"(2) == 2);
    assert(y.tryGetMember!"Bar"(2) == 4);
}

///
version(mir_test)
@safe pure @nogc
unittest
{
    alias Number = Variant!(int, double);

    Number x = Number(23);
    Number y = Number(1.0);

    assert(x.match!((int v) => true, (float v) => false));
    assert(y.match!((int v) => false, (float v) => true));
}

private template getMemberHandler(string member)
{
    ///
    auto ref getMemberHandler(V, Args...)(ref V value, auto ref Args args)
    {
        static if (Args.length == 0)
        {
            return __traits(getMember, value, member);
        }
        else
        {
            import core.lifetime: forward;
            return __traits(getMember, value, member)(forward!args);
        }
    }
}

/++
Params:
    visitor = a function name alias
    exhaustive = if `true` checks at compile time, that the visitor can be called for all types.
+/
template visit(alias visitor, bool exhaustive = true)
{
    import std.traits: Unqual;
    ///
    auto ref visit(V, Args...)(auto ref V variant, auto ref Args args)
        if (is(Unqual!V : Variant!Types, Types))
    {
        import core.lifetime: forward;
        switch (variant.type)
        {
            case 0:
                version(D_Exceptions)
                    throw variantNullException;
                else
                    assert(0, variantNullExceptionMsg);
            static foreach (i, T; V._Types)
            static if (exhaustive || __traits(compiles, visitor(variant.trustedGet!T, forward!args)))
            {
                case i + 1:
                    return visitor(variant.trustedGet!T, forward!args);
            }
            else
            static if (exhaustive)
                static assert(0, V.stringof ~ ": the visitor cann't be caled with type (first argument) " ~ T.stringof ~ " and additional arguments " ~ Args.stringof);
            default:
                version(D_Exceptions)
                    throw variantMemberException;
                else
                    assert(0, variantMemberExceptionMsg);
        }
    }
}

///
version(mir_test)
@safe pure @nogc
unittest
{
    static struct S { int a; }

    Variant!(S, double) variant;
    variant = 1.0;
    variant.visit!((ref value, b) => value += b, false)(2);
    assert (variant.get!double == 3);

    alias fun = (ref value) {
        static if (is(typeof(value) == S))
            value.a += 2;
        else
           value += 2;
    };

    variant.visit!fun;
    assert (variant.get!double == 5);

    variant = S(4);
    variant.visit!fun;
    assert (variant.get!S.a == 6);
}

/++
Params:
    visitor = a function name alias
+/
template optionalVisit(alias visitor)
{
    import std.traits: Unqual;
    ///
    bool optionalVisit(Result, V, Args...)(ref Result result, auto ref V variant, auto ref Args args) @property
        if (is(Unqual!V : Variant!Types, Types))
    {
        import core.lifetime: forward;
        switch (variant.type)
        {
            static foreach (i, T; V._Types)
            static if (__traits(compiles, result = visitor(variant.trustedGet!T, forward!args)))
            {
                case i + 1:
                    result = visitor(variant.trustedGet!T, forward!args);
                    return true;
            }
            default:
                return false;
        }
    }
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    static struct S { int a; }

    Variant!(S, double) variant;

    double result = 100;

    // do nothing because of variant isn't initialized
    optionalVisit!((ref value) => value)(result, variant);
    assert(result == 100);

    variant = S(2);
    // do nothing because of lambda can't compile
    optionalVisit!((ref value) => value)(result, variant);
    assert(result == 100);

    variant = 3.0;
    optionalVisit!((ref value) => value)(result, variant);
    assert (result == 3);
}
