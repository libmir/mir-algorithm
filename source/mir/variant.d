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
    import std.traits: Largest, isCopyable, hasElaborateDestructor, hasElaborateAssign, hasElaborateCopyConstructor, isEqualityComparable, isOrderingComparable;

    private alias _Types = Types;

    union
    {
        private Types payload;
        private ubyte[Largest!Types.sizeof] bytes;
    }

    private uint type; // 0 for unininit value, index = type - 1

    private enum hasDestructor = anySatisfy!(hasElaborateDestructor, Types);

    static if (hasDestructor)
    ~this() @safe
    {
        S: switch (type)
        {
            static foreach (i, T; Types)
            static if (hasElaborateDestructor!T)
            {
                case i:
                    .destroy!false(trustedGet!T);
                    break S;
            }
            default: return;
        }
    }

    static if (!__traits(compiles, (){ Types[0] arg; }))
        @disable this();

    static if (!allSatisfy!(isCopyable, Types))
        @disable this(this);
    else
    static if (anySatisfy!(hasElaborateCopyConstructor, Types))
    {
        ///
        this(ref return scope typeof(this) rhs)
        {
            this.bytes = rhs.bytes;
            this.type = rhs.type;
            S: switch (type)
            {
                static foreach (i, T; Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        this.trustedGet!T.emplaceRef(rhs.trustedGet!T);
                        return;
                }
                default: return;
            }
        }

        /// ditto
        this(ref return scope const typeof(this) rhs) const
        {
            this.bytes = rhs.bytes;
            this.type = rhs.type;
            S: switch (type)
            {
                static foreach (i, T; Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        this.mutableTrustedGet!T.emplaceRef!(const T)(rhs.trustedGet!T);
                        return;
                }
                default: return;
            }
        }

        /// ditto
        this(ref return scope immutable typeof(this) rhs) immutable
        {
            this.bytes = rhs.bytes;
            this.type = rhs.type;
            S: switch (type)
            {
                static foreach (i, T; Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        this.mutableTrustedGet!T.emplaceRef!(immutable T)(rhs.trustedGet!T);
                        return;
                }
                default: return;
            }
        }
    }

    static if (is(Types[0] == typeof(null)))
    {
        /// Defined if the first type is `typeof(null)`
        bool isNull() const { return type == 0; }
        /// ditto
        void nullify() { this = null; }
        /// ditto
        static if (allSatisfy!(isCopyable, Types[1 .. $]))
        auto get()
        {
            if (!type)
            {
                version(D_Exceptions)
                    throw variantNullException;
                else
                    assert(0, variantNullExceptionMsg);
            }

            Variant!(Types[1 .. $]) ret;
            ret.type = this.type - 1;

            static if (anySatisfy!(hasElaborateCopyConstructor, Types))
            {
                ret.bytes = 0;
                S: switch (type)
                {
                    static foreach (i, T; Types)
                    {
                        static if (hasElaborateCopyConstructor!T)
                        {
                            case i:
                                ret.trustedGet!T.emplaceRef(this.trustedGet!T);
                                break S;
                        }
                    }
                    default:
                        ret.bytes = this.bytes[0 .. ret.bytes.length];
                }
            }
            else
            {
                ret.bytes = this.bytes[0 .. ret.bytes.length];
            }

            return ret;
        }
    }

    static foreach (i, T; Types)
    ///
    void opAssign(T value)
    {
        static if (hasDestructor)
            __dtor;
        type = i;
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
        type = i;
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
        if (_expect(i != type, false))
        {
            version(D_Exceptions)
                throw variantException;
            else
                assert(0, variantExceptionMsg);
        }
        return trustedGet!T;
    }

    static foreach (i, T; Types)
    /// Zero cost always nothrow `get` alternative
    ref inout(T) trustedGet(E)() @trusted @property return inout nothrow
        if (is(E == T))
    {
        assert (i == type);
        return payload[i];
    }

    static foreach (i, T; Types)
    private ref T mutableTrustedGet(E)() @trusted @property return const nothrow
        if (is(E == T))
    {
        assert (i == type);
        return *cast(Types[i]*)&payload[i];
    }

    /++
    Returns: zero based type index.
    +/
    uint typeId() @nogc nothrow const @property
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
                case i:
                    return hashOf(trustedGet!T, type);
            }
            default: assert(0);
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
                case i:
                    return this.trustedGet!T == rhs.trustedGet!T;
            }
            default: assert(0);
        }
    } 

    static if (allSatisfy!(isOrderingComparable, Types))
    /++
    +/
    auto opCmp(ref const typeof(this) rhs) const
    {
        if (auto d = int(this.type) - int(rhs.type))
            return d;
        switch (type)
        {
            static foreach (i, T; Types)
            {
                case i:
                    static if (__traits(hasMember, T, "opCmp"))
                        return this.trustedGet!T.opCmp(rhs.trustedGet!T);
                    else
                        return this.trustedGet!T < rhs.trustedGet!T ? -1 :
                               this.trustedGet!T > rhs.trustedGet!T ? +1 : 0;
            }
            default: assert(0);
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
@safe pure @nogc nothrow
unittest
{
    alias Number = Variant!(int, double);

    Number x = 23;
    Number y = 1.0;

    assert(x.match!((int v) => true, (float v) => false));
    assert(y.match!((int v) => false, (float v) => true));
}


/// Special `typeof(null)` support for the first argument.
@safe pure @nogc
unittest
{
    alias Number = Variant!(typeof(null), int, double);

    Number z = null; // default
    Number x = 23;
    Number y = 1.0;

    () nothrow {
        assert(x.match!((int v) => true, (float v) => false));
        assert(y.match!((int v) => false, (float v) => true));
        assert(z.match!((typeof(null) v) => true, (v) => false));
    } ();

    auto xx = x.get;
    static assert (is(typeof(xx) == Variant!(int, double)));
    assert(xx.match!((int v) => v, (float v) => 0) == 23);

    x = null;
    y.nullify;

    assert(x.isNull);
    assert(y.isNull);
    assert(z.isNull);
    assert(z == y);
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
@safe pure @nogc nothrow
unittest
{
    static struct S { auto bar(int a) { return a; }}
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
@safe pure @nogc nothrow
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
            static foreach (i, T; V._Types)
            {
                case i:
                    static if (__traits(compiles, visitor(variant.trustedGet!T, forward!args)))
                        return visitor(variant.trustedGet!T, forward!args);
                    else
                    static if (exhaustive && !is(T == typeof(null)))
                        static assert(0, V.stringof ~ ": the visitor cann't be caled with type (first argument) " ~ T.stringof ~ " and additional arguments " ~ Args.stringof);
                    else
                    static if (is(T == typeof(null)) && i == 0)
                        assert(0, "Null " ~ V.stringof);
                    else
                    version(D_Exceptions)
                        throw variantMemberException;
                    else
                        assert(0, variantMemberExceptionMsg);
            }
            default: assert(0);
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
                case i:
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
