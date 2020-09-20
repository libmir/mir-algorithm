/++
This module implements a generic variant type.
+/
module mir.variant;

private static immutable variantExceptionMsg = "mir.variant: the variant stores other type then requested.";
private static immutable variantNulllExceptionMsg = "mir.variant: the variant is empty and doesn't store any value.";
private static immutable variantMemberExceptionMsg = "mir.variant: the variant is stores the type that isn't compatible with the user provided visitor and arguments.";

version (D_Exceptions)
{
    private static immutable variantException = new Exception(variantExceptionMsg);
    private static immutable variantNulllException = new Exception(variantNulllExceptionMsg);
    private static immutable variantMemberException = new Exception(variantMemberExceptionMsg);
}

private enum int alignOf(T) = T.alignof;

private enum hasToHash(T) = __traits(hasMember, T, "toHash");
private enum hasToHash(T) = __traits(hasMember, T, "opCmp");
private enum hasToHash(T) = __traits(hasMember, T, "opEquals");
private enum isPOD(T) = __traits(isPOD, T);

private template LargestAlignOf(T...)
{
    static if (T.length == 0)
        enum size_t LargestAlignOf = 0;
    else
    {
        enum tail = LargestAlignOf!(T[1 .. $]);
        enum size_t LargestAlignOf = T[0].alignof > tail ? T[0].alignof : tail;
    }
}

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

    align(max(4, staticMap!(alignOf, Types)))
    private uint type; // 0 for unininit value, index = type - 1
    private align(LargestAlignOf!Types) ubyte[Largest!Types.sizeof] payload;
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
        payload[] = 0;
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
            payload[] = 0;
        }
        else
        {
            emplaceRef(trustedGet!T);
            payload[T.sizeof .. $] = 0;
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
    ref inout(T) get(E : T)() @property return inout
    {
        import mir.utility: _expect;
        if (_expect(i + 1 != type, false))
        {
            if (i == 0)
            {
                version(D_Exceptions)
                    throw variantNulllException;
                else
                    assert(0, variantNulllExceptionMsg);
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
    ref inout(T) trustedGet(E : T)() @trusted @property return inout nothrow
    {
        assert (i + 1 == type);
        return *cast(inout(T)*)payload.ptr;
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
        static if (this.sizeof <= 16)
        {
            return hashOf(payload, type);
        }
        else
        static if (allSatisfy!(isPOD, Types))
        {
            static immutable sizes = [size_t(0), staticMap!(Sizeof, Types)];
            return hashOf(payload[0 .. sizes[type]], type);
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

    static if (allSatisfy!(isEqualityComparable, Types))
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

/++
Params:
    visitor = a function name alias
    forceAllTypes = if `true` checks at compile time, that the visitor can be called for all types.
+/
template visit(alias visitor, bool forceAllTypes = true)
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
                    throw variantNulllException;
                else
                    assert(0, variantNulllExceptionMsg);
            static foreach (i, T; V._Types)
            static if (forceAllTypes || __traits(compiles, visitor(variant.trustedGet!T, forward!args)))
            {
                case i + 1:
                    return visitor(variant.trustedGet!T, forward!args);
            }
            else
            static if (forceAllTypes)
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
