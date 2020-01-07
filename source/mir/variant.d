/++
This module implements a generic variant type.
+/
module mir.variant;

private static immutable variantExceptionMsg = "mir.variant: the variant stores other type then requested.";
private static immutable variantNulllExceptionMsg = "mir.variant: the variant is empty and doesn't store any value.";
private static immutable variantMemberExceptionMsg = "mir.variant: the variant is stores the type that isn't compatible with the user proveded visitor and arguments.";

version (D_Exceptions)
{
    private static immutable variantException = new Exception(variantExceptionMsg);
    private static immutable variantNulllException = new Exception(variantNulllExceptionMsg);
    private static immutable variantMemberException = new Exception(variantMemberExceptionMsg);
}

/++
Variant Type (aka Algebraic Type) with clever member access.

Compatible with BetterC mode.
+/
struct Variant(Types...)
    if (Types.length)
{
    import mir.utility: swap;
    import mir.conv: emplaceRef;
    import std.meta: anySatisfy;
    import std.traits: Largest, hasElaborateDestructor, hasElaborateAssign;

    private alias _Types = Types;

    private void[Largest!Types.sizeof] payload = void;
    private uint type; // 0 for unininit value, index = type - 1
    private enum hasDestructor = anySatisfy!(hasElaborateDestructor, Types);
pure nothrow @nogc:
    static if (hasDestructor)
    ~this()
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
        type = 0;
    }

    static if (anySatisfy!(hasElaborateAssign, Types))
    this(this)
    {
        S: switch (type)
        {
            static foreach (i, T; Types) static if (hasElaborateAssign!T)
            {
                case i + 1:
                    __ctor(trustedGet!T);
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
        type = 0;
    }

    static foreach (i, T; Types)
    ///
    void opAssign(T value)
    {
        static if (hasDestructor)
            __dtor;
        type = i + 1;
        emplaceRef(trustedGet!T);
        swap(trustedGet!T, value);
    }

    static foreach (i, T; Types)
    ///
    this(T value)
    {
        type = i + 1;
        emplaceRef(trustedGet!T);
        swap(trustedGet!T, value);
    }

    static foreach (i, T; Types)
    ///
    ref inout(E) get(E : T)() @property return inout
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
            version(D_Exceptions)
                throw variantException;
            else
                assert(0, variantExceptionMsg);
        }
        return trustedGet!T;
    }

    static foreach (i, T; Types)
    /// Zero cost always nothrow `get` alternative
    ref inout(E) trustedGet(E : T)() @trusted @property return inout nothrow
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
}

/++
Params:
    visitor = a function name alias
    forceAllTypes = if `true` checks at compile time, that the member can be called for all types.
+/
template visit(alias visitor, bool forceAllTypes = true)
{
    import std.traits: Unqual;
    ///
    auto ref visit(V, Args...)(auto ref V variant, auto ref Args args)
        if (is(Unqual!V : Variant!Types, Types))
    {
        import mir.functional: forward;
        switch (variant.type)
        {
            case 0:
                version(D_Exceptions)
                    throw variantNulllException;
                else
                    assert(0, variantNulllExceptionMsg);
            static foreach (i, T; V._Types)
            static if (forceAllTypes || __traits(compiles, { return visitor(variant.trustedGet!T, forward!args); }))
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

/++
Params:
    visitor = a function name alias
+/
template optionalVisit(alias visitor)
{
    import std.traits: Unqual;
    ///
    bool optionalVisit(Result, V, Args...)(out Result result, auto ref V variant, auto ref Args args)
        if (is(Unqual!V : Variant!Types, Types))
    {
        import mir.functional: forward;
        switch (variant.type)
        {
            static foreach (i, T; V._Types)
            static if (__traits(compiles, { result = visitor(variant.trustedGet!T, forward!args); }))
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
