/++
This module implements a generic variant type.
+/
module mir.variant;

import mir.functional: naryFun;
import std.meta: allSatisfy;

private static immutable variantExceptionMsg = "mir.variant: the variant stores other type then requested.";
private static immutable variantNullExceptionMsg = "mir.variant: the variant is empty and doesn't store any value.";
private static immutable variantMemberExceptionMsg = "mir.variant: the variant is stores the type that isn't compatible with the user provided visitor and arguments.";

version (D_Exceptions)
{
    private static immutable variantException = new Exception(variantExceptionMsg);
    private static immutable variantNullException = new Exception(variantNullExceptionMsg);
    private static immutable variantMemberException = new Exception(variantMemberExceptionMsg);
}

private alias ConstOf(T) = const T;
private enum Alignof(T) = T.alignof;
private enum canConstructWith(From, To) = __traits(compiles, (From a) { To b = a; } );
private enum canImplicitlyRemoveConst(T) = __traits(compiles, {static T _function_(ref const T a) { return a; }} );
private enum canRemoveConst(T) = canConstructWith!(const T, T);
private enum canRemoveImmutable(T) = canConstructWith!(immutable T, T);
private enum hasConstConstruction(T) = __traits(compiles, (const T a) { auto b = a; } );
private enum hasImmutableConstruction(T) = __traits(compiles, (immutable T a) { auto b = a; } );
private enum hasMutableConstruction(T) = __traits(compiles, (T a) { auto b = a; } );
private enum hasOpPostMove(T) = __traits(hasMember, T, "opPostMove");
private enum hasSemiImmutableConstruction(T) = __traits(compiles, (const T a) { immutable b = a; } );
private enum hasToHash(T) = __traits(hasMember, T, "toHash");
private enum isCopyable(S) = __traits(isCopyable, S); 
private enum isPOD(T) = __traits(isPOD, T);
private enum isVariant(T) = __traits(hasMember, T, "__isVariant");
private enum Sizeof(T) = T.sizeof;

private template staticIsSorted(alias cmp, Seq...)
{
    static if (Seq.length <= 1)
        enum staticIsSorted = true;
    else static if (Seq.length == 2)
        enum staticIsSorted = cmp!(Seq[0], Seq[1]);
    else
    {
        enum staticIsSorted =
            cmp!(Seq[($ / 2) - 1], Seq[$ / 2]) &&
            staticIsSorted!(cmp, Seq[0 .. $ / 2]) &&
            staticIsSorted!(cmp, Seq[$ / 2 .. $]);
    }
}

private template TryRemoveConst(T)
{
    import std.traits: Unqual;
    alias U = Unqual!T;
    static if (canImplicitlyRemoveConst!U)
    {
        alias TryRemoveConst = U;
    }
    else
    {
        alias TryRemoveConst = T;
    }
}

unittest
{
    static assert(is(TryRemoveConst!(const int) == int));
}

private template TypeCmp(A, B)
{
    enum bool TypeCmp = is(A == B) ? false:
    is(A == typeof(null)) ? true:
    is(B == typeof(null)) ? false:
    A.sizeof < B.sizeof ? true:
    A.sizeof > B.sizeof ? false:
    A.mangleof < B.mangleof;
}

private template isInstanceOf(alias S)
{
    enum isInstanceOf(T) = is(T == S!Args, Args...);
}

private struct VariantSet(Sets...);

/++
Dummy type for $(LREF Variant) self-referencing.
+/
struct SetAlias(uint id);
///ditto
alias This = SetAlias!0;

/++
+/
template TypeSet(T...)
{
    import std.meta: NoDuplicates, staticSort, staticMap;
    // sort types by siezeof and them mangleof
    static if (is(staticMap!(TryRemoveConst, T) == T))
        static if (is(NoDuplicates!T == T))
            static if (staticIsSorted!(TypeCmp, T))
                struct TypeSet;
            else
                alias TypeSet = .TypeSet!(staticSort!(TypeCmp, T));
        else
            alias TypeSet = TypeSet!(NoDuplicates!T);
    else
        alias TypeSet = staticMap!(TryRemoveConst, T);
}


unittest
{
    struct S {}
    alias C = S;
    alias Int = int;
    static assert(__traits(isSame, TypeSet!(S, int), TypeSet!(Int, C)));
    static assert(__traits(isSame, TypeSet!(S, int, int), TypeSet!(Int, C)));
    static assert(!__traits(isSame, TypeSet!(uint, S), TypeSet!(int, S)));
}


/++
+/
template Variants(Sets...)
    if (allSatisfy!(isInstanceOf!TypeSet, Sets))
{
    import std.meta: staticMap;
    import mir.internal.utility: Iota;

    private alias TypeSetsInst(uint id) = Algebraic!(id, Sets);
    ///
    alias Variants = staticMap!(TypeSetsInst, Iota!(Sets.length));
}

private static struct __Null()
{
    @safe pure nothrow @nogc const:
        size_t toHash() {return 0;}
        bool opEquals(__Null) { return true; }
        int opCmp(__Null) { return 0; }

    typeof(null) __self() @property { return null; }
    typeof(null) __self(typeof(null)) @property { return null; }
    this(typeof(null)) inout {}
    string toString() { return "null"; }
}

///
struct Algebraic(uint _setId, _TypeSets...)
    if (allSatisfy!(isInstanceOf!TypeSet, _TypeSets))
{
    import core.lifetime: moveEmplace;
    import mir.conv: emplaceRef;
    import std.meta: AliasSeq, anySatisfy, allSatisfy, staticMap, templateOr;
    import std.typecons: ReplaceTypeUnless;
    import std.traits:
        hasElaborateCopyConstructor,
        hasElaborateDestructor,
        isEqualityComparable,
        isOrderingComparable,
        Largest,
        TemplateArgsOf
        ;

    private template __ApplyAliasesImpl(uint length, Types...)
    {
        static if (length == 0)
            alias __ApplyAliasesImpl = Types;
        else
        {
            enum next  = length - 1;
            import std.typecons: ReplaceTypeUnless;
            alias __ApplyAliasesImpl = __ApplyAliasesImpl!(next,
                ReplaceTypeUnless!(isVariant, SetAlias!next, Algebraic!(next, _TypeSets), Types));
        }
    }

    private enum __isVariant;

    ///
    alias __Types = __ApplyAliasesImpl!(_TypeSets.length, TemplateArgsOf!(_TypeSets[_setId]));

    union
    {
        static if (is(__Types[0] == typeof(null)))
            private alias __Payload =  AliasSeq!(__Null!(), __Types[1 .. $]);
        else
            private alias __Payload = __Types;

        private __Payload __payload;

        static if (__Types.length == 0 || is(__Types == AliasSeq!(typeof(null))))
            private ubyte[0] __bytes;
        else
            private ubyte[Largest!__Payload.sizeof] __bytes;
    }

    static if (__Types.length)
    {
        static if (__Types.length > 1)
        {
            import mir.utility: max;
            private enum __alignof = max(staticMap!(Alignof, __Payload));
            static if ((__bytes.length | __alignof) & 1)
                private ubyte __type; 
            else
            static if ((__bytes.length | __alignof) & 2)
                private ushort __type;
            else
                private uint __type;
        }
        else
        {
            private enum uint __type = 0;
        }
    }

    static foreach (i, T; __Types)
    {
        /// Zero cost always nothrow `get` alternative
        auto ref __trustedGet(E)() @trusted @property return inout nothrow
            if (is(E == T))
        {
            assert (i == __type);
            static if (is(T == typeof(null)))
                return null;
            else
                return __payload[i];
        }

        private ref T __mutableTrustedGet(E)() @trusted @property return const nothrow
            if (is(E == T))
        {
            assert (i == __type);
            return *cast(__Types[i]*)&__payload[i];
        }

        ///
        auto ref get(E)() @property return inout
            if (is(E == T))
        {
            import mir.utility: _expect;
            static if (__Types.length > 1)
            {
                if (_expect(i != __type, false))
                {
                    version(D_Exceptions)
                        throw variantException;
                    else
                        assert(0, variantExceptionMsg);
                }
            }
            return __trustedGet!T;
        }
        
        static if (hasMutableConstruction!T)
        ///
        this(T value) @trusted
        {
            static if (__Types.length > 1)
                __type = i;
            static if (!is(T == typeof(null)))
                moveEmplace(value, __payload[i]);
        }

        static if (!hasSemiImmutableConstruction!T)
        {
            static if (hasConstConstruction!T)
            ///
            this(const T value) const
            {
                static if (__Types.length > 1)
                    __type = i;
                emplaceRef!(const T)(__mutableTrustedGet!T, value);
            }

            static if (hasImmutableConstruction!T)
            ///
            this(immutable T value) immutable
            {
                static if (__Types.length > 1)
                    __type = i;
                emplaceRef!(immutable T)(__mutableTrustedGet!T, value);
            }
        }
        else
        {
            ///
            this(const T value) immutable
            {
                static if (__Types.length > 1)
                    __type = i;
                emplaceRef!(immutable T)(__mutableTrustedGet!T, value);
            }
        }

        static if (__traits(compiles, (ref T a, ref T b) { moveEmplace(a, b); }))
        ///
        ref opAssign(T value) return @trusted
        {
            static if (__traits(hasMember, this, "__dtor"))
                __dtor;
            static if (__Types.length > 1)
                __type = i;
            static if (__traits(isZeroInit, T) || is(T == typeof(null)))
            {
                __bytes[] = 0;
            }
            else
            {
                __bytes[__Payload[i].sizeof .. $] = 0;
            }
            static if (!is(T == typeof(null)))
                moveEmplace(value, __payload[i]);
            return this;
        }

        static if (isEqualityComparable!T)
        /++
        +/
        auto opEquals()(auto ref const T rhs) const
        {
            static if (__Types.length > 1)
                if (__type != i)
                    return false;
            return __trustedGet!T == rhs;
        } 

        static if (isOrderingComparable!T)
        /++
        +/
        auto opCmp()(auto ref const T rhs) const
        {
            static if (__Types.length > 1)
                if (auto d = int(__type) - int(rhs.__type))
                    return d;
            static if (__traits(hasMember, T, "opCmp"))
                return __trustedGet!T.opCmp(rhs);
            else
                return __trustedGet!T < rhs ? -1 :
                    __trustedGet!T > rhs ? +1 : 0;
        }
    }

    static if (anySatisfy!(hasElaborateDestructor, __Types))
    ~this() @safe
    {
        S: switch (__type)
        {
            static foreach (i, T; __Types)
            static if (hasElaborateDestructor!T)
            {
                case i:
                    .destroy!false(__trustedGet!T);
                    break S;
            }
            default: return;
        }
    }


    static if (anySatisfy!(hasOpPostMove, __Types))
    void opPostMove(const ref typeof(this) old)
    {
        S: switch (__type)
        {
            static foreach (i, T; __Types)
            static if (hasOpPostMove!T)
            {
                case i:
                    this.__payload[i].opPostMove(old.__payload[i]);
                    return;
            }
            default: return;
        }
    }

    private enum allCopyable = allSatisfy!(isCopyable, __Types);

    static if (__Types.length)
        static if (!__traits(compiles, (){ __Types[0] arg; }))
            @disable this();

    static if (!allCopyable)
        @disable this(this);
    else
    static if (anySatisfy!(hasElaborateCopyConstructor, __Types))
    {
        private enum __allCanRemoveConst = allSatisfy!(canRemoveConst, __Types);
        private enum __allHaveConstConstruction = allSatisfy!(hasConstConstruction, __Types);
        private enum __allHaveImmutableConstruction = allSatisfy!(hasImmutableConstruction, __Types);
        private enum __allHaveMutableConstruction = allSatisfy!(hasMutableConstruction, __Types);
        private enum __allHaveSemiImmutableConstruction = allSatisfy!(hasSemiImmutableConstruction, __Types);

        static if (__allHaveMutableConstruction)
        this(return ref scope typeof(this) rhs)
        {
            this.__bytes = rhs.__bytes;
            static if (__Types.length > 1)
                this.__type = rhs.__type;
            S: switch (__type)
            {
                static foreach (i, T; __Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        this.__payload[i].emplaceRef(rhs.__payload[i]);
                        return;
                }
                default: return;
            }
        }

        static if (__allHaveConstConstruction)
        this(return ref scope const typeof(this) rhs) const
        {
            this.__bytes = rhs.__bytes;
            static if (__Types.length > 1)
                this.__type = rhs.__type;
            S: switch (__type)
            {
                static foreach (i, T; __Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        this.__mutableTrustedGet!T.emplaceRef!(const T)(rhs.__payload[i]);
                        return;
                }
                default: return;
            }
        }

        static if (__allHaveImmutableConstruction)
        this(return ref scope immutable typeof(this) rhs) immutable
        {
            this.__bytes = rhs.__bytes;
            static if (__Types.length > 1)
                this.__type = rhs.__type;
            S: switch (__type)
            {
                static foreach (i, T; __Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        this.__mutableTrustedGet!T.emplaceRef!(immutable T)(rhs.__payload[i]);
                        return;
                }
                default: return;
            }
        }

        static if (__allHaveSemiImmutableConstruction)
        this(return ref scope const typeof(this) rhs) immutable
        {
            this.__bytes = rhs.__bytes;
            static if (__Types.length > 1)
                this.__type = rhs.__type;
            S: switch (__type)
            {
                static foreach (i, T; __Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        emplaceRef!(immutable T)(this.__mutableTrustedGet!T, rhs.__trustedGet!T);
                        return;
                }
                default: return;
            }
        }

        static if (__allCanRemoveConst && __allHaveMutableConstruction)
        this(return ref scope const typeof(this) rhs)
        {
            this.__bytes = rhs.__bytes;
            static if (__Types.length > 1)
                this.__type = rhs.__type;
            S: switch (__type)
            {
                static foreach (i, T; __Types)
                static if (hasElaborateCopyConstructor!T)
                {
                    case i:
                        this.__trustedGet!T.emplaceRef(rhs.__trustedGet!T);
                        return;
                }
                default: return;
            }
        }

        static if (__allCanRemoveConst && __allHaveMutableConstruction)
        ref opAssign(return ref scope const typeof(this) rhs) return
        {
            static if (__traits(hasMember, this, "__dtor"))
                __dtor;
            // don't need emplace here
            __ctor(rhs);
            return this;
        }

        static if (__allCanRemoveConst && __allHaveMutableConstruction)
        ref opAssign(typeof(this) rhs) return @trusted
        {
            moveEmplace(rhs, this);
        }
    }

    static if (is(__Types[0] == typeof(null)))
    {
        /// Defined if the first type is `typeof(null)`
        bool isNull() const { return __type == 0; }
        /// ditto
        void nullify() { this = null; }

        static if (allSatisfy!(isCopyable, __Types[1 .. $]) && __Types.length != 2)
        /// ditto
        auto get()
        {
            if (!__type)
            {
                version(D_Exceptions)
                    throw variantNullException;
                else
                    assert(0, variantNullExceptionMsg);
            }
            static if (__Types.length > 1)
            {
                Variant!(__Types[1 .. $]) ret;
                static if (ret.__Types.length > 1)
                    ret.__type = cast(typeof(ret.__type))(this.__type - 1);

                static if (anySatisfy!(hasElaborateCopyConstructor, __Types))
                {
                    ret.__bytes = 0;
                    S: switch (__type)
                    {
                        static foreach (i, T; __Types)
                        {
                            static if (hasElaborateCopyConstructor!T)
                            {
                                case i:
                                    ret.__trustedGet!T.emplaceRef(this.__trustedGet!T);
                                    break S;
                            }
                        }
                        default:
                            ret.__bytes = this.__bytes[0 .. ret.__bytes.length];
                    }
                }
                else
                {
                    ret.__bytes = this.__bytes[0 .. ret.__bytes.length];
                }

                return ret;
            }
        }

        static if (__Types.length == 2)
        /// ditto
        ref inout(__Types[1]) get() inout
        {
            return get!(__Types[1]);
        }
    }

    static if (__Types.length)
    /++
    Returns: zero based type index.
    +/
    uint __typeId() @nogc nothrow const @property
    {
        return __type;
    }

    static if (allSatisfy!(templateOr!(isPOD, hasToHash), __Types))
    /++
    +/
    size_t toHash() const
    {
        static if (allSatisfy!(isPOD, __Types))
        {
            static if (__Types.length == 0 || is(__Types == AliasSeq!(typeof(null))))
            {
                return 0;
            }
            else
            static if (this.sizeof <= 16)
            {
                return hashOf(__bytes, __type);
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

                static immutable UInt[__Types.length + 1] sizes = [0, staticMap!(Sizeof, __Types)];
                return hashOf(__bytes[0 .. sizes[__type]], __type);
            }
        }
        else
        switch (__type)
        {
            static foreach (i, T; __Types)
            {
                case i:
                    return hashOf(__trustedGet!T, i);
            }
            default: assert(0);
        }
    }

    static if (allSatisfy!(isEqualityComparable, __Types))
    /++
    +/
    auto opEquals()(auto ref const typeof(this) rhs) const
    {
        static if (__Types.length == 0)
        {
            return true;
        }
        else
        {
            if (this.__type != rhs.__type)
                return false;
            switch (__type)
            {
                static foreach (i, T; __Types)
                {
                    case i:
                        return this.__trustedGet!T == rhs.__trustedGet!T;
                }
                default: assert(0);
            }
        }
    }

    static if (allSatisfy!(isOrderingComparable, __Types))
    /++
    +/
    auto opCmp()(auto ref const typeof(this) rhs) const
    {
        static if (__Types.length == 0)
        {
            return 0;
        }
        else
        {
            if (auto d = int(this.__type) - int(rhs.__type))
                return d;
            switch (__type)
            {
                static foreach (i, T; __Types)
                {
                    case i:
                        static if (__traits(hasMember, T, "opCmp"))
                            return this.__trustedGet!T.opCmp(rhs.__trustedGet!T);
                        else
                            return this.__trustedGet!T < rhs.__trustedGet!T ? -1 :
                                this.__trustedGet!T > rhs.__trustedGet!T ? +1 : 0;
                }
                default: assert(0);
            }
        }
    }

    ///
    void toString(C, W)(scope ref W w)
    {
        static if (__Types.length == 0)
        {
            return w.put(cast(immutable C[])"Algebraic");
        }
        else
        {
            import mir.format: print;
            switch (__type)
            {
                static foreach (i, T; __Types)
                {
                    case i:
                        print(w, __trustedGet!T);
                }
                default: assert(0);
            }
        }
    }
}

/++
Variant Type (aka Algebraic Type) with clever member access.

Compatible with BetterC mode.
+/
alias Variant(T...) = Algebraic!(0, TypeSet!T);

/++
Nullable variant Type (aka Algebraic Type) with clever member access.

Compatible with BetterC mode.
+/
alias Nullable(T...) = Variant!(typeof(null), T);

// example from std.variant
/**
$(H4 Self-Referential Types)
A useful and popular use of algebraic data structures is for defining
$(LUCKY self-referential data structures), i.e. structures that embed references to
values of their own type within.
This is achieved with $(LREF Variant) by using $(LREF This) as a placeholder whenever a
reference to the type being defined is needed. The $(LREF Variant) instantiation
will perform $(LINK2 https://en.wikipedia.org/wiki/Name_resolution_(programming_languages)#Alpha_renaming_to_make_name_resolution_trivial,
alpha renaming) on its constituent types, replacing $(LREF This)
with the self-referenced type. The structure of the type involving $(LREF This) may
be arbitrarily complex.
*/
@safe pure unittest
{
    import std.typecons : Tuple, tuple;

    // A tree is either a leaf or a branch of two other trees
    alias Tree(Leaf) = Variant!(Leaf, Tuple!(This*, This*));
    alias Leafs = Tuple!(Tree!int*, Tree!int*);

    Tree!int tree = tuple(new Tree!int(42), new Tree!int(43));
    Tree!int* right = tree.get!Leafs[1];
    assert(*right == 43);
}

///ditto
@safe pure unittest
{
    // An object is a double, a string, or a hash of objects
    alias Obj = Variant!(double, string, This[string]);
    alias Map = Obj[string];

    Obj obj = "hello";
    assert(obj.get!string == "hello");
    obj = 42.0;
    assert(obj.get!double == 42);
    obj = ["customer": Obj("John"), "paid": Obj(23.95)];
    assert(obj.get!Map["customer"] == "John");
}

/// Test for opCmp, opEqual, toHash
// version(mir_test)
version(none)
@safe pure @nogc nothrow
unittest
{
    import core.stdc.string: memcmp;

    static struct C(ubyte payloadSize, bool isPOD, bool hasToHash = true, bool hasOpEquals = true)
    {
        ubyte[payloadSize] __payload;

    const:

        static if (!isPOD)
        {
            this(this) {}
            ~this() {}
        }

    @safe pure nothrow @nogc:


    static if (hasToHash)
        size_t toHash() { return hashOf(__payload); }

    static if (hasOpEquals)
        auto opEquals(ref const typeof(this) rhs) @trusted { return memcmp(__payload.ptr, rhs.__payload.ptr, __payload.length); }
        auto opCmp(ref const typeof(this) rhs) { return __payload == rhs.__payload; }
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
        static assert (__traits(compiles, T.init == T.init) == isPOD || hasOpEquals);
        static assert (__traits(compiles, T.init <= T.init));
    }}
}

/// const propogation
@safe pure nothrow @nogc
unittest
{
    static struct S { immutable(ubyte)* value; }
    static struct C { immutable(uint)* value; }

    alias V = Variant!(S, C);
    const V v = S();
    V w = v;
    w = v;

    immutable f = V(S());
    auto t = immutable V(S());
    // auto j = immutable V(t);
    // auto i = const V(t);
}

/// ditto
@safe pure nothrow @nogc
unittest
{
    static struct S {
        uint* value;
        this(return ref scope const typeof(this) rhs) {}
        void opAssign(return ref scope const typeof(this) rhs) {}
    }
    static struct C { const(uint)* value; }

    alias V = Variant!(S, C);
    const V v = S();
    V w = v;
    w = S();
    w = cast(const) V.init;
    w = v;

    const f = V(S());
    auto t = const V(f);
}


@safe pure nothrow @nogc
unittest
{
    static struct S {
        uint* value;
        this(return ref scope typeof(this) rhs) {}
        this(return ref scope const typeof(this) rhs) const {}
        this(return ref scope immutable typeof(this) rhs) immutable {}
    }
    static struct C { immutable(uint)* value; }

    S s;
    S r = s;
    r = s;
    r = S.init;

    alias V = Variant!(S, C);
    V v = S();
    V w = v;
    w = S();
    w = V.init;
    w = v;

    immutable V e = S();
    auto t = immutable V(S());
    auto j = const V(t);
    auto h = t;

    immutable V l = C();
    auto g = immutable V(C());
}

@safe pure nothrow @nogc
unittest
{
    static struct S {
        uint* value;
        this(return ref scope typeof(this) rhs) {}
        this(return ref scope const typeof(this) rhs) const {}
        this(return ref scope const typeof(this) rhs) immutable {}
    }
    static struct C { immutable(uint)* value; }

    S s;
    S r = s;
    r = s;
    r = S.init;

    alias V = Variant!(S, C);
    V v = S();
    V w = v;
    w = S();
    w = V.init;
    w = v;

    {
        const V e = S();
        const k = w;
        auto t = const V(k);
        auto j = immutable V(k);
    }

    immutable V e = S();
    immutable k = w;
    auto t = immutable V(S());
    auto j = const V(t);
    auto h = t;

    immutable V l = C();
    import core.lifetime;
    auto g = immutable V(C());
    immutable b = immutable V(s);
}

@safe pure nothrow @nogc
unittest
{
    import core.lifetime: move;

    static struct S {
        immutable(uint)* value;
        this(return ref scope typeof(this) rhs) {}
        this(return ref scope const typeof(this) rhs) immutable {}
    }
    static struct C { immutable(uint)* value; }

    S s;
    S r = s;
    r = s;
    r = S.init;

    alias V = Variant!(S, C);
    V v = S();
    V w = v;
    w = S();
    w = V.init;
    w = v;

    immutable V e = S();
    immutable f = V(S());
    immutable k = w;
    auto t = immutable V(S());
    auto j = const V(t);
    auto h = t;

    immutable V l = C();
    import core.lifetime;
    immutable n = w.move;
    auto g = immutable V(C());
    immutable b = immutable V(s);
}

@safe pure nothrow @nogc
unittest
{
    static struct S {
        uint* value;
        this(this) @safe pure nothrow @nogc {}
        // void opAssign(typeof(this) rhs) {}
    }
    static struct C { const(uint)* value; }

    S s;
    S r = s;
    r = s;
    r = S.init;

    alias V = Variant!(S, C);
    V v = S();
    V w = v;
    w = S();
    w = V.init;
    w = v;
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
    Nullable!int a = 5;
    assert(a.get!int == 5);
    a.nullify;
    assert(a.isNull);
    a = 4;
    assert(!a.isNull);
    assert(a.get == 4);
    assert(a == 4);
    a = 4;
    a = null;
    assert(a == null);
}

/// ditto
@safe pure @nogc
unittest
{
    alias Number = Nullable!(int, double);

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
    assert(xx.match!((ref v) => v) == 23);

    x = null;
    y.nullify;

    assert(x.isNull);
    assert(y.isNull);
    assert(z.isNull);
    assert(z == y);
}

// Type with copy constructor
@safe pure nothrow @nogc unittest 
{
    static struct S
    {
        int n;
        this(ref return scope inout S rhs) inout
        {
            this.n = rhs.n + 1;
        }
    }

    Variant!S a = S();
    auto b = a;

    assert(a.get!S.n == 0);
    assert(b.get!S.n == 1);
}

// Empty type set
@safe pure nothrow @nogc unittest 
{
    Variant!() a;
    auto b = a;
    assert(a.toHash == 0);
    assert(a == b);
    assert(a <= b && b >= a);
    static assert(typeof(a).sizeof == 1);
}

// Empty nullable type set
@safe pure nothrow @nogc unittest 
{
    Nullable!() a;
    auto b = a;
    assert(a.toHash == 0);
    assert(a == b);
    assert(a <= b && b >= a);
    static assert(typeof(a).sizeof == 1);
}

// Small types
@safe pure nothrow @nogc unittest 
{
    struct S { ubyte d; }
    static assert(Nullable!(byte, char, S).sizeof == 2);
}

// Alignment
@safe pure nothrow @nogc unittest 
{
    struct S { ubyte[3] d; }
    static assert(Nullable!(ushort, wchar, S).sizeof == 4);
}

// opPostMove support
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import std.algorithm.mutation: move;

    static struct S
    {
        uint s;

        void opPostMove(const ref S old) nothrow
        {
            this.s = old.s + 1;
        }
    }

    Variant!S a;

    auto b = a.move;
    assert(b.get!S.s == 1);
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

// AliasSeq!(ReplaceTypeUnless!(isVariant, This, typeof(this), __Types))

private template VariantReturnTypes(T...)
{
    import std.meta: NoDuplicates, staticMap;

    alias VariantReturnTypes = NoDuplicates!(staticMap!(TryRemoveConst, T));
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
        if (isVariant!V)
    {
        import core.lifetime: forward;

        // template VariantReturnTypesImpl(T)
        // {
        //     static if (__traits(compiles, visitor(variant.__trustedGet!T, forward!args)))
        //     {
        //         alias Ret = typeof(visitor(variant.__trustedGet!T, forward!args));
        //         static if (is(Ret == void))
        //             alias VariantReturnTypesImpl = AliasSeq!(typeof(null));
        //         else
        //             alias VariantReturnTypesImpl = AliasSeq!(TryRemoveConst!Ret);
        //     }
        //     else
        //     {
        //         alias VariantReturnTypesImpl = AliasSeq!();
        //     }
        // }

        // alias AllReturnTypes = NoDuplicates!(staticMap!(VariantReturnTypesImpl, V.__Types));

        // static if (AllReturnTypes.length == 0 || is(AllReturnTypes == AliasSeq!(typeof(null))))
        // {
        //     alias ThisReturnType = void;
        // }
        // else
        // static if (AllReturnTypes.length == 2 && (is(AllReturnTypes[0] == typeof(null)) || is(AllReturnTypes[1] == typeof(null))))
        // {
        //     alias ThisReturnType = Variant!(typeof(null), OtherType);
        // }

        // template VariantReturnTypesImpl(T)
        // {
        //     import std.traits: Unqual, CopyTypeQualifiers;
        //     import std.meta: AliasSeq;

        //     static if (__traits(compiles, visitor(variant.__trustedGet!T, forward!args)))
        //     {
        //         alias Ret = typeof(visitor(variant.__trustedGet!T, forward!args));
        //         static if (is(Ret == void))
        //             alias VariantReturnTypesImpl = AliasSeq!(typeof(null));
        //         else
        //         static if (is(Unqual!Ret == Variant!InnerTypes, InnerTypes))
        //         {
        //             alias CopyTypeQualifiers1(Y) = CopyTypeQualifiers(Ret, Y);
        //             alias VariantReturnTypesImpl = staticMap!(CopyTypeQualifiers1, Ret.Types);
        //         }
        //         else
        //             alias VariantReturnTypesImpl = AliasSeq!Ret;
        //     }
        //     else
        //     {
        //         alias VariantReturnTypesImpl = AliasSeq!();
        //     }
        // }

        // import std.meta: staticMap;
        // alias Types = VariantReturnTypes!(staticMap!(VariantReturnTypesImpl, V.__Types));

        // V.__Types;
        switch (variant.__type)
        {
            static foreach (i, T; V.__Types)
            {
                case i:
                    static if (__traits(compiles, visitor(variant.__trustedGet!T, forward!args)))
                        return visitor(variant.__trustedGet!T, forward!args);
                    else
                    static if (exhaustive && !is(T == typeof(null)))
                        static assert(0, V.stringof ~ ": the visitor cann't be caled with __type (first argument) " ~ T.stringof ~ " and additional arguments " ~ Args.stringof);
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
        if (isVariant!V)
    {
        import core.lifetime: forward;
        switch (variant.__type)
        {
            static foreach (i, T; V.__Types)
            static if (__traits(compiles, result = visitor(variant.__trustedGet!T, forward!args)))
            {
                case i:
                    result = visitor(variant.__trustedGet!T, forward!args);
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
