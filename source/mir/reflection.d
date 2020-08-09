/++
+/
module mir.reflection;

import std.meta;
import std.traits: getUDAs, Parameters, isSomeFunction, FunctionAttribute, functionAttributes;

/++
Returns: single UDA.
+/
template getUDA(alias symbol, alias attribute)
{
    private alias all = getUDAs!(symbol, attribute);
    static if (all.length != 1)
        static assert(0, "Exactly one " ~ attribute.stringof ~ " attribute is required");
    else
    {
        static if (is(typeof(all[0])))
            enum getUDA = all[0];
        else
            alias getUDA = all[0];
    }
}

/++
Checks if member is field.
+/
enum bool isField(T, string member) = __traits(compiles, (ref T aggregate) { return __traits(getMember, aggregate, member).offsetof; });


///
version(mir_test)
unittest
{
    struct D
    {
        int gi;
    }

    struct I
    {
        int f;

        D base;
        alias base this;

        void gi(double ) @property {}
        void gi(uint ) @property {}
    }

    struct S
    {
        int d;

        I i;
        alias i this;

        int gm() @property {return 0;}
        int gc() const @property {return 0;}
        void gs(int) @property {}
    }

    static assert(!isField!(S, "gi"));
    static assert(!isField!(S, "gs"));
    static assert(!isField!(S, "gc"));
    static assert(!isField!(S, "gm"));
    static assert(!isField!(S, "gi"));
    static assert(isField!(S, "d"));
    static assert(isField!(S, "f"));
    static assert(isField!(S, "i"));
}

///  with classes
version(mir_test)
unittest
{
    class I
    {
        int f;

        void gi(double ) @property {}
        void gi(uint ) @property {}
    }

    class S
    {
        int d;

        I i;
        alias i this;

        int gm() @property {return 0;}
        int gc() const @property {return 0;}
        void gs(int) @property {}
    }

    static assert(!isField!(S, "gi"));
    static assert(!isField!(S, "gs"));
    static assert(!isField!(S, "gc"));
    static assert(!isField!(S, "gm"));
    static assert(isField!(S, "d"));
    static assert(isField!(S, "f"));
    static assert(isField!(S, "i"));
}

/++
Checks if member is property.
+/
template isProperty(T, string member)
{
    T aggregate;

    static if (__traits(compiles, isSomeFunction!(__traits(getMember, aggregate, member))))
    {
        static if (isSomeFunction!(__traits(getMember, aggregate, member)))
        {
            enum bool isProperty = isPropertyImpl!(__traits(getMember, aggregate, member));
        }
        else
        {
            enum bool isProperty = false;
        }
    }
    else
        enum bool isProperty = false;
}

///
version(mir_test)
unittest
{
    struct D
    {
        int y;

        void gf(double ) @property {}
        void gf(uint ) @property {}
    }

    struct I
    {
        int f;

        D base;
        alias base this;

        void gi(double ) @property {}
        void gi(uint ) @property {}
    }

    struct S
    {
        int d;

        I i;
        alias i this;

        int gm() @property {return 0;}
        int gc() const @property {return 0;}
        void gs(int) @property {}
    }

    static assert(isProperty!(S, "gf"));
    static assert(isProperty!(S, "gi"));
    static assert(isProperty!(S, "gs"));
    static assert(isProperty!(S, "gc"));
    static assert(isProperty!(S, "gm"));
    static assert(!isProperty!(S, "d"));
    static assert(!isProperty!(S, "f"));
    static assert(!isProperty!(S, "y"));
}

/++
Returns: list of the setter properties.

Note: The implementation ignores templates.
+/
template getSetters(T, string member)
{
    alias getSetters = Filter!(hasSingleArgument, Filter!(isPropertyImpl, __traits(getOverloads, T, member)));
}

///
version(mir_test)
unittest
{
    struct I
    {
        int f;

        void gi(double ) @property {}
        void gi(uint ) @property {}
    }

    struct S
    {
        int d;

        I i;
        alias i this;

        int gm() @property {return 0;}
        int gc() const @property {return 0;}
        void gs(int) @property {}
    }

    static assert(getSetters!(S, "gi").length == 2);
    static assert(getSetters!(S, "gs").length == 1);
    static assert(getSetters!(S, "gc").length == 0);
    static assert(getSetters!(S, "gm").length == 0);
    static assert(getSetters!(S, "d").length == 0);
    static assert(getSetters!(S, "f").length == 0);
}

/++
Returns: list of the serializable (public getters) members.
+/
enum string[] SerializableMembers(T) = [Filter!(ApplyLeft!(Serializable, T), FieldsAndProperties!T)];

///
version(mir_test)
unittest
{
    struct D
    {
        int y;

        int gf() @property {return 0;}
    }

    struct I
    {
        int f;

        D base;
        alias base this;

        int gi() @property {return 0;}
    }

    struct S
    {
        int d;

        package int p;

        int gm() @property {return 0;}

        private int q;

        I i;
        alias i this;

        int gc() const @property {return 0;}
        void gs(int) @property {}
    }

    static assert(SerializableMembers!S == ["y", "gf", "f", "gi", "d", "gm", "gc"]);
    static assert(SerializableMembers!(const S) == ["y", "f", "d", "gc"]);
}

/++
Returns: list of the deserializable (public setters) members.
+/
enum string[] DeserializableMembers(T) = [Filter!(ApplyLeft!(Deserializable, T), FieldsAndProperties!T)];

///
version(mir_test)
unittest
{
    struct I
    {
        int f;
        void ga(int) @property {}
    }

    struct S
    {
        int d;
        package int p;

        int gm() @property {return 0;}
        void gm(int) @property {}

        private int q;

        I i;
        alias i this;


        void gc(int, int) @property {}
        void gc(int) @property {}
    }

    S s;
    // s.gc(0);

    static assert (DeserializableMembers!S == ["f", "ga", "d", "gm", "gc"]);
    static assert (DeserializableMembers!(const S) == []);
}

// This trait defines what members should be serialized -
// public members that are either readable and writable or getter properties
private template Serializable(T, string member)
{
    static if (!isPublic!(T, member))
        enum Serializable = false;
    else
        enum Serializable = isReadable!(T, member); // any readable is good
}

private enum bool hasSingleArgument(alias fun) = Parameters!fun.length == 1;
private enum bool hasZeroArguments(alias fun) = Parameters!fun.length == 0;

// This trait defines what members should be serialized -
// public members that are either readable and writable or setter properties
private template Deserializable(T, string member)
{
    static if (!isPublic!(T, member))
        enum Deserializable = false;
    else
    static if (isReadableAndWritable!(T, member))
        enum Deserializable = true;
    else
    static if (getSetters!(T, member).length == 1)
        enum Deserializable =  is(typeof((ref T val){ __traits(getMember, val, member) = Parameters!(getSetters!(T, member)[0])[0].init; }));
    else
        enum Deserializable = false;
}

private enum FieldsAndProperties(T) = Reverse!(NoDuplicates!(Reverse!(FieldsAndPropertiesImpl!T)));

private template FieldsAndPropertiesImpl(T)
{
    alias isProperty = ApplyLeft!(.isProperty, T);
    alias isField = ApplyLeft!(.isField, T);
    static if (__traits(getAliasThis, T).length)
    {
        T aggregate;
        alias baseMembers = FieldsAndPropertiesImpl!(typeof(__traits(getMember, aggregate, __traits(getAliasThis, T))));
        alias members = Erase!(__traits(getAliasThis, T)[0], __traits(allMembers, T));
        alias FieldsAndPropertiesImpl = AliasSeq!(baseMembers, Filter!(isField, members), Filter!(isProperty, members));
        
    }
    else
    {
        alias members = __traits(allMembers, T);
        alias FieldsAndPropertiesImpl = AliasSeq!(Filter!(isField, members), Filter!(isProperty, members));
    }
}

// check if the member is readable
private template isReadable(T, string member)
{
    T aggregate;
    enum bool isReadable = __traits(compiles, { static fun(T)(auto ref T t) {} fun(__traits(getMember, aggregate, member)); });
}

// check if the member is readable/writeble?
private template isReadableAndWritable(T, string member)
{
    T aggregate;
    enum bool isReadableAndWritable = __traits(compiles, __traits(getMember, aggregate, member) = __traits(getMember, aggregate, member));
}

private template isPublic(T, string member)
{
    T aggregate;
    enum bool isPublic = !__traits(getProtection, __traits(getMember, aggregate, member)).privateOrPackage;
}

// check if the member is property
private template isSetter(T, string member)
{
    T aggregate;
    static if (__traits(compiles, isSomeFunction!(__traits(getMember, aggregate, member))))
    {
        static if (isSomeFunction!(__traits(getMember, aggregate, member)))
        {
            enum bool isSetter = getSetters!(T, member).length > 0;;
        }
        else
        {
            enum bool isSetter = false;
        }
    }
    else
        enum bool isSetter = false;
}

private template isGetter(T, string member)
{
    T aggregate;
    static if (__traits(compiles, isSomeFunction!(__traits(getMember, aggregate, member))))
    {
        static if (isSomeFunction!(__traits(getMember, aggregate, member)))
        {
            enum bool isGetter = Filter!(hasZeroArguments, Filter!(isPropertyImpl, __traits(getOverloads, T, member))).length == 1;
        }
        else
        {
            enum bool isGetter = false;
        }
    }
    else
        enum bool isGetter = false;
}

private enum bool isPropertyImpl(alias member) = (functionAttributes!member & FunctionAttribute.property) != 0;

private bool privateOrPackage()(string protection)
{
    return protection == "private" || protection == "package";
}
