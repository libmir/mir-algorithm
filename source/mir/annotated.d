/++
$(H1 Annotated value)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilia Ki 
Macros:
+/
module mir.annotated;

import mir.internal.meta: basicElementType;
import mir.algebraic: isVariant;
import mir.serde: serdeRegister, serdeAnnotation, serdeIsDynamicAlgebraic;

static immutable excMsg = "At least one annotation is required to create an annotated value.";
version (D_Exceptions)
    static immutable exc = new Exception(excMsg);

/++
A convenience definition of an annotated value.

A structure that behaves like a recursive algebraic type should define `enum _serdeRecursiveAlgebraic;` member.
+/
@serdeRegister
@serdeAnnotation
struct Annotated(T) {
    ///
    @serdeAnnotation
    string[] annotations;

    static if (!(is(T == union) || is(T == struct)))
        private enum _alloc_ = false;
    else
    static if (__traits(hasMember, T, "_serdeRecursiveAlgebraic"))
        private enum _alloc_ = true;
    else
    {
        static if (isVariant!T)
            private enum _alloc_ = true;
        else
            private enum _alloc_ = false;
    }

    static if (_alloc_)
    {
        ///
        private T* _value;
        ///
        ref inout(T) value() inout @property
            in(_value)
        {
            return *_value;
        }

        ///
        ref T value(T value) @property return scope
        {
            if (_value is null)
            {
                _value = new T;
                import core.lifetime: move;
                *_value = move(value);
            }
            return *_value;
        }

        // Algebraic equality already promises these attributes. State them here
        // to break recursive attribute inference through annotated alternatives.
        static if (isVariant!T)
        {
            ///
            bool opEquals(scope const Annotated rhs) scope const pure nothrow @nogc
            {
                return annotations == rhs.annotations && value == rhs.value;
            }
        }
        else
        {
            /// ditto
            bool opEquals(scope const Annotated rhs) scope const
            {
                return annotations == rhs.annotations && value == rhs.value;
            }
        }

        size_t toHash() scope @trusted const pure nothrow @nogc
        {
            static if (__traits(compiles, hashOf(value)))
                return hashOf(value);
            else
            {
                debug pragma(msg, "Mir warning: can't compute hash. Expexted `size_t toHash() scope @safe const pure nothrow @nogc` method for " ~ T.stringof);
                return cast(size_t)_value;
            }
        }
    }
    else
    {
        ///
        T value;
    }


    /++
    Params:
        annotations = non-empty array of annotations
        args = arguments to construct value with
    +/
    this(Args...)(string[] annotations, Args args) @safe pure {
        if (annotations.length == 0)
        {
            version (D_Exceptions)
                { import mir.exception : toMutable; throw exc.toMutable; }
            else
                assert(0, excMsg);
        }
        import core.lifetime: forward;
        this.annotations = annotations;
        static if (_alloc_)
            this._value = new T(forward!args);
        else
        static if (__traits(compiles, value = args))
            this.value = args;
        else
        static if (is(T == class))
            this.value = new T(forward!args);
        else
            this.value = T(forward!args);
    }

    // private alias E = .basicElementType!T;

    import std.traits: isAssociativeArray, isAggregateType;
    ///
    int opCmp()(scope const typeof(this) rhs) scope const pure nothrow @nogc @system
        // if (!isAssociativeArray!E && (!isAggregateType!E || __traits(hasMember, E, "opCmp")))
    {
        if (auto d = __cmp(annotations, rhs.annotations))
            return d;

        static if (__traits(compiles, __cmp(value, rhs.value)))
            return __cmp(value, rhs.value);
        else
        static if (__traits(hasMember, value, "opCmp") && !is(T[i] == U*, U))
            return value.opCmp(rhs.value);
        else
            return value < rhs.value ? -1 : value > rhs.value ? +1 : 0;
    }
}

///
version(mir_test)
unittest
{
    auto annotations = ["annotation"];
    static struct S {double x;}
    auto as = Annotated!S(annotations, 5);
    assert(as.annotations == annotations);
    assert(as.value.x == 5);

    static struct C {double x;}
    auto ac = Annotated!S(annotations, 5);
    assert(ac.annotations == annotations);
    assert(ac.value.x == 5);
}

///
version(mir_test)
unittest
{
    import mir.algebraic;
    auto annotations = ["annotation"];
    static struct S {double x;}
    auto as = Annotated!(Variant!S)(annotations, 5);
    assert(as.annotations == annotations);
    assert(as.value.x == 5);

    static struct C {double x;}
    auto ac = Annotated!(Variant!S)(annotations, 5);
    assert(ac.annotations == annotations);
    assert(ac.value.x == 5);
}

/++
A convenience definition of an annotated value.

A structure that behaves like a recursive algebraic type should define `enum _serdeRecursiveAlgebraic;` member.
+/
@serdeRegister
@serdeAnnotation
struct AnnotatedOnce(T) {
    ///
    @serdeAnnotation
    string annotation;

    static if (!(is(T == union) || is(T == struct)))
        private enum _alloc_ = false;
    else
    static if (__traits(hasMember, T, "_serdeRecursiveAlgebraic"))
        private enum _alloc_ = true;
    else
    {
        static if (isVariant!T)
            private enum _alloc_ = true;
        else
            private enum _alloc_ = false;
    }

    static if (_alloc_)
    {
        ///
        private T* _value;
        ///
        ref inout(T) value() inout @property
        {
            return *_value;
        }

        ///
        ref T value(T value) @property
        {
            if (_value is null)
            {
                _value = new T;
                import core.lifetime: move;
                *_value = move(value);
            }
            return *_value;
        }

        // Algebraic equality already promises these attributes. State them here
        // to break recursive attribute inference through annotated alternatives.
        static if (isVariant!T)
        {
            ///
            bool opEquals(scope const AnnotatedOnce rhs) scope const pure nothrow @nogc
            {
                return annotation == rhs.annotation && value == rhs.value;
            }
        }
        else
        {
            /// ditto
            bool opEquals(scope const AnnotatedOnce rhs) scope const
            {
                return annotation == rhs.annotation && value == rhs.value;
            }
        }
    }
    else
    {
        ///
        T value;
    }


    /++
    Params:
        annotation = non-empty array of annotation
        args = arguments to construct value with
    +/
    this(Args...)(string annotation, Args args) @safe pure {
        import core.lifetime: forward;
        this.annotation = annotation;
        static if (_alloc_)
            this._value = new T(forward!args);
        else
        static if (__traits(compiles, value = args))
            this.value = args;
        else
        static if (is(T == class))
            this.value = new T(forward!args);
        else
            this.value = T(forward!args);
    }

    // private alias E = .basicElementType!T;

    import std.traits: isAssociativeArray, isAggregateType;
    // static if (!isAssociativeArray!E && (!isAggregateType!E || __traits(hasMember, E, "opCmp")))
    ///
    int opCmp()(scope const typeof(this) rhs) scope const @system pure nothrow @nogc
    {
        if (auto d = __cmp(annotation, rhs.annotation))
            return d;

        static if (__traits(compiles, __cmp(value, rhs.value)))
            return __cmp(value, rhs.value);
        else
        static if (__traits(hasMember, value, "opCmp") && !is(T[i] == U*, U))
            return value.opCmp(rhs.value);
        else
            return value < rhs.value ? -1 : value > rhs.value ? +1 : 0;
    }
}

///
version(mir_test)
unittest
{
    auto annotation = "annotation";
    static struct S {double x;}
    auto as = AnnotatedOnce!S(annotation, 5);
    assert(as.annotation == annotation);
    assert(as.value.x == 5);

    static struct C {double x;}
    auto ac = AnnotatedOnce!S(annotation, 5);
    assert(ac.annotation == annotation);
    assert(ac.value.x == 5);
}

///
version(mir_test)
unittest
{
    import mir.algebraic;
    auto annotation = "annotation";
    static struct S {double x;}
    auto as = AnnotatedOnce!(Variant!S)(annotation, 5);
    assert(as.annotation == annotation);
    assert(as.value.x == 5);

    static struct C {double x;}
    auto ac = AnnotatedOnce!(Variant!S)(annotation, 5);
    assert(ac.annotation == annotation);
    assert(ac.value.x == 5);
}

// Equality must not acquire attributes that the wrapped value cannot satisfy.
unittest
{
    static struct Effectful
    {
        enum _serdeRecursiveAlgebraic = true;
        int payload;
        static int comparisons;

        bool opEquals(scope const Effectful rhs) const
        {
            ++comparisons;
            auto copy = new int(payload);
            if (payload < 0)
                throw new Exception("negative payload");
            return *copy == rhs.payload;
        }
    }
    static foreach (once; [false, true])
    {{
        static if (once)
            alias W = AnnotatedOnce!Effectful;
        else
            alias W = Annotated!Effectful;
        static assert(!__traits(compiles, () pure { W a, b; return a == b; }));
        static assert(!__traits(compiles, () nothrow { W a, b; return a == b; }));
        static assert(!__traits(compiles, () @nogc { W a, b; return a == b; }));
        W a, b;
        a.value = Effectful(1);
        b.value = Effectful(1);
        auto before = Effectful.comparisons;
        assert(a == b);
        assert(Effectful.comparisons > before);
    }}
}
