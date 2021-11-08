/++
$(H1 Annotated value)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko 
Macros:
+/
module mir.annotated;

import mir.serde: serdeRegister, serdeAnnotation, serdeIsDynamicAlgebraic;

static immutable excMsg = "At least one annotation is required to create an annotated value.";
version (D_Exceptions)
    static immutable exc = new Exception(excMsg);

/++
A convenience difinition of an annotated value. 
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
    static if (serdeIsDynamicAlgebraic!T)
        private enum _alloc_ = true;
    else
    {
        import mir.algebraic: isVariant;
        static if (isVariant!T)
            private enum _alloc_ = true;
        else
            private enum _alloc_ = false;
    }

    static if (_alloc_)
    {
        ///
        private T* _value_;
        ///
        ref inout(T) _value() inout @property
        {
            return *_value_;
        }

        ///
        ref T _value(T value) @property
        {
            if (_value_ is null)
            {
                _value_ = new T;
                import core.lifetime: move;
                *_value_ = move(value);
            }
            return *_value_;
        }

        ///
        bool opEquals(const Annotated rhs) const
        {
            return annotations == rhs.annotations && _value == rhs._value;
        }
    }
    else
    {
        ///
        T _value;
    }

    ///
    alias _value this;

    /++
    Params:
        annotations = non-empty array of annotations
        value = actual value
    +/
    this(Args...)(string[] annotations, Args args) @safe pure {
        if (annotations.length == 0)
        {
            version (D_Exceptions)
                throw exc;
            else
                assert(0, excMsg);
        }
        import core.lifetime: forward;
        this.annotations = annotations;
        static if (_alloc_)
            this._value_ = new T(forward!args);
        else
        static if (__traits(compiles, value = args))
            this._value = args;
        else
        static if (is(T == class))
            this._value = new T(forward!args);
        else
            this._value = T(forward!args);
    }
}

///
unittest
{
    auto annotations = ["annotation"];
    static struct S {double x;}
    auto as = Annotated!S(annotations, 5);
    assert(as.annotations == annotations);
    assert(as.x == 5);

    static struct C {double x;}
    auto ac = Annotated!S(annotations, 5);
    assert(ac.annotations == annotations);
    assert(ac.x == 5);
}

///
unittest
{
    import mir.algebraic;
    auto annotations = ["annotation"];
    static struct S {double x;}
    auto as = Annotated!(Variant!S)(annotations, 5);
    assert(as.annotations == annotations);
    assert(as.x == 5);

    static struct C {double x;}
    auto ac = Annotated!(Variant!S)(annotations, 5);
    assert(ac.annotations == annotations);
    assert(ac.x == 5);
}
