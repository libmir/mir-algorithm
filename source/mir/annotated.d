/++
$(H1 Annotated value)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko 
Macros:
+/
module mir.annotated;

import mir.serde: serdeRegister, serdeAnnotation;

static immutable excMsg = "At least one annotation is required to create an annotated value.";
version (D_Exceptions)
    static immutable exc = new Exception(excMsg);

/++
A convenience difintion of an annotated value. 
+/
@serdeRegister
@serdeAnnotation
struct Annotated(T) {
    ///
    @serdeAnnotation
    string[] annotations;
    static if (is(T == union) || is(T == struct))
    {
        ///
        private T* _value;
        ///
        ref inout(T) value() inout @property
        {
            return *_value;
        }
    }
    else
    {
        ///
        T value;
    }

    ///
    alias value this;

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
        static if (is(T == union) || is(T == struct))
            this._value = new T(forward!args);
        else
        static if (__traits(compiles, value = args))
            this.value = args;
        else
            this.value = new T(forward!args);
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
