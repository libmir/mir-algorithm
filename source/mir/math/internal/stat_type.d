/++ Internal result-type selection shared by statistical and product algorithms.
License: Apache-2.0
Authors: Shigeki Karita, Ilia Ki, John Michael Hall
Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
+/
module mir.math.internal.stat_type;

import std.traits: Unqual;

///
package(mir)
template statType(T, bool checkComplex = true)
{
    import mir.internal.utility: isFloatingPoint;

    static if (isFloatingPoint!T) {
        import std.traits: Unqual;
        alias statType = Unqual!T;
    } else static if (is(T : double)) {
        alias statType = double;
    } else static if (checkComplex) {
        import mir.internal.utility: isComplex;
        static if (isComplex!T) {
            static if (__traits(getAliasThis, T).length == 1)
            {
                alias statType = .statType!(typeof(__traits(getMember, T, __traits(getAliasThis, T)[0])));
            }
            else
            {
                alias statType = Unqual!T;
            }
        } else {
            static assert(0, "statType: type " ~ T.stringof ~ " must be convertible to a complex floating point type");
        }
    } else {
        static assert(0, "statType: type " ~ T.stringof ~ " must be convertible to a floating point type");
    }
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static assert(is(statType!int == double));
    static assert(is(statType!uint == double));
    static assert(is(statType!double == double));
    static assert(is(statType!float == float));
    static assert(is(statType!real == real));

    static assert(is(statType!(const(int)) == double));
    static assert(is(statType!(immutable(int)) == double));
    static assert(is(statType!(const(double)) == double));
    static assert(is(statType!(immutable(double)) == double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex: Complex;

    static assert(is(statType!(Complex!float) == Complex!float));
    static assert(is(statType!(Complex!double) == Complex!double));
    static assert(is(statType!(Complex!real) == Complex!real));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        float x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not float
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        Complex!float x;
        alias x this;
    }

    static assert(is(statType!Foo == Complex!float));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        double x;
        alias x this;
    }

    static assert(is(statType!Foo == double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        Complex!double x;
        alias x this;
    }

    static assert(is(statType!Foo == Complex!double));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        real x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not real
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.complex;
    static struct Foo {
        Complex!real x;
        alias x this;
    }

    static assert(is(statType!Foo == Complex!real));
}

version(mir_test)
@safe pure nothrow @nogc
unittest
{
    static struct Foo {
        int x;
        alias x this;
    }

    static assert(is(statType!Foo == double)); // note: this is not ints
}
