module mir.conv;

import std.traits;

/**
The `to` template converts a value from one type _to another.
The source type is deduced and the target type must be specified, for example the
expression `to!int(42.0)` converts the number 42 from
`double` _to `int`. The conversion is "unsafe", i.e.,
it does not check for overflow.
 */
template to(T)
{
    auto ref T to(A...)(auto ref A args)
        if (A.length > 0)
    {
        static if (A.length == 1 && isImplicitlyConvertible!(A[0], T))
            return args[0];
        else
        static if (is(T == class) && is(typeof(new T(args))))
            return new T(args);
        else
        static if (is(typeof(T(args))))
            return T(args);
        else
        static if (A.length == 1)
            return cast(T) args[0];
        else
            static assert(0);
    }
}
