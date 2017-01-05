module mir.conv;

import std.range.primitives;
import std.traits;
import std.meta;
public import std.ascii : LetterCase;


package template convFormat()
{
    import std.format : format;
    alias convFormat = format;
}

/* ************* Exceptions *************** */

/**
 * Thrown on conversion errors.
 */
class ConvException : Exception
{
    @safe pure nothrow
    this(string s, string fn = __FILE__, size_t ln = __LINE__)
    {
        super(s, fn, ln);
    }
}

private string convError_unexpected(S)(S source)
{
    return source.empty ? "end of input" : text("'", source.front, "'");
}

private auto convError(S, T)(S source, string fn = __FILE__, size_t ln = __LINE__)
{
    return new ConvException(
        text("Unexpected ", convError_unexpected(source),
             " when converting from type "~S.stringof~" to type "~T.stringof),
        fn, ln);
}

private auto convError(S, T)(S source, int radix, string fn = __FILE__, size_t ln = __LINE__)
{
    return new ConvException(
        text("Unexpected ", convError_unexpected(source),
             " when converting from type "~S.stringof~" base ", radix,
             " to type "~T.stringof),
        fn, ln);
}



/**
The `to` template converts a value from one type _to another.
The source type is deduced and the target type must be specified, for example the
expression `to!int(42.0)` converts the number 42 from
`double` _to `int`. The conversion is "unsafe", i.e.,
it does check for overflow.
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
