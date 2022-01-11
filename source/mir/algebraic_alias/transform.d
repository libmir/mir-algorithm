/++
$(H1 Transformation utilities for JSON-like values)

See_also: JSON libraries $(MIR_PACKAGE mir-ion) and $(MIR_PACKAGE asdf);

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko 
Macros:
+/
module mir.algebraic_alias.transform;

import mir.algebraic: Algebraic, tryVisit, visit, optionalVisit;
import mir.functional: naryFun;
private alias AliasSeq(T...) = T;

/++
Transforms algebraics leafs recursively in place,
ensuring that all leaf types are handled by the visiting functions.

Recursion is done for `This[]`, `StringMap!This`, `This[string]`, and `Annotated!This` types.
+/
alias transformLeafs(visitors...) = transformLeafsImpl!(visit, naryFun!visitors);

///
unittest
{
    import mir.format: text;
    import mir.algebraic_alias.json;
    JsonAlgebraic value = ["key" : ["str".JsonAlgebraic, 2.32.JsonAlgebraic, null.JsonAlgebraic].JsonAlgebraic];
 
    // converts all leavs to a text form
    value.transformLeafs!text;
    assert(value == ["key" : ["str".JsonAlgebraic, "2.32".JsonAlgebraic, "null".JsonAlgebraic].JsonAlgebraic].JsonAlgebraic);
    
    value = ["key" : ["str".JsonAlgebraic, 2.32.JsonAlgebraic, true.JsonAlgebraic].JsonAlgebraic].JsonAlgebraic;

    /// converts only bool values
    value.transformLeafs!(
        (bool b) => b.text,
        v => v, // other values are copied as is
    );

    assert(value == ["key" : ["str".JsonAlgebraic, 2.32.JsonAlgebraic, "true".JsonAlgebraic].JsonAlgebraic].JsonAlgebraic);
}

/++
Behaves as $(LREF transformLeafs) but doesn't enforce at compile time that all types can be handled by the visiting functions.

Throws: Exception if `naryFun!visitors` can't be called with provided arguments
+/
alias tryTransformLeafs(visitors...) = transformLeafsImpl!(tryVisit, naryFun!visitors);

///
unittest
{
    import mir.format: text;
    import mir.algebraic_alias.json;
    JsonAlgebraic value = ["key" : [true.JsonAlgebraic, 100.JsonAlgebraic, 2.32.JsonAlgebraic].JsonAlgebraic];
 
    // converts long and double numbers to a text form, bool values is converted to `long`
    value.tryTransformLeafs!((double v) => v.text, (long v) => v.text);
    assert(value == ["key" : ["1".JsonAlgebraic, "100".JsonAlgebraic, "2.32".JsonAlgebraic].JsonAlgebraic].JsonAlgebraic);
}

/++
Behaves as $(LREF transformLeafs) but doesn't enforce at compile time that all types can be handled by the visiting functions.

The function ignores leafs that can't be handled by the visiting functions.
+/
alias optionalTransformLeafs(visitors...) = transformLeafsImpl!(optionalVisit, naryFun!visitors);

///
unittest
{
    import mir.format: text;
    import mir.algebraic_alias.json;
    JsonAlgebraic value = ["key" : [null.JsonAlgebraic, true.JsonAlgebraic, 100.JsonAlgebraic, 2.32.JsonAlgebraic].JsonAlgebraic];
 
    // converts long numbers to a text form, ignores other types
    value.optionalTransformLeafs!(
        (long v) => v.text,
        (bool b) => b, // needs special overload for bool to get rid of implicit converion to long/double
    );
    assert(value == ["key" : [null.JsonAlgebraic, true.JsonAlgebraic, "100".JsonAlgebraic, 2.32.JsonAlgebraic].JsonAlgebraic].JsonAlgebraic);
}

///
template transformLeafsImpl(alias handler, alias visitor)
{
    ///
    ref Algebraic!Types transformLeafsImpl(Types...)(ref return Algebraic!Types value)
    {
        import core.lifetime: move;
        import mir.algebraic: visit;
        import mir.annotated: Annotated;
        import mir.string_map: StringMap;
        alias T = Algebraic!Types;
        static if (is(T.AllowedTypes[0] == typeof(null)))
        {
            enum nullCompiles = __traits(compiles, value = visitor(null));
            static if (nullCompiles || __traits(isSame, handler, visit))
            {
                alias nullHandler = (typeof(null)) {
                    static if (nullCompiles)
                        value = visitor(null);
                    else
                        assert(0, "Null " ~ T.stringof);
                };
            }
            else
            {
                alias nullHandler = AliasSeq!();
            }
        }
        else
        {
            alias nullHandler = AliasSeq!();
        }
        handler!(
            (T[] v) {
                foreach (ref e; v)
                   transformLeafsImpl(e);
            },
            (StringMap!T v) {
                foreach (ref e; v.values)
                   transformLeafsImpl(e);
            },
            (T[string] v) {
                foreach (key, ref e; v)
                   transformLeafsImpl(e);
            },
            (Annotated!T v) {
                transformLeafsImpl(v.value);
            },
            nullHandler,
            (ref v) { // auto for typeof(null) support
                static if (__traits(compiles, value = visitor(move(v))))
                    value = visitor(move(v));
                else
                    value = visitor(v);
            }
        )(value);
        return value;
    }

    /// ditto
    Algebraic!Types transformLeafsImpl(Types...)(Algebraic!Types value)
    {
        import core.lifetime: move;
        transformLeafsImpl(value);
        return move(value);
    }
}
