/++
$(H1 Mutable JSON value)

This module contains a single alias definition and doesn't provide JSON serialization API.

See_also: JSON libraries $(MIR_PACKAGE mir-ion) and $(MIR_PACKAGE asdf);

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilia Ki 
Macros:
+/
module mir.algebraic_alias.json;

import mir.algebraic: Algebraic, This;
///
public import mir.string_map: StringMap;

/++
Definition union for $(LREF JsonAlgebraic).
+/
union Json_
{
    ///
    typeof(null) null_;
    ///
    bool boolean;
    ///
    long integer;
    ///
    double float_;
    ///
    immutable(char)[] string;
    /// Self alias in array.
    This[] array;
    /// Self alias in $(MREF mir,string_map).
    StringMap!This object;
}

/++
JSON tagged algebraic alias.

The example below shows only the basic features. Advanced API to work with algebraic types can be found at $(GMREF mir-core, mir,algebraic).
See also $(MREF mir,string_map) - ordered string-value associative array.
+/
alias JsonAlgebraic = Algebraic!Json_;

///
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.topology: map;
    import mir.array.allocation: array;

    JsonAlgebraic value;

    StringMap!JsonAlgebraic object;

    // Default
    assert(value.isNull);
    assert(value.kind == JsonAlgebraic.Kind.null_);

    // Boolean
    value = object["bool"] = true;
    assert(!value.isNull);
    assert(value == true);
    assert(value.kind == JsonAlgebraic.Kind.boolean);
    // access
    assert(value.boolean == true);
    assert(value.get!bool == true);
    assert(value.get!"boolean" == true);
    assert(value.get!(JsonAlgebraic.Kind.boolean) == true);
    // nothrow access
    assert(value.trustedGet!bool == true);
    assert(value.trustedGet!"boolean" == true);
    assert(value.trustedGet!(JsonAlgebraic.Kind.boolean) == true);
    // checks
    assert(!value._is!string);
    assert(value._is!bool);
    assert(value._is!"boolean");
    assert(value._is!(JsonAlgebraic.Kind.boolean));

    // Null
    value = object["null"] = null;
    assert(value.isNull);
    assert(value == null);
    assert(value.kind == JsonAlgebraic.Kind.null_);
    // access
    assert(value.null_ == null);
    assert(value.get!(typeof(null)) == null);
    assert(value.get!(JsonAlgebraic.Kind.null_) == null);

    // String
    value = object["string"] = "s";
    assert(value.kind == JsonAlgebraic.Kind.string);
    assert(value == "s");
    // access
    // Yep, `string` here is an alias to `get!(immutable(char)[])` method
    assert(value.string == "s");
    // `string` here is an alias of type `immutable(char)[]`
    assert(value.get!string == "s");
    assert(value.get!"string" == "s");
    // finally, `string` here is an enum meber
    assert(value.get!(JsonAlgebraic.Kind.string) == "s");

    // Integer
    value = object["integer"] = 4;
    assert(value.kind == JsonAlgebraic.Kind.integer);
    assert(value == 4);
    assert(value != 4.0);
    assert(value.integer == 4);

    // Float
    value = object["float"] = 3.0;
    assert(value.kind == JsonAlgebraic.Kind.float_);
    assert(value != 3);
    assert(value == 3.0);
    assert(value.float_ == 3.0);

    // Array
    JsonAlgebraic[] arr = [0, 1, 2, 3, 4].map!JsonAlgebraic.array;

    value = object["array"] = arr;
    assert(value.kind == JsonAlgebraic.Kind.array);
    assert(value == arr);
    assert(value.array[3] == 3);

    // Object
    assert(object.keys == ["bool", "null", "string", "integer", "float", "array"]);
    object.values[0] = "false";
    assert(object["bool"] == "false"); // it is a string now
    object.remove("bool"); // remove the member

    value = object["array"] = object;
    assert(value.kind == JsonAlgebraic.Kind.object);
    assert(value.object.keys is object.keys);

    JsonAlgebraic[string] aa = object.toAA;
    object = aa.StringMap!JsonAlgebraic;

    JsonAlgebraic fromAA = ["a" : JsonAlgebraic(3), "b" : JsonAlgebraic("b")];
    assert(fromAA.object["a"] == 3);
    assert(fromAA.object["b"] == "b");
}
