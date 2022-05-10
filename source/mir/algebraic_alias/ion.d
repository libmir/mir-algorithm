/++
$(H1 Mutable Ion value)

This module contains a single alias definition and doesn't provide Ion serialization API.

See_also: Ion library $(MIR_PACKAGE mir-ion)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko 
Macros:
+/
module mir.algebraic_alias.ion;

import mir.algebraic: TaggedVariant, This;
///
public import mir.annotated: Annotated;
///
public import mir.lob: Clob, Blob;
///
public import mir.string_map: StringMap;
///
public import mir.timestamp: Timestamp;


/++
Definition union for $(LREF IonAlgebraic).
+/
union IonAlgebraicUnion
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
    ///
    Blob blob;
    ///
    Clob clob;
    ///
    Timestamp timestamp;
    /// Self alias in array.
    This[] array;
    /// Self alias in $(MREF mir,string_map).
    StringMap!This object;
    /// Self alias in $(MREF mir,annotated).
    Annotated!This annotations;
}

/++
Ion tagged algebraic alias.

The example below shows only the basic features. Advanced API to work with algebraic types can be found at $(GMREF mir-core, mir,algebraic).
See also $(MREF mir,string_map) - ordered string-value associative array.
+/
alias IonAlgebraic = TaggedVariant!IonAlgebraicUnion;

///
unittest
{
    import mir.ndslice.topology: map;
    import mir.array.allocation: array;

    IonAlgebraic value;

    StringMap!IonAlgebraic object;

    // Default
    assert(value.isNull);
    assert(value.kind == IonAlgebraic.Kind.null_);

    // Boolean
    value = object["bool"] = true;
    assert(!value.isNull);
    assert(value == true);
    assert(value.kind == IonAlgebraic.Kind.boolean);
    assert(value.get!bool == true);
    assert(value.get!(IonAlgebraic.Kind.boolean) == true);

    // Null
    value = object["null"] = null;
    assert(value.isNull);
    assert(value == null);
    assert(value.kind == IonAlgebraic.Kind.null_);
    assert(value.get!(typeof(null)) == null);
    assert(value.get!(IonAlgebraic.Kind.null_) == null);

    // String
    value = object["string"] = "s";
    assert(value.kind == IonAlgebraic.Kind.string);
    assert(value == "s");
    assert(value.get!string == "s");
    assert(value.get!(IonAlgebraic.Kind.string) == "s");

    // Integer
    value = object["integer"] = 4;
    assert(value.kind == IonAlgebraic.Kind.integer);
    assert(value == 4);
    assert(value != 4.0);
    assert(value.get!long == 4);
    assert(value.get!(IonAlgebraic.Kind.integer) == 4);

    // Float
    value = object["float"] = 3.0;
    assert(value.kind == IonAlgebraic.Kind.float_);
    assert(value != 3);
    assert(value == 3.0);
    assert(value.get!double == 3.0);
    assert(value.get!(IonAlgebraic.Kind.float_) == 3.0);

    // Array
    IonAlgebraic[] arr = [0, 1, 2, 3, 4].map!IonAlgebraic.array;

    value = object["array"] = arr;
    assert(value.kind == IonAlgebraic.Kind.array);
    assert(value == arr);
    assert(value.get!(IonAlgebraic[])[3] == 3);

    // Object
    assert(object.keys == ["bool", "null", "string", "integer", "float", "array"]);
    object.values[0] = "false";
    assert(object["bool"] == "false"); // it is a string now
    object.remove("bool"); // remove the member

    value = object["array"] = object;
    assert(value.kind == IonAlgebraic.Kind.object);
    assert(value.get!(StringMap!IonAlgebraic).keys is object.keys);
    assert(value.get!(StringMap!IonAlgebraic).values is object.values);

    IonAlgebraic[string] aa = object.toAA;
    object = StringMap!IonAlgebraic(aa);

    IonAlgebraic fromAA = ["a" : IonAlgebraic(3), "b" : IonAlgebraic("b")];
    assert(fromAA.get!(StringMap!IonAlgebraic)["a"] == 3);
    assert(fromAA.get!(StringMap!IonAlgebraic)["b"] == "b");

    auto annotated = Annotated!IonAlgebraic(["birthday"], Timestamp("2001-01-01"));
    value = annotated;
    assert(value == annotated);
    value = annotated.IonAlgebraic;
    assert(value == annotated);
}
