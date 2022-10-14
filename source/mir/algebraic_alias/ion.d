/++
$(H1 Mutable Ion value)

This module contains a single alias definition and doesn't provide Ion serialization API.

See_also: Ion library $(MIR_PACKAGE mir-ion)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilia Ki 
Macros:
+/
module mir.algebraic_alias.ion;

import mir.algebraic: Algebraic, This;
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
union Ion_
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
    Annotated!This annotated;
}

/++
Ion tagged algebraic alias.

The example below shows only the basic features. Advanced API to work with algebraic types can be found at $(GMREF mir-core, mir,algebraic).
See also $(MREF mir,string_map) - ordered string-value associative array.
+/
alias IonAlgebraic = Algebraic!Ion_;

///
@safe pure
version(mir_test)
unittest
{
    import mir.test: should;
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
    // access
    assert(value.boolean == true);
    assert(value.get!bool == true);
    assert(value.get!"boolean" == true);
    assert(value.get!(IonAlgebraic.Kind.boolean) == true);
    // nothrow access
    assert(value.trustedGet!bool == true);
    assert(value.trustedGet!"boolean" == true);
    assert(value.trustedGet!(IonAlgebraic.Kind.boolean) == true);
    // checks
    assert(!value._is!string);
    assert(value._is!bool);
    assert(value._is!"boolean");
    assert(value._is!(IonAlgebraic.Kind.boolean));

    // Null
    value = object["null"] = null;
    assert(value.isNull);
    assert(value == null);
    assert(value.kind == IonAlgebraic.Kind.null_);
    // access
    assert(value.null_ == null);
    assert(value.get!(typeof(null)) == null);
    assert(value.get!(IonAlgebraic.Kind.null_) == null);

    // String
    value = object["string"] = "s";
    assert(value.kind == IonAlgebraic.Kind.string);
    assert(value == "s");
    // access
    // Yep, `string` here is an alias to `get!(immutable(char)[])` method
    assert(value.string == "s");
    // `string` here is an alias of type `immutable(char)[]`
    assert(value.get!string == "s");
    assert(value.get!"string" == "s");
    // finally, `string` here is an enum meber
    assert(value.get!(IonAlgebraic.Kind.string) == "s");

    // Integer
    value = object["integer"] = 4;
    assert(value.kind == IonAlgebraic.Kind.integer);
    assert(value == 4);
    assert(value != 4.0);
    assert(value.integer == 4);

    // Float
    value = object["float"] = 3.0;
    assert(value.kind == IonAlgebraic.Kind.float_);
    assert(value != 3);
    assert(value == 3.0);
    assert(value.float_ == 3.0);

    // Array
    IonAlgebraic[] arr = [0, 1, 2, 3, 4].map!IonAlgebraic.array;

    value = object["array"] = arr;
    assert(value.kind == IonAlgebraic.Kind.array);
    assert(value == arr);
    assert(value == [0, 1, 2, 3, 4].map!IonAlgebraic.array);// by value
    assert(value.array[3] == 3);

    // Object
    assert(object.keys == ["bool", "null", "string", "integer", "float", "array"]);
    object.values[0] = "false";
    assert(object["bool"] == "false"); // it is a string now
    object.remove("bool"); // remove the member

    value = object["array"] = object;
    assert(value.kind == IonAlgebraic.Kind.object);
    assert(value.object.keys is object.keys);

    IonAlgebraic[string] aa = object.toAA;
    object = aa.StringMap!IonAlgebraic;

    IonAlgebraic fromAA = ["a" : IonAlgebraic(3), "b" : IonAlgebraic("b")];
    assert(fromAA.object["a"] == 3);
    assert(fromAA.object["b"] == "b");

    // object foreach iteration
    long sum;
    foreach (ref key, ref val; fromAA.object)
        if (key == "a")
            sum += val.get!long;
    sum.should == 3;

    // annotations
    auto annotated = Annotated!IonAlgebraic(["birthday"], Timestamp("2001-01-01"));
    value = annotated;
    assert(value == annotated);
    value = annotated.IonAlgebraic;
    assert(value == annotated);
}
