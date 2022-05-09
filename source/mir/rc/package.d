/++
$(H1 Thread-safe reference-counted arrays and pointers)

Mir provides two kinds of ref-counting pointers and two kinds of ref-counted arrays.

The first kind pointer is `RCPtr`, which consists of a pointer to the context and pointer to the value.`RCPtr` supports structural and object polymorphism. It allows getting members with the same context as the root.
The second kind is `SlimRCPtr`, which consist only from a pointer to the value. The context for `SlimRCPtr`is computed using a fixed-length memory shift from the pointer to the value.
`SlimRCPtr` can be converted to an `RCPtr` and to an `RCArray` of the one element.

`RCArray` is an array type without range primitives. It's length can't be reduced after construction.In the other hand, `Slice!(RCI!(T))` is an ndslice with all random-access range primitives.`RCI` is an iterator, which consists of `RCArray` and the pointer to the current element.
`RCArray!T` can be converted or moved to `Slice!(RCI!(T))` using `.asSlice` or `.moveToSlice` methods respectively.

$(RED `RCArray!T` aliases itself to a common D array slice. This feature may cause a segmentation fault in safe code if used without DIP1000.)

`RCPtr!T` can be constructed from an element index and `RCArray!T` / `Slice!(RCI!(T))`.

The package publicly imports $(MREF mir,rc,array), $(MREF mir,rc,ptr), and $(MREF mir,rc,slim_ptr).

See_also: $(MREF mir,ndslice).
+/
module mir.rc;

///
public import mir.rc.array;
///
public import mir.rc.ptr;
///
public import mir.rc.slim_ptr;

import mir.ndslice.slice;

/++
Returns: shared pointer constructed from the slim shared pointer.

The function has zero computation cost.
+/
RCPtr!F toRCPtr(F)(return SlimRCPtr!F contextAndValue) @trusted
{
    typeof(return) ret;
    ret._value = contextAndValue._value;
    ret._context = &contextAndValue.context();
    contextAndValue._value = null;
    return ret;
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    import core.lifetime: move;
    struct S
    {
        double e;
    }
    struct C
    {
        int i;
        S s;
    }

    auto a = createSlimRC!C(10, S(3));
    auto s = a.move.toRCPtr.shareMember!"s";
    assert(s._counter == 1);
    assert(s.e == 3);
}

/++
Returns: shared pointer constructed with the `array`'s context and the value points to `array[index]`.

The function has zero computation cost.
+/
RCPtr!F toRCPtrAt(F)(return RCArray!F array, size_t index) @trusted
    if (!is(R == class) && !is(R == interface))
in {
    assert(index < array.length, "toRCPtrAt: index should be less then array.length");
}
do {
    typeof(return) ret;
    ret._value = array._payload + index;
    ret._context = &array.context();
    array._payload = null;
    return ret;
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    struct S { double e; }

    auto a = RCArray!S(10);
    a[3].e = 4;

    auto s = a.toRCPtrAt(3);

    assert(s._counter == 2);
    assert(s.e == 4);
}

/// ditto
RCPtr!F toRCPtrAt(F)(return Slice!(RCI!F) array, size_t index) @trusted
    if (!is(R == class) && !is(R == interface))
in {
    assert(index < array.length, "toRCPtrAt: index should be less then array.length");
}
do {
    typeof(return) ret;
    ret._value = array._iterator._iterator + index;
    ret._context = &array._iterator._array.context();
    array._iterator._array._payload = null;
    return ret;
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    struct S { double e; }

    auto a = RCArray!S(10).asSlice[5 .. $];
    a[3].e = 4;

    auto s = a.toRCPtrAt(3);

    assert(s._counter == 2);
    assert(s.e == 4);
}

/++
Returns: RC array length of one constructed from the slim shared pointer.

The function has zero computation cost.
+/
RCArray!F toRCArray(F)(return SlimRCPtr!F context) @trusted
{
    typeof(return) ret;
    ret._payload = context._value;
    context._value = null;
    return ret;
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest
{
    struct S { double e; }

    auto a = createSlimRC!S(4).toRCArray;
    assert(a._counter == 1);
    assert(a.length == 1);
    assert(a[0].e == 4);
}
