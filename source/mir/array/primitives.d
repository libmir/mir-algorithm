/++
Range primitives for arrays with multi-dimensional like API support.

Note:
UTF strings behaves like common arrays in Mir.
`std.uni.byCodePoint` can be used to create a range of characters.

See_also: $(MREF mir,_primitives).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
+/
module mir.array.primitives;

import std.traits;
import mir.math.common: optmath;

pragma(inline, true) @optmath:

///
bool empty(size_t dim = 0, T)(in T[] ar)
    if (!dim)
{
    return !ar.length;
}

///
version(mir_test)
unittest
{
   assert((int[]).init.empty);
   assert(![1].empty!0); // Slice-like API
}

///
ref front(size_t dim = 0, T)(T[] ar)
    if (!dim && !is(Unqual!T[] == void[]))
{
    assert(ar.length, "Accessing front of an empty array.");
    return ar[0];
}

///
version(mir_test)
unittest
{
   assert(*&[3, 4].front == 3); // access be ref
   assert([3, 4].front!0 == 3); // Slice-like API
}


///
ref back(size_t dim = 0, T)(T[] ar)
    if (!dim && !is(Unqual!T[] == void[]))
{
    assert(ar.length, "Accessing back of an empty array.");
    return ar[$ - 1];
}

///
version(mir_test)
unittest
{
   assert(*&[3, 4].back == 4); // access be ref
   assert([3, 4].back!0 == 4); // Slice-like API
}

///
void popFront(size_t dim = 0, T)(ref T[] ar)
    if (!dim && !is(Unqual!T[] == void[]))
{
    assert(ar.length, "Evaluating popFront() on an empty array.");
    ar = ar[1 .. $];
}

///
version(mir_test)
unittest
{
    auto ar = [3, 4];
    ar.popFront;
    assert(ar == [4]);
    ar.popFront!0;  // Slice-like API
    assert(ar == []);
}

///
void popBack(size_t dim = 0, T)(ref T[] ar)
    if (!dim && !is(Unqual!T[] == void[]))
{
    assert(ar.length, "Evaluating popBack() on an empty array.");
    ar = ar[0 .. $ - 1];
}

///
version(mir_test)
unittest
{
    auto ar = [3, 4];
    ar.popBack;
    assert(ar == [3]);
    ar.popBack!0;  // Slice-like API
    assert(ar == []);
}

///
size_t popFrontN(size_t dim = 0, T)(ref T[] ar, size_t n)
    if (!dim && !is(Unqual!T[] == void[]))
{
    n = ar.length < n ? ar.length : n;
    ar = ar[n .. $];
    return n;
}

///
version(mir_test)
unittest
{
    auto ar = [3, 4];
    ar.popFrontN(1);
    assert(ar == [4]);
    ar.popFrontN!0(10);  // Slice-like API
    assert(ar == []);
}

///
size_t popBackN(size_t dim = 0, T)(ref T[] ar, size_t n)
    if (!dim && !is(Unqual!T[] == void[]))
{
    n = ar.length < n ? ar.length : n;
    ar = ar[0 .. $ - n];
    return n;
}

///
version(mir_test)
unittest
{
    auto ar = [3, 4];
    ar.popBackN(1);
    assert(ar == [3]);
    ar.popBackN!0(10);  // Slice-like API
    assert(ar == []);
}

///
void popFrontExactly(size_t dim = 0, T)(ref T[] ar, size_t n)
    if (!dim && !is(Unqual!T[] == void[]))
{
    assert(ar.length >= n, "Evaluating *.popFrontExactly(n) on an array with length less then n.");
    ar = ar[n .. $];
}

///
version(mir_test)
unittest
{
    auto ar = [3, 4, 5];
    ar.popFrontExactly(2);
    assert(ar == [5]);
    ar.popFrontExactly!0(1);  // Slice-like API
    assert(ar == []);
}

///
void popBackExactly(size_t dim = 0, T)(ref T[] ar, size_t n)
    if (!dim && !is(Unqual!T[] == void[]))
{
    assert(ar.length >= n, "Evaluating *.popBackExactly(n) on an array with length less then n.");
    ar = ar[0 .. $ - n];
}

///
version(mir_test)
unittest
{
    auto ar = [3, 4, 5];
    ar.popBackExactly(2);
    assert(ar == [3]);
    ar.popBackExactly!0(1);  // Slice-like API
    assert(ar == []);
}

///
size_t length(size_t d : 0, T)(in T[] array)
    if (d == 0)
{
    pragma(inline, true);
    return array.length;
}

///
version(mir_test)
unittest
{
    assert([1, 2].length!0 == 2);
}

///
alias elementCount = length;

deprecated("use elementCount instead")
alias elementsCount = elementCount;

