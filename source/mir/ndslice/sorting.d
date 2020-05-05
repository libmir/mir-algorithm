/++
This is a submodule of $(MREF mir,ndslice).

Note:
    The combination of
    $(SUBREF topology, pairwise) with lambda `"a <= b"` (`"a < b"`) and $(SUBREF algorithm, all) can be used
    to check if an ndslice is sorted (strictly monotonic).
    $(SUBREF topology iota) can be used to make an index.
    $(SUBREF topology map) and $(SUBREF topology zip) can be used to create Schwartzian transform.
    See also the examples in the module.


See_also: $(SUBREF topology, flattened)

`isSorted` and `isStrictlyMonotonic`

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Andrei Alexandrescu 2008-2016, Ilya Yaroshenko 2016-, 
Authors:   Andrei Alexandrescu (Phobos), Ilya Yaroshenko (API, rework, Mir adoptation)

Macros:
    SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
+/
module mir.ndslice.sorting;

/// Check if ndslice is sorted, or strictly monotonic.
@safe pure version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.sorting: sort;
    import mir.ndslice.topology: pairwise;

    auto arr = [1, 1, 2].sliced;

    assert(arr.pairwise!"a <= b".all);
    assert(!arr.pairwise!"a < b".all);

    arr = [4, 3, 2, 1].sliced;

    assert(!arr.pairwise!"a <= b".all);
    assert(!arr.pairwise!"a < b".all);

    sort(arr);

    assert(arr.pairwise!"a <= b".all);
    assert(arr.pairwise!"a < b".all);
}

/// Create index
version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.sorting: sort;
    import mir.ndslice.topology: iota, pairwise;

    auto arr = [4, 2, 3, 1].sliced;

    auto index = arr.length.iota.slice;
    index.sort!((a, b) => arr[a] < arr[b]);

    assert(arr[index].pairwise!"a <= b".all);
}

/// Schwartzian transform
version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.sorting: sort;
    import mir.ndslice.topology: zip, map, pairwise;

    alias transform = (a) => (a - 3) ^^ 2;

    auto arr = [4, 2, 3, 1].sliced;

    arr.map!transform.slice.zip(arr).sort!((l, r) => l.a < r.a);

    assert(arr.map!transform.pairwise!"a <= b".all);
}

import mir.ndslice.slice;
import mir.math.common: optmath;

@optmath:

@safe pure version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.topology: pairwise;

    auto a = [1, 2, 3].sliced;
    assert(a[0 .. 0].pairwise!"a <= b".all);
    assert(a[0 .. 1].pairwise!"a <= b".all);
    assert(a.pairwise!"a <= b".all);
    auto b = [1, 3, 2].sliced;
    assert(!b.pairwise!"a <= b".all);

    // ignores duplicates
    auto c = [1, 1, 2].sliced;
    assert(c.pairwise!"a <= b".all);
}

@safe pure version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.topology: pairwise;

    assert([1, 2, 3][0 .. 0].sliced.pairwise!"a < b".all);
    assert([1, 2, 3][0 .. 1].sliced.pairwise!"a < b".all);
    assert([1, 2, 3].sliced.pairwise!"a < b".all);
    assert(![1, 3, 2].sliced.pairwise!"a < b".all);
    assert(![1, 1, 2].sliced.pairwise!"a < b".all);
}


/++
Sorts ndslice, array, or series.

See_also: $(SUBREF topology, flattened).
+/
template sort(alias less = "a < b")
{
    import mir.functional: naryFun;
    import mir.series: Series;
    static if (__traits(isSame, naryFun!less, less))
    {
@optmath:
        /++
        Sort n-dimensional slice.
        +/
        Slice!(Iterator, N, kind) sort(Iterator, size_t N, SliceKind kind)
            (Slice!(Iterator, N, kind) slice)
        {
            if (false) // break safety
            {
                import mir.utility : swapStars;
                auto elem = typeof(*slice._iterator).init;
                elem = elem;
                auto l = less(elem, elem);
            }
            import mir.ndslice.topology: flattened;
            if (slice.anyEmpty)
                return slice;
            .quickSortImpl!less(slice.flattened);
            return slice;
        }

        /++
        Sort for arrays
        +/
        T[] sort(T)(T[] ar)
        {
            return .sort!less(ar.sliced).field;
        }

        /++
        Sort for one-dimensional Series.
        +/
        Series!(IndexIterator, Iterator, N, kind)
            sort(IndexIterator, Iterator, size_t N, SliceKind kind)
            (Series!(IndexIterator, Iterator, N, kind) series)
        if (N == 1)
        {
            import mir.ndslice.sorting: sort;
            import mir.ndslice.topology: zip;
            with(series)
                index.zip(data).sort!((a, b) => less(a.a, b.a));
            return series;
        }

        /++
        Sort for n-dimensional Series.
        +/
        Series!(IndexIterator, Iterator, N, kind)
            sort(
                IndexIterator,
                Iterator,
                size_t N,
                SliceKind kind,
                SortIndexIterator,
                DataIterator,
                )
            (
                Series!(IndexIterator, Iterator, N, kind) series,
                Slice!SortIndexIterator indexBuffer,
                Slice!DataIterator dataBuffer,
            )
        {
            import mir.algorithm.iteration: each;
            import mir.ndslice.sorting: sort;
            import mir.ndslice.topology: iota, zip, ipack, evertPack;

            assert(indexBuffer.length == series.length);
            assert(dataBuffer.length == series.length);
            indexBuffer[] = indexBuffer.length.iota!(typeof(indexBuffer.front));
            series.index.zip(indexBuffer).sort!((a, b) => less(a.a, b.a));
            series.data.ipack!1.evertPack.each!((sl){
            {
                assert(sl.shape == dataBuffer.shape);
                dataBuffer[] = sl[indexBuffer];
                sl[] = dataBuffer;
            }});
            return series;
        }
    }
    else
        alias sort = .sort!(naryFun!less);
}

///
@safe pure version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.slice;
    import mir.ndslice.sorting: sort;
    import mir.ndslice.topology: pairwise;

    int[10] arr = [7,1,3,2,9,0,5,4,8,6];

    auto data = arr[].sliced(arr.length);
    data.sort();
    assert(data.pairwise!"a <= b".all);
}

/// one-dimensional series
pure version(mir_test) unittest
{
    import mir.series;

    auto index = [4, 2, 1, 3, 0].sliced;
    auto data = [5.6, 3.4, 2.1, 7.8, 0.1].sliced;
    auto series = index.series(data);
    series.sort;
    assert(series.index == [0, 1, 2, 3, 4]);
    assert(series.data == [0.1, 2.1, 3.4, 7.8, 5.6]);
    /// initial index and data are the same
    assert(index.iterator is series.index.iterator);
    assert(data.iterator is series.data.iterator);

    foreach(obs; series)
    {
        static assert(is(typeof(obs) == Observation!(int, double)));
    }
}

/// two-dimensional series
pure version(mir_test) unittest
{
    import mir.series;
    import mir.ndslice.allocation: uninitSlice;

    auto index = [4, 2, 3, 1].sliced;
    auto data =
        [2.1, 3.4, 
         5.6, 7.8,
         3.9, 9.0,
         4.0, 2.0].sliced(4, 2);
    auto series = index.series(data);

    series.sort(
        uninitSlice!size_t(series.length), // index buffer
        uninitSlice!double(series.length), // data buffer
        );

    assert(series.index == [1, 2, 3, 4]);
    assert(series.data ==
        [[4.0, 2.0],
         [5.6, 7.8],
         [3.9, 9.0],
         [2.1, 3.4]]);
    /// initial index and data are the same
    assert(index.iterator is series.index.iterator);
    assert(data.iterator is series.data.iterator);
}

void quickSortImpl(alias less, Iterator)(Slice!Iterator slice) @trusted
{
    import mir.utility : swap, swapStars;

    enum  max_depth = 64;
    enum naive_est = 1024 / slice.Element!0.sizeof;
    enum size_t naive = 32 > naive_est ? 32 : naive_est;
    //enum size_t naive = 1;
    static assert(naive >= 1);

    for(;;)
    {
        auto l = slice._iterator;
        auto r = l;
        r += slice.length;

        static if (naive > 1)
        {
            if (slice.length <= naive)
            {
                auto p = r;
                --p;
                while(p != l)
                {
                    --p;
                    //static if (is(typeof(() nothrow
                    //    {
                    //        auto t = slice[0]; if (less(t, slice[0])) slice[0] = slice[0];
                    //    })))
                    //{
                        auto d = p;
                        import mir.functional: unref;
                        auto temp = unref(*d);
                        auto c = d;
                        ++c;
                        if (less(*c, temp))
                        {
                            do
                            {
                                d[0] = *c;
                                ++d;
                                ++c;
                            }
                            while (c != r && less(*c, temp));
                            d[0] = temp;
                        }
                    //}
                    //else
                    //{
                    //    auto d = p;
                    //    auto c = d;
                    //    ++c;
                    //    while (less(*c, *d))
                    //    {
                    //        swap(*d, *c);
                    //        d = c;
                    //        ++c;
                    //        if (c == maxJ) break;
                    //    }
                    //}
                }
                return;
            }
        }
        else
        {
            if(slice.length <= 1)
                return;
        }

        // partition
        auto lessI = l;
        --r;
        auto pivotIdx = l + slice.length / 2;
        setPivot!less(slice.length, l, pivotIdx, r);
        import mir.functional: unref;
        auto pivot = unref(*pivotIdx);
        --lessI;
        auto greaterI = r;
        swapStars(pivotIdx, greaterI);

        outer: for (;;)
        {
            do ++lessI;
            while (less(*lessI, pivot));
            assert(lessI <= greaterI, "sort: invalid comparison function.");
            for (;;)
            {
                if (greaterI == lessI)
                    break outer;
                --greaterI;
                if (!less(pivot, *greaterI))
                    break;
            }
            assert(lessI <= greaterI, "sort: invalid comparison function.");
            if (lessI == greaterI)
                break;
            swapStars(lessI, greaterI);
        }

        swapStars(r, lessI);

        ptrdiff_t len = lessI - l;
        auto tail = slice[len + 1 .. $];
        slice = slice[0 .. len];
        if (tail.length > slice.length)
            swap(slice, tail);
        quickSortImpl!less(tail);
    }
}

void setPivot(alias less, Iterator)(size_t length, ref Iterator l, ref Iterator mid, ref Iterator r) @trusted
{
    if (length < 512)
    {
        if (length >= 32)
            medianOf!less(l, mid, r);
        return;
    }
    auto quarter = length >> 2;
    auto b = mid - quarter;
    auto e = mid + quarter;
    medianOf!less(l, e, mid, b, r);
}

void medianOf(alias less, Iterator)
    (ref Iterator a, ref Iterator b, ref Iterator c) @trusted
{
    import mir.utility : swapStars;
   if (less(*c, *a)) // c < a
    {
        if (less(*a, *b)) // c < a < b
        {
            swapStars(a, b);
            swapStars(a, c);
        }
        else // c < a, b <= a
        {
            swapStars(a, c);
            if (less(*b, *a)) swapStars(a, b);
        }
    }
    else // a <= c
    {
        if (less(*b, *a)) // b < a <= c
        {
            swapStars(a, b);
        }
        else // a <= c, a <= b
        {
            if (less(*c, *b)) swapStars(b, c);
        }
    }
    assert(!less(*b, *a));
    assert(!less(*c, *b));
}

void medianOf(alias less, Iterator)
    (ref Iterator a, ref Iterator b, ref Iterator c, ref Iterator d, ref Iterator e) @trusted
{
    import mir.utility : swapStars;   // Credit: Teppo Niinimäki
    version(unittest) scope(success)
    {
        assert(!less(*c, *a));
        assert(!less(*c, *b));
        assert(!less(*d, *c));
        assert(!less(*e, *c));
    }

    if (less(*c, *a)) swapStars(a, c);
    if (less(*d, *b)) swapStars(b, d);
    if (less(*d, *c))
    {
        swapStars(c, d);
        swapStars(a, b);
    }
    if (less(*e, *b)) swapStars(b, e);
    if (less(*e, *c))
    {
        swapStars(c, e);
        if (less(*c, *a)) swapStars(a, c);
    }
    else
    {
        if (less(*c, *b)) swapStars(b, c);
    }
}

/++
Returns: `true` if a sorted array contains the value.

Params:
    test = strict ordering symmetric predicate

For non-symmetric predicates please use a structure with two `opCall`s or an alias of two global functions,
that correponds to `(array[i], value)` and `(value, array[i])` cases.

See_also: $(LREF transitionIndex).
+/
template assumeSortedContains(alias test = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!test, test))
    {
@optmath:
        /++
        Params:
            slice = sorted one-dimensional slice or array.
            v = value to test with. It is passed to second argument.
        +/
        bool assumeSortedContains(Iterator, SliceKind kind, V)
            (auto ref Slice!(Iterator, 1, kind) slice, auto ref scope const V v)
        {
            auto ti = transitionIndex!test(slice, v);
            return ti < slice.length && !test(v, slice[ti]);
        }

        /// ditto
        bool assumeSortedContains(T, V)(scope T[] ar, auto ref scope const V v)
        {
            return .assumeSortedContains!test(ar.sliced, v);
        }
    }
    else
        alias assumeSortedContains = .assumeSortedContains!(naryFun!test);
}

/++
Returns: the smallest index of a sorted array such
    that the index corresponds to the arrays element at the index according to the predicate
    and `-1` if the array doesn't contain corresponding element.

Params:
    test = strict ordering symmetric predicate.

For non-symmetric predicates please use a structure with two `opCall`s or an alias of two global functions,
that correponds to `(array[i], value)` and `(value, array[i])` cases.

See_also: $(LREF transitionIndex).
+/
template assumeSortedEqualIndex(alias test = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!test, test))
    {
@optmath:
        /++
        Params:
            slice = sorted one-dimensional slice or array.
            v = value to test with. It is passed to second argument.
        +/
        sizediff_t assumeSortedEqualIndex(Iterator, SliceKind kind, V)
            (auto ref Slice!(Iterator, 1, kind) slice, auto ref scope const V v)
        {
            auto ti = transitionIndex!test(slice, v);
            return ti < slice.length && !test(v, slice[ti]) ? ti : -1;
        }

        /// ditto
        sizediff_t assumeSortedEqualIndex(T, V)(scope T[] ar, auto ref scope const V v)
        {
            return .assumeSortedEqualIndex!test(ar.sliced, v);
        }
    }
    else
        alias assumeSortedEqualIndex = .assumeSortedEqualIndex!(naryFun!test);
}

///
version(mir_test)
@safe pure unittest
{
    // sorted: a < b
    auto a = [0, 1, 2, 3, 4, 6];

    assert(a.assumeSortedEqualIndex(2) == 2);
    assert(a.assumeSortedEqualIndex(5) == -1);

    // <= non strict predicates doesn't work
    assert(a.assumeSortedEqualIndex!"a <= b"(2) == -1);
}

/++
Computes transition index using binary search.
It is low-level API for lower and upper bounds of a sorted array.

Params:
    test = ordering predicate for (`(array[i], value)`) pairs.

See_also: $(SUBREF topology, assumeSortedEqualIndex).
+/
template transitionIndex(alias test = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!test, test))
    {
@optmath:
        /++
        Params:
            slice = sorted one-dimensional slice or array.
            v = value to test with. It is passed to second argument.
        +/
        size_t transitionIndex(Iterator, SliceKind kind, V)
            (auto ref Slice!(Iterator, 1, kind) slice, auto ref scope const V v)
        {
            size_t first = 0, count = slice.length;
            while (count > 0)
            {
                immutable step = count / 2, it = first + step;
                if (test(slice[it], v))
                {
                    first = it + 1;
                    count -= step + 1;
                }
                else
                {
                    count = step;
                }
            }
            return first;
        }

        /// ditto
        size_t transitionIndex(T, V)(scope T[] ar, auto ref scope const V v)
        {
            return .transitionIndex!test(ar.sliced, v);
        }

    }
    else
        alias transitionIndex = .transitionIndex!(naryFun!test);
}

///
version(mir_test)
@safe pure unittest
{
    // sorted: a < b
    auto a = [0, 1, 2, 3, 4, 6];

    auto i = a.transitionIndex(2);
    assert(i == 2);
    auto lowerBound = a[0 .. i];

    auto j = a.transitionIndex!"a <= b"(2);
    assert(j == 3);
    auto upperBound = a[j .. $];

    assert(a.transitionIndex(a[$-1]) == a.length - 1);
    assert(a.transitionIndex!"a <= b"(a[$-1]) == a.length);
}

/++
Computes an index for `r` based on the comparison `less`. The
index is a sorted array of indices into the original
range. This technique is similar to sorting, but it is more flexible
because (1) it allows "sorting" of immutable collections, (2) allows
binary search even if the original collection does not offer random
access, (3) allows multiple indexes, each on a different predicate,
and (4) may be faster when dealing with large objects. However, using
an index may also be slower under certain circumstances due to the
extra indirection, and is always larger than a sorting-based solution
because it needs space for the index in addition to the original
collection. The complexity is the same as `sort`'s.
Params:
    less = The comparison to use.
    r = The slice/array to index.
Returns: Index slice/array.
+/
Slice!(I*) makeIndex(I = size_t, alias less = "a < b", Iterator, SliceKind kind)(Slice!(Iterator, 1, kind) r)
{
    import mir.functional: naryFun;
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;
    return r
        .length
        .iota!I
        .slice
        .sort!((a, b) => naryFun!less(r[a], r[b]));
}

///
I[] makeIndex(I = size_t, alias less = "a < b", T)(scope T[] r)
{
    return .makeIndex!(I, less)(r.sliced).field;
}

///
version(mir_test)
@system unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.topology: indexed, pairwise;

    immutable arr = [ 2, 3, 1, 5, 0 ];
    auto index = arr.makeIndex;

    assert(arr.indexed(index).pairwise!"a < b".all);
}

/++
Default function for topN

Params:
    slice = input 1-dimensional slice
+/
@trusted pure @nogc nothrow
template setPivotAt(alias less = "a < b") {
    size_t setPivotAt(Iterator, SliceKind kind)
        (Slice!(Iterator, 1, kind) slice)
    {
        size_t len = slice.length;
        
        assert(len > 0, "setPivotAt: slice must have a length greater than zero");

        auto leftI = slice._iterator;
        auto midI = leftI + len / 2;
        auto rightI = leftI + len - 1;

        setPivot!less(len, leftI, midI, rightI);
        return midI - leftI;
    }
}

///
version(mir_test)
@safe pure
unittest {
    import mir.functional: naryFun;
    auto x = [3, 1, 5, 2, 0].sliced;

    auto y = setPivotAt!(naryFun!("a < b"))(x);
    assert(y == 2);
    assert(x[0 + y] == 5);

    auto z = setPivotAt!(naryFun!("a < b"))(x[1 .. 3]);
    assert(z == 1);
    assert(x[1 + z] == 5);
}

/++
Reorders `slice` such that `slice[nth]` refers to the element that would fall
there if the range were fully sorted. In addition, it also partitions `slice`
such that all elements `e1` from `slice[0]` to `slice[nth]` satisfy
`!less(slice[nth], e1)`, and all elements `e2` from `slice[nth]` to
`slice[slice.length]` satisfy `!less(e2, slice[nth])`. Effectively, it finds
the `nth` smallest (according to `less`) elements in `slice`. Performs an
expected $(BIGOH slice.length) evaluations of `less` and `swap`, with a worst
case of $(BIGOH slice.length^^2).

This function implements an iterative, in-place version of the
$(HTTP en.wikipedia.org/wiki/Quickselect, quickselect) algorithm. It loops
through a slice, calling a user-provided `pivotFunction` (default
implementation: setPivotAt) to choose a pivot point. The `pivotFunction` must
conform to the following signatures:
------
    size_t value = pivotFunction!less(slice);
    size_t value = pivotFunction(slice);
------
It then partitions `slice` using `less` at the given pivot point and loops
through a slice of the original `slice`. It also includes specialization for
when `nth` equals zero or the length of `slice` minus one (to partition around
the smallest or largest element of a slice).

Params:
    less = The predicate to sort by.
    pivotFunction = The pivot strategy to use.
    slice = n-dimensional slice
    nth = The index of the element that should be in sorted position after the
        function is finished.
See_Also:
    $(LREF pivotPartition), $(LREF setPivotAt)

+/
template topN(alias less = "a < b", alias pivotFunction = setPivotAt)
{
    import mir.functional: naryFun;

    static if (__traits(isSame, naryFun!less, less))
    {
        /++
        Sort n-dimensional slice.
        +/
        void topN(Iterator, size_t N, SliceKind kind)
            (Slice!(Iterator, N, kind) slice, size_t nth)
        {
            assert(slice.elementCount > 0, "topN: slice must have elementCount greater than 0");
            assert(nth >= 0, "topN: nth must be greater than or equal to zero");
            assert(nth < slice.elementCount, "topN: nth must be less than the elementCount of the slice");
        
            import mir.ndslice.topology: flattened;

            topNImpl!(less, pivotFunction)(slice.flattened, nth);
        }
    } else {
        alias topN = .topN!(naryFun!less, pivotFunction);
    }
}

private @trusted
void topNImpl(alias less, alias pivotFunction, Iterator, SliceKind kind)(
        Slice!(Iterator, 1, kind) slice, size_t n) 
{
    import std.algorithm.sorting: pivotPartition;
    import mir.utility: swap;
    import mir.functional: reverseArgs;

    size_t pivot = void;
    size_t len = void;

    for (;;) {
        len = slice.length;

        if (len <= 1) {
            break;
        }

        if (n == 0) {
            pivot = 0;
            foreach (i; 1 .. len) {
                if (less(slice[i], slice[pivot])) {
                    pivot = i;
                }
            }
            swap(slice[n], slice[pivot]);
            break;
        }

        if (n + 1 == len) {
            pivot = 0;
            foreach (i; 1 .. len) {
                if (reverseArgs!less(slice[i], slice[pivot])) {
                    pivot = i;
                }
            }
            swap(slice[n], slice[pivot]);
            break;
        }

        static if (__traits(compiles, pivotFunction!less(slice)))
        {
            pivot = pivotFunction!(less)(slice);
        } else {
            static if (__traits(compiles, pivotFunction(slice))) {
                pivot = pivotFunction(slice);
            } else
                static assert(0, "topNImpl: pivotFunction does not compile");
        }

        assert(pivot >= 0, "topNImpl: pivotFunction must provide a value greater than zero");
        assert(pivot < len, "topNImpl: pivotFunction must provide a value less than the length of the slice");
        pivot = pivotPartition!less(slice, pivot);

        if (n < pivot) {
            slice = slice[0 .. pivot];
        } else if (n > pivot) {
            slice = slice[(pivot + 1) .. $];
            n -= pivot + 1;
        } else {
            break;
        }
    }
}

/// Partition 1-dimensional slice at nth
version(mir_test)
@safe pure
unittest {
    size_t nth = 2;
    auto x = [3, 1, 5, 2, 0].sliced;
    x.topN(nth);
    assert(x[nth] == 2);
}

/// Partition 2-dimensional slice
version(mir_test)
@safe pure
unittest {
    size_t nth = 4;
    auto x = [3, 1, 5, 2, 0, 7].sliced(3, 2);
    x.topN(nth);
    assert(x[2, 0] == 5);
}

/// Can supply alternate ordering function
version(mir_test)
@safe pure
unittest {
    size_t nth = 2;
    auto x = [3, 1, 5, 2, 0].sliced;
    x.topN!("a > b")(nth);
    assert(x[nth] == 2);
}

/// Provide a custom pivot function
version(mir_test)
@safe pure
unittest {
    static auto tail(Iterator, SliceKind kind)(Slice!(Iterator, 1, kind) slice) {
        return slice.length - 1;
    }

    size_t nth = 2;
    auto x = [3, 1, 5, 0, 2].sliced;
    x.topN!("a < b", tail)(nth);
    assert(x[nth] == 2);
}

version(unittest) {
    template checkTopNAll(alias less = "a < b", alias pivotFunction = setPivotAt)
    {
        import mir.functional: naryFun;

        static if (__traits(isSame, naryFun!less, less))
        {
            @safe pure nothrow
            static bool checkTopNAll
                (Iterator, SliceKind kind)(
                    Slice!(Iterator, 1, kind) x)
            {
                auto x_sorted = x.dup;
                x_sorted.sort!less;

                bool result = true;

                foreach (nth; 0 .. x.length)
                {
                    auto x_i = x.dup;
                    x_i.topN!(less, pivotFunction)(nth);
                    if (x_i[nth] != x_sorted[nth]) {
                        result = false;
                        break;
                    }
                }
                return result;
            }
        } else {
            alias checkTopNAll = .checkTopNAll!(naryFun!less, pivotFunction);
        }
    }
}

version(mir_test)
@safe pure
unittest {
    assert(checkTopNAll([2, 2].sliced));
    
    assert(checkTopNAll([3, 1, 5, 2, 0].sliced));
    assert(checkTopNAll([3, 1, 5, 0, 2].sliced));
    assert(checkTopNAll([0, 0, 4, 3, 3].sliced));
    assert(checkTopNAll([5, 1, 5, 1, 5].sliced));
    assert(checkTopNAll([2, 2, 0, 0, 0].sliced));
    
    assert(checkTopNAll([ 2, 12, 10,  8,  1, 20, 19,  1,  2,  7].sliced));
    assert(checkTopNAll([ 4, 18, 16,  0, 15,  6,  2, 17, 10, 16].sliced));
    assert(checkTopNAll([ 7,  5,  9,  4,  4,  2, 12, 20, 15, 15].sliced));

    assert(checkTopNAll([17, 87, 58, 50, 34, 98, 25, 77, 88, 79].sliced));

}
