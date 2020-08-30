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

void medianOf(alias less, bool leanRight = false, Iterator)
    (ref Iterator a, ref Iterator b) @trusted
{
   import mir.utility : swapStars;

    if (less(*b, *a)) {
        swapStars(a, b);
    }
    assert(!less(*b, *a));
}

void medianOf(alias less, bool leanRight = false, Iterator)
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

void medianOf(alias less, bool leanRight = false, Iterator)
    (ref Iterator a, ref Iterator b, ref Iterator c, ref Iterator d) @trusted
{
    import mir.utility: swapStars;

    static if (!leanRight)
    {
        // Eliminate the rightmost from the competition
        if (less(*d, *c)) swapStars(c, d); // c <= d
        if (less(*d, *b)) swapStars(b, d); // b <= d
        medianOf!less(a, b, c);
    }
    else
    {
        // Eliminate the leftmost from the competition
        if (less(*b, *a)) swapStars(a, b); // a <= b
        if (less(*c, *a)) swapStars(a, c); // a <= c
        medianOf!less(b, c, d);
    }
}

void medianOf(alias less, bool leanRight = false, Iterator)
    (ref Iterator a, ref Iterator b, ref Iterator c, ref Iterator d, ref Iterator e) @trusted
{
    import mir.utility: swapStars; // Credit: Teppo Niinimäki

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
access, (3) allows multiple indices, each on a different predicate,
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
Partitions `slice` around `pivot` using comparison function `less`, algorithm 
akin to $(LINK2 https://en.wikipedia.org/wiki/Quicksort#Hoare_partition_scheme,
Hoare partition). Specifically, permutes elements of `slice` and returns
an index `k < slice.length` such that: 

$(UL

$(LI `slice[pivot]` is swapped to `slice[k]`)

 
$(LI All elements `e` in subrange `slice[0 .. k]` satisfy `!less(slice[k], e)`
(i.e. `slice[k]` is greater than or equal to each element to its left according 
to predicate `less`))

$(LI All elements `e` in subrange `slice[k .. $]` satisfy 
`!less(e, slice[k])` (i.e. `slice[k]` is less than or equal to each element to 
its right according to predicate `less`)))

If `slice` contains equivalent elements, multiple permutations of `slice` may
satisfy these constraints. In such cases, `pivotPartition` attempts to 
distribute equivalent elements fairly to the left and right of `k` such that `k`
stays close to `slice.length / 2`.
 
Params:
    less = The predicate used for comparison

Returns:
    The new position of the pivot
    
See_Also:
    $(HTTP jgrcs.info/index.php/jgrcs/article/view/142, Engineering of a Quicksort
    Partitioning Algorithm), D. Abhyankar, Journal of Global Research in Computer
    Science, February 2011. $(HTTPS youtube.com/watch?v=AxnotgLql0k, ACCU 2016
    Keynote), Andrei Alexandrescu.
+/
@trusted
template pivotPartition(alias less = "a < b")
{
    import mir.functional: naryFun;

    static if (__traits(isSame, naryFun!less, less))
    {
        /++
        Params:
            slice = slice being partitioned
            pivot = The index of the pivot for partitioning, must be less than
            `slice.length` or `0` if `slice.length` is `0`
        +/
        size_t pivotPartition(Iterator, size_t N, SliceKind kind)
                (Slice!(Iterator, N, kind) slice, 
                size_t pivot)
        {
            assert(pivot < slice.elementCount || slice.elementCount == 0 && pivot == 0, "pivotPartition: pivot must be less than the elementCount of the slice or the slice must be empty and pivot zero");

            if (slice.elementCount <= 1) return 0;

            import mir.ndslice.topology: flattened;

            auto flattenedSlice = slice.flattened;
            auto frontI = flattenedSlice._iterator;
            auto lastI = frontI + flattenedSlice.length - 1;
            auto pivotI = frontI + pivot;
            pivotPartitionImpl!less(frontI, lastI, pivotI);
            return pivotI - frontI;
        }
    } else {
        alias pivotPartition = .pivotPartition!(naryFun!less);
    }
}

/// pivotPartition with 1-dimensional Slice
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: all;

    auto x = [5, 3, 2, 6, 4, 1, 3, 7].sliced;
    size_t pivot = pivotPartition(x, x.length / 2);

    assert(x[0 .. pivot].all!(a => a <= x[pivot]));
    assert(x[pivot .. $].all!(a => a >= x[pivot]));
}

/// pivotPartition with 2-dimensional Slice
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;
    import mir.ndslice.topology: flattened;
    import mir.algorithm.iteration: all;
    
    auto x = [
        [5, 3, 2, 6],
        [4, 1, 3, 7]
    ].fuse;
    
    size_t pivot = pivotPartition(x, x.elementCount / 2);

    auto xFlattened = x.flattened;
    assert(xFlattened[0 .. pivot].all!(a => a <= xFlattened[pivot]));
    assert(xFlattened[pivot .. $].all!(a => a >= xFlattened[pivot]));
}

version(mir_test)
@safe
unittest
{
    void test(alias less)()
    {
        import mir.ndslice.slice: sliced;
        import mir.algorithm.iteration: all, equal;

        Slice!(int*) x;
        size_t pivot;

        x = [-9, -4, -2, -2, 9].sliced;
        pivot = pivotPartition!less(x, x.length / 2);
        
        assert(x[0 .. pivot].all!(a => a <= x[pivot]));
        assert(x[pivot .. $].all!(a => a >= x[pivot]));

        x = [9, 2, 8, -5, 5, 4, -8, -4, 9].sliced;
        pivot = pivotPartition!less(x, x.length / 2);

        assert(x[0 .. pivot].all!(a => a <= x[pivot]));
        assert(x[pivot .. $].all!(a => a >= x[pivot]));

        x = [ 42 ].sliced;
        pivot = pivotPartition!less(x, x.length / 2);

        assert(pivot == 0);
        assert(x.equal([ 42 ]));

        x = [ 43, 42 ].sliced;
        pivot = pivotPartition!less(x, 0);
        assert(pivot == 1);
        assert(x.equal([ 42, 43 ]));

        x = [ 43, 42 ].sliced;
        pivot = pivotPartition!less(x, 1);

        assert(pivot == 0);
        assert(x.equal([ 42, 43 ]));

        x = [ 42, 42 ].sliced;
        pivot = pivotPartition!less(x, 0);

        assert(pivot == 0 || pivot == 1);
        assert(x.equal([ 42, 42 ]));

        pivot = pivotPartition!less(x, 1);

        assert(pivot == 0 || pivot == 1);
        assert(x.equal([ 42, 42 ]));
    }
    test!"a < b";
    static bool myLess(int a, int b)
    {
        static bool bogus;
        if (bogus) throw new Exception(""); // just to make it no-nothrow
        return a < b;
    }
    test!myLess;
}

@trusted
template pivotPartitionImpl(alias less)
{
    void pivotPartitionImpl(Iterator)
        (ref Iterator frontI,
         ref Iterator lastI,
         ref Iterator pivotI)
    {
        assert(pivotI <= lastI && pivotI >= frontI, "pivotPartition: pivot must be less than the length of slice or slice must be empty and pivot zero");
        
        if (frontI == lastI) return;

        import mir.utility: swapStars;

        // Pivot at the front
        swapStars(pivotI, frontI);

        // Fork implementation depending on nothrow copy, assignment, and
        // comparison. If all of these are nothrow, use the specialized
        // implementation discussed at 
        // https://youtube.com/watch?v=AxnotgLql0k.
        static if (is(typeof(
                () nothrow { auto x = frontI; x = frontI; return less(*x, *x); }
            )))
        {
            // Plant the pivot in the end as well as a sentinel
            auto loI = frontI;
            auto hiI = lastI;
            auto save = *hiI;
            *hiI = *frontI; // Vacancy is in r[$ - 1] now

            // Start process
            for (;;)
            {
                // Loop invariant
                version(mir_test)
                {
                    // this used to import std.algorithm.all, but we want to
                    // save imports when unittests are enabled if possible.
                    size_t len = lastI - frontI + 1;
                    foreach (x; 0 .. (loI - frontI))
                        assert(!less(*frontI, frontI[x]), "pivotPartition: *frontI must not be less than frontI[x]");
                    foreach (x; (hiI - frontI + 1) .. len)
                        assert(!less(frontI[x], *frontI), "pivotPartition: frontI[x] must not be less than *frontI");
                }
                do ++loI; while (less(*loI, *frontI));
                *(hiI) = *(loI);
                // Vacancy is now in slice[lo]
                do --hiI; while (less(*frontI, *hiI));
                if (loI >= hiI) break;
                *(loI) = *(hiI);
                // Vacancy is not in slice[hi]
            }
            // Fixup
            assert(loI - hiI <= 2, "pivotPartition: Following compare not possible");
            assert(!less(*frontI, *hiI), "pivotPartition: *hiI must not be less than *frontI");
            if (loI - hiI == 2)
            {
                assert(!less(hiI[1], *frontI), "pivotPartition: *(hiI + 1) must not be less than *frontI");
                *(loI) = hiI[1];
                --loI;
            }
            *loI = save;
            if (less(*frontI, save)) --loI;
            assert(!less(*frontI, *loI), "pivotPartition: *frontI must not be less than *loI");
        } else {
            auto loI = frontI;
            ++loI;
            auto hiI = lastI;

            loop: for (;; loI++, hiI--)
            {
                for (;; ++loI)
                {
                    if (loI > hiI) break loop;
                    if (!less(*loI, *frontI)) break;
                }
                // found the left bound:  !less(*loI, *frontI)
                assert(loI <= hiI, "pivotPartition: loI must be less or equal than hiI");
                for (;; --hiI)
                {
                    if (loI >= hiI) break loop;
                    if (!less(*frontI, *hiI)) break;
                }
                // found the right bound: !less(*frontI, *hiI), swap & make progress
                assert(!less(*loI, *hiI), "pivotPartition: *lowI must not be less than *hiI");
                swapStars(loI, hiI);
            }
            --loI;
        }

        swapStars(loI, frontI);
        pivotI = loI;
    }
}

version(mir_test)
@safe pure nothrow
unittest {
    import mir.ndslice.sorting: partitionAt;
    import mir.ndslice.allocation: rcslice;
    auto x = rcslice!double(4);
    x[0] = 3;
    x[1] = 2;
    x[2] = 1;
    x[3] = 0;
    partitionAt!("a > b")(x, 2);
}


version(mir_test)
@trusted pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: all;

    auto x = [5, 3, 2, 6, 4, 1, 3, 7].sliced;
    auto frontI = x._iterator;
    auto lastI = x._iterator + x.length - 1;
    auto pivotI = frontI + x.length / 2;
    alias less = (a, b) => (a < b);
    pivotPartitionImpl!less(frontI, lastI, pivotI);
    size_t pivot = pivotI - frontI;

    assert(x[0 .. pivot].all!(a => a <= x[pivot]));
    assert(x[pivot .. $].all!(a => a >= x[pivot]));
}

/++
Partitions `slice`, such that all elements `e1` from `slice[0]` to `slice[nth]` 
satisfy `!less(slice[nth], e1)`, and all elements `e2` from `slice[nth]` to
`slice[slice.length]` satisfy `!less(e2, slice[nth])`. This effectively reorders 
`slice` such that `slice[nth]` refers to the element that would fall there if 
the range were fully sorted. Performs an expected $(BIGOH slice.length) 
evaluations of `less` and `swap`, with a worst case of $(BIGOH slice.length^^2).

This function implements the [Fast, Deterministic Selection](https://erdani.com/research/sea2017.pdf)
algorithm that is implemented in the [`topN`](https://dlang.org/library/std/algorithm/sorting/top_n.html) 
function in D's standard library (as of version `2.092.0`).

Params:
    less = The predicate to sort by.

See_Also:
    $(LREF pivotPartition), https://erdani.com/research/sea2017.pdf

+/
template partitionAt(alias less = "a < b")
{
    import mir.functional: naryFun;

    static if (__traits(isSame, naryFun!less, less))
    {
        /++
        Params:
            slice = n-dimensional slice
            nth = The index of the element that should be in sorted position after the
                function is finished.
        +/
        void partitionAt(Iterator, size_t N, SliceKind kind)
            (Slice!(Iterator, N, kind) slice, size_t nth) @trusted nothrow @nogc
        {
            import mir.qualifier: lightScope;
            import core.lifetime: move;
            import mir.ndslice.topology: flattened;

            assert(slice.elementCount > 0, "partitionAt: slice must have elementCount greater than 0");
            assert(nth >= 0, "partitionAt: nth must be greater than or equal to zero");
            assert(nth < slice.elementCount, "partitionAt: nth must be less than the elementCount of the slice");
        
            bool useSampling = true;
            auto flattenedSlice = slice.move.flattened;
            auto frontI = flattenedSlice._iterator.lightScope;
            auto lastI = frontI + (flattenedSlice.length - 1);
            partitionAtImpl!less(frontI, lastI, nth, useSampling);
        }
    }
    else
        alias partitionAt = .partitionAt!(naryFun!less);
}

/// Partition 1-dimensional slice at nth
version(mir_test)
@safe pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 2;
    auto x = [3, 1, 5, 2, 0].sliced;
    x.partitionAt(nth);
    assert(x[nth] == 2);
}

/// Partition 2-dimensional slice
version(mir_test)
@safe pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 4;
    auto x = [3, 1, 5, 2, 0, 7].sliced(3, 2);
    x.partitionAt(nth);
    assert(x[2, 0] == 5);
}

/// Can supply alternate ordering function
version(mir_test)
@safe pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 2;
    auto x = [3, 1, 5, 2, 0].sliced;
    x.partitionAt!("a > b")(nth);
    assert(x[nth] == 2);
}

version(unittest) {
    template checkTopNAll(alias less = "a < b")
    {
        import mir.functional: naryFun;
        import mir.ndslice.slice: SliceKind, Slice;

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
                    x_i.partitionAt!less(nth);
                    if (x_i[nth] != x_sorted[nth]) {
                        result = false;
                        break;
                    }
                }
                return result;
            }
        } else {
            alias checkTopNAll = .checkTopNAll!(naryFun!less);
        }
    }
}

version(mir_test)
@safe pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

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

    assert(checkTopNAll([ 6,  7, 10, 25,  5, 10,  9,  0,  2, 15,  7,  9, 11,  8, 13, 18, 17, 13, 25, 22].sliced));
    assert(checkTopNAll([21,  3, 11, 22, 24, 12, 14, 12, 15, 15,  1,  3, 12, 15, 25, 19,  9, 16, 16, 19].sliced));
    assert(checkTopNAll([22,  6, 18,  0,  1,  8, 13, 13, 16, 19, 23, 17,  4,  6, 12, 24, 15, 20, 11, 17].sliced));
    assert(checkTopNAll([19, 23, 14,  5, 12,  3, 13,  7, 25, 25, 24,  9, 21, 25, 12, 22, 15, 22,  7, 11].sliced));
    assert(checkTopNAll([ 0,  2,  7, 16,  2, 20,  1, 11, 17,  5, 22, 17, 25, 13, 14,  5, 22, 21, 24, 14].sliced));
}

private @trusted pure nothrow @nogc
void partitionAtImpl(alias less, Iterator)(
    Iterator loI, 
    Iterator hiI, 
    size_t n, 
    bool useSampling)
{
    assert(loI <= hiI, "partitionAtImpl: frontI must be less than or equal to lastI");

    import mir.utility: swapStars;
    import mir.functional: reverseArgs;

    Iterator pivotI;
    size_t len;

    for (;;) {
        len = hiI - loI + 1;

        if (len <= 1) {
            break;
        }

        if (n == 0) {
            pivotI = loI;
            foreach (i; 1 .. len) {
                if (less(loI[i], *pivotI)) {
                    pivotI = loI + i;
                }
            }
            swapStars(loI + n, pivotI);
            break;
        }

        if (n + 1 == len) {
            pivotI = loI;
            foreach (i; 1 .. len) {
                if (reverseArgs!less(loI[i], *pivotI)) {
                    pivotI = loI + i;
                }
            }
            swapStars(loI + n, pivotI);
            break;
        }
        
        if (len <= 12) {
            pivotI = loI + len / 2;
            pivotPartitionImpl!less(loI, hiI, pivotI);
        } else if (n * 16 <= (len - 1) * 7) {
            pivotI = partitionAtPartitionOffMedian!(less, false)(loI, hiI, n, useSampling);
            // Quality check
            if (useSampling)
            {
                auto pivot = pivotI - loI;
                if (pivot < n)
                {
                    if (pivot * 4 < len)
                    {
                        useSampling = false;
                    }
                }
                else if ((len - pivot) * 8 < len * 3)
                {
                    useSampling = false;
                }
            }
        } else if (n * 16 >= (len - 1) * 9) {
            pivotI = partitionAtPartitionOffMedian!(less, true)(loI, hiI, n, useSampling);
            // Quality check
            if (useSampling)
            {
                auto pivot = pivotI - loI;
                if (pivot < n)
                {
                    if (pivot * 8 < len * 3)
                    {
                        useSampling = false;
                    }
                }
                else if ((len - pivot) * 4 < len)
                {
                    useSampling = false;
                }
            }
        } else {
            pivotI = partitionAtPartition!less(loI, hiI, n, useSampling);
            // Quality check
            if (useSampling) {
                auto pivot = pivotI - loI;
                if (pivot * 9 < len * 2 || pivot * 9 > len * 7)
                {
                    // Failed - abort sampling going forward
                    useSampling = false;
                }
            }
        }

        if (n < (pivotI - loI)) {
            hiI = pivotI - 1;
        } else if (n > (pivotI - loI)) {
            n -= (pivotI - loI + 1);
            loI = pivotI;
            ++loI;
        } else {
            break;
        }
    }
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 2;
    auto x = [3, 1, 5, 2, 0].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, 1, true);
    assert(x[nth] == 2);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 4;
    auto x = [3, 1, 5, 2, 0, 7].sliced(3, 2);
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, nth, true);
    assert(x[2, 0] == 5);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 1;
    auto x = [0, 0, 4, 3, 3].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, nth, true);
    assert(x[nth] == 0);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 2;
    auto x = [0, 0, 4, 3, 3].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, nth, true);
    assert(x[nth] == 3);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 3;
    auto x = [0, 0, 4, 3, 3].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, nth, true);
    assert(x[nth] == 3);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 4;
    auto x = [ 2, 12, 10,  8,  1, 20, 19,  1,  2,  7].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, nth, true);
    assert(x[nth] == 7);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 5;
    auto x = [ 2, 12, 10,  8,  1, 20, 19,  1,  2,  7].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, nth, true);
    assert(x[nth] == 8);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    size_t nth = 6;
    auto x = [ 2, 12, 10,  8,  1, 20, 19,  1,  2,  7].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.elementCount - 1;
    partitionAtImpl!((a, b) => (a < b))(frontI, lastI, nth, true);
    assert(x[nth] == 10);
}

private @trusted pure nothrow @nogc
Iterator partitionAtPartition(alias less, Iterator)(
    ref Iterator frontI, 
    ref Iterator lastI, 
    size_t n, 
    bool useSampling)
{
    size_t len = lastI - frontI + 1;

    assert(len >= 9 && n < len, "partitionAtImpl: length must be longer than 9 and n must be less than r.length");

    size_t ninth = len / 9;
    size_t pivot = ninth / 2;
    // Position subrange r[loI .. hiI] to have length equal to ninth and its upper
    // median r[loI .. hiI][$ / 2] in exactly the same place as the upper median
    // of the entire range r[$ / 2]. This is to improve behavior for searching
    // the median in already sorted ranges.
    auto loI = frontI;
    loI += len / 2 - pivot;
    auto hiI = loI;
    hiI += ninth;

    // We have either one straggler on the left, one on the right, or none.
    assert(loI - frontI <= lastI - hiI + 1 || lastI - hiI <= loI - frontI + 1, "partitionAtPartition: straggler check failed for loI, len, hiI");
    assert(loI - frontI >= ninth * 4, "partitionAtPartition: loI - frontI >= ninth * 4");
    assert(lastI - hiI >= ninth * 4, "partitionAtPartition: lastI - hiI >= ninth * 4");

    // Partition in groups of 3, and the mid tertile again in groups of 3
    if (!useSampling) {
        auto loI_ = loI;
        loI_ -= ninth;
        auto hiI_ = hiI;
        hiI_ += ninth;
        p3!(less, Iterator)(frontI, lastI, loI_, hiI_);
    }
    p3!(less, Iterator)(frontI, lastI, loI, hiI);

    // Get the median of medians of medians
    // Map the full interval of n to the full interval of the ninth
    pivot = (n * (ninth - 1)) / (len - 1);
    if (hiI > loI) {
        auto hiI_minus = hiI;
        --hiI_minus;
        partitionAtImpl!less(loI, hiI_minus, pivot, useSampling);
    }

    auto pivotI = loI;
    pivotI += pivot;

    return expandPartition!less(frontI, lastI, loI, pivotI, hiI);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;

    auto x = [ 6,  7, 10, 25,  5, 10,  9,  0,  2, 15,  7,  9, 11,  8, 13, 18, 17, 13, 25, 22].sliced;
    auto x_sort = x.dup;
    x_sort = x_sort.sort;
    auto frontI = x._iterator;
    auto lastI = frontI + x.length - 1;
    size_t n = x.length / 2;
    partitionAtPartition!((a, b) => (a < b))(frontI, lastI, n, true);
    assert(x[n - 1] == x_sort[n - 1]);
}

private @trusted pure nothrow @nogc
Iterator partitionAtPartitionOffMedian(alias less, bool leanRight, Iterator)(
    ref Iterator frontI, 
    ref Iterator lastI, 
    size_t n, 
    bool useSampling)
{
    size_t len = lastI - frontI + 1;

    assert(len >= 12, "partitionAtPartitionOffMedian: len must be greater than 11");
    assert(n < len, "partitionAtPartitionOffMedian: n must be less than len");
    auto _4 = len / 4;
    auto leftLimitI = frontI;
    static if (leanRight)
        leftLimitI += 2 * _4;
    else
        leftLimitI += _4;
    // Partition in groups of 4, and the left quartile again in groups of 3
    if (!useSampling)
    {
        auto leftLimit_plus_4 = leftLimitI;
        leftLimit_plus_4 += _4;
        p4!(less, leanRight)(frontI, lastI, leftLimitI, leftLimit_plus_4);
    }
    auto _12 = _4 / 3;
    auto loI = leftLimitI;
    loI += _12;
    auto hiI = loI;
    hiI += _12;
    p3!less(frontI, lastI, loI, hiI);

    // Get the median of medians of medians
    // Map the full interval of n to the full interval of the ninth
    auto pivot = (n * (_12 - 1)) / (len - 1);
    if (hiI > loI) {
        auto hiI_minus = hiI;
        --hiI_minus;
        partitionAtImpl!less(loI, hiI_minus, pivot, useSampling);
    }
    auto pivotI = loI;
    pivotI += pivot;
    return expandPartition!less(frontI, lastI, loI, pivotI, hiI);
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: equal;

    auto x = [ 6,  7, 10, 25,  5, 10,  9,  0,  2, 15,  7,  9, 11,  8, 13, 18, 17, 13, 25, 22].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.length - 1;
    partitionAtPartitionOffMedian!((a, b) => (a < b), false)(frontI, lastI, 5, true);
    assert(x.equal([6, 7, 8, 9, 5, 0, 2, 7, 9, 15, 10, 25, 11, 10, 13, 18, 17, 13, 25, 22]));
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: equal;

    auto x = [ 6,  7, 10, 25,  5, 10,  9,  0,  2, 15,  7,  9, 11,  8, 13, 18, 17, 13, 25, 22].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.length - 1;
    partitionAtPartitionOffMedian!((a, b) => (a < b), true)(frontI, lastI, 15, true);
    assert(x.equal([6, 7, 8, 7, 5, 2, 9, 0, 9, 15, 25, 10, 11, 10, 13, 18, 17, 13, 25, 22]));
}

private @trusted
void p3(alias less, Iterator)(
    Iterator frontI,
    Iterator lastI,
    Iterator loI,
    Iterator hiI)
{
    assert(loI <= hiI && hiI <= lastI, "p3: loI must be less than or equal to hiI and hiI must be less than or equal to lastI");
    immutable diffI = hiI - loI;
    Iterator lo_loI;
    Iterator hi_loI;
    for (; loI < hiI; ++loI)
    {
        lo_loI = loI;
        lo_loI -= diffI;
        hi_loI = loI;
        hi_loI += diffI;
        assert(lo_loI >= frontI, "p3: lo_loI must be greater than or equal to frontI");
        assert(hi_loI <= lastI, "p3: hi_loI must be less than or equal to lastI");
        medianOf!less(lo_loI, loI, hi_loI);
    }
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: equal;

    auto x = [3, 4, 0, 5, 2, 1].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.length - 1;
    auto loI = frontI + 2;
    auto hiI = frontI + 4;
    p3!((a, b) => (a < b))(frontI, lastI, loI, hiI);
    assert(x.equal([0, 1, 2, 4, 3, 5]));
}

private @trusted
template p4(alias less, bool leanRight)
{
    void p4(Iterator)(
        Iterator frontI,
        Iterator lastI,
        Iterator loI, 
        Iterator hiI)
    {
        assert(loI <= hiI && hiI <= lastI, "p4: loI must be less than or equal to hiI and hiI must be less than or equal to lastI");

        immutable diffI = hiI - loI; 
        immutable diffI2 = diffI * 2;

        Iterator lo_loI;
        Iterator hi_loI;

        static if (leanRight)
            Iterator lo2_loI;
        else
            Iterator hi2_loI;

        for (; loI < hiI; ++loI)
        {
            lo_loI = loI - diffI;
            hi_loI = loI + diffI;
            
            assert(lo_loI >= frontI, "p4: lo_loI must be greater than or equal to frontI");
            assert(hi_loI <= lastI, "p4: hi_loI must be less than or equal to lastI");

            static if (leanRight) {
                lo2_loI = loI - diffI2;
                assert(lo2_loI >= frontI, "lo2_loI must be greater than or equal to frontI");
                medianOf!(less, leanRight)(lo2_loI, lo_loI, loI, hi_loI);
            } else {
                hi2_loI = loI + diffI2;
                assert(hi2_loI <= lastI, "hi2_loI must be less than or equal to lastI");
                medianOf!(less, leanRight)(lo_loI, loI, hi_loI, hi2_loI);
            }
        }
    }
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: equal;

    auto x = [3, 4, 0, 7, 2, 6, 5, 1, 4].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.length - 1;
    auto loI = frontI + 3;
    auto hiI = frontI + 5;
    p4!((a, b) => (a < b), false)(frontI, lastI, loI, hiI);
    assert(x.equal([3, 1, 0, 4, 2, 6, 4, 7, 5]));
}

version(mir_test)
@trusted pure nothrow
unittest {
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: equal;

    auto x = [3, 4, 0, 8, 2, 7, 5, 1, 4, 3].sliced;
    auto frontI = x._iterator;
    auto lastI = frontI + x.length - 1;
    auto loI = frontI + 4;
    auto hiI = frontI + 6;
    p4!((a, b) => (a < b), true)(frontI, lastI, loI, hiI);
    assert(x.equal([0, 4, 2, 1, 3, 7, 5, 8, 4, 3]));
}

private @trusted
template expandPartition(alias less)
{
    Iterator expandPartition(Iterator)(
        ref Iterator frontI,
        ref Iterator lastI,
        ref Iterator loI,
        ref Iterator pivotI,
        ref Iterator hiI)
    {
        import mir.algorithm.iteration: all;
        
        assert(frontI <= loI, "expandPartition: frontI must be less than or equal to loI");
        assert(loI <= pivotI, "expandPartition: loI must be less than or equal pivotI");
        assert(pivotI < hiI, "expandPartition: pivotI must be less than hiI");
        assert(hiI <= lastI, "expandPartition: hiI must be less than or equal to lastI");
        
        foreach(x; loI .. (pivotI + 1))
            assert(!less(*pivotI, *x), "expandPartition: loI .. (pivotI + 1) failed test");
        foreach(x; (pivotI + 1) .. hiI)
            assert(!less(*x, *pivotI), "expandPartition: (pivotI + 1) .. hiI failed test");

        import mir.utility: swapStars;
        import mir.algorithm.iteration: all;
        // We work with closed intervals!
        --hiI;

        auto leftI = frontI;
        auto rightI = lastI;
        loop: for (;; ++leftI, --rightI)
        {
            for (;; ++leftI)
            {
                if (leftI == loI) break loop;
                if (!less(*leftI, *pivotI)) break;
            }
            for (;; --rightI)
            {
                if (rightI == hiI) break loop;
                if (!less(*pivotI, *rightI)) break;
            }
            swapStars(leftI, rightI);
        }

        foreach(x; loI .. (pivotI + 1))
            assert(!less(*pivotI, *x), "expandPartition: loI .. (pivotI + 1) failed less than test");
        foreach(x; (pivotI + 1) .. (hiI + 1))
            assert(!less(*x, *pivotI), "expandPartition: (pivotI + 1) .. (hiI + 1) failed less than test");
        foreach(x; frontI .. leftI)
            assert(!less(*pivotI, *x), "expandPartition: frontI .. leftI failed less than test");
        foreach(x; (rightI + 1) .. (lastI + 1))
            assert(!less(*x, *pivotI), "expandPartition: (rightI + 1) .. (lastI + 1) failed less than test"); 

        auto oldPivotI = pivotI;

        if (leftI < loI)
        {
            // First loop: spend r[loI .. pivot]
            for (; loI < pivotI; ++leftI)
            {
                if (leftI == loI) goto done;
                if (!less(*oldPivotI, *leftI)) continue;
                --pivotI;
                assert(!less(*oldPivotI, *pivotI), "expandPartition: less check failed");
                swapStars(leftI, pivotI);
            }
            // Second loop: make leftI and pivot meet
            for (;; ++leftI)
            {
                if (leftI == pivotI) goto done;
                if (!less(*oldPivotI, *leftI)) continue;
                for (;;)
                {
                    if (leftI == pivotI) goto done;
                    --pivotI;
                    if (less(*pivotI, *oldPivotI))
                    {
                        swapStars(leftI, pivotI);
                        break;
                    }
                }
            }
        }

        // First loop: spend r[lo .. pivot]
        for (; hiI != pivotI; --rightI)
        {
            if (rightI == hiI) goto done;
            if (!less(*rightI, *oldPivotI)) continue;
            ++pivotI;
            assert(!less(*pivotI, *oldPivotI), "expandPartition: less check failed");
            swapStars(rightI, pivotI);
        }
        // Second loop: make leftI and pivotI meet
        for (; rightI > pivotI; --rightI)
        {
            if (!less(*rightI, *oldPivotI)) continue;
            while (rightI > pivotI)
            {
                ++pivotI;
                if (less(*oldPivotI, *pivotI))
                {
                    swapStars(rightI, pivotI);
                    break;
                }
            }
        }

    done:
        swapStars(oldPivotI, pivotI);
        

        foreach(x; frontI .. (pivotI + 1))
            assert(!less(*pivotI, *x), "expandPartition: frontI .. (pivotI + 1) failed test");
        foreach(x; (pivotI + 1) .. (lastI + 1))
            assert(!less(*x, *pivotI), "expandPartition: (pivotI + 1) .. (lastI + 1) failed test");
        return pivotI;
    }
}

version(mir_test)
@trusted pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;

    auto a = [ 10, 5, 3, 4, 8,  11,  13, 3, 9, 4, 10 ].sliced;
    auto frontI = a._iterator;
    auto lastI = frontI + a.length - 1;
    auto loI = frontI + 4;
    auto pivotI = frontI + 5;
    auto hiI = frontI + 6;
    assert(expandPartition!((a, b) => a < b)(frontI, lastI, loI, pivotI, hiI) == (frontI + 9));
}
