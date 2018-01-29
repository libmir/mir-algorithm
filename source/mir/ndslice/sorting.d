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
Authors:   Ilya Yaroshenko, Andrei Alexandrescu

Macros:
    SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
+/
module mir.ndslice.sorting;

/// Check if ndslice is sorted, or strictly monotonic.
version(mir_test) @safe pure unittest
{
    import mir.ndslice.algorithm: all;
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
    import mir.ndslice.algorithm: all;
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
    import mir.ndslice.algorithm: all;
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

deprecated(`Use 'yourSlice.pairwise!"a <= b".all' instead. Imports:
    import mir.ndslice.algorithm: all;
    import mir.ndslice.topology: pairwise;
`)
template isSorted(alias less = "!(a >= b)")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    @optmath bool isSorted(SliceKind kind, size_t[] packs, Iterator)
        (Slice!(kind, packs, Iterator) slice)
        if (packs.length == 1)
    {
        import mir.functional: reverseArgs, not;
        import mir.ndslice.algorithm: all;
        import mir.ndslice.topology: flattened, pairwise;
        return slice.flattened.pairwise!(not!(reverseArgs!less)).all;
    }
    else
        alias isSorted = .isSorted!(naryFun!less);
}

deprecated(`Use 'yourSlice.pairwise!"a < b".all' instead. Imports:
    import mir.ndslice.algorithm: all;
    import mir.ndslice.topology: pairwise;
`)
template isStrictlyMonotonic(alias less = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    @optmath bool isStrictlyMonotonic(SliceKind kind, size_t[] packs, Iterator)
        (Slice!(kind, packs, Iterator) slice)
        if (packs.length == 1)
    {
        import mir.ndslice.algorithm: all;
        import mir.ndslice.topology: flattened, pairwise;
        return slice.flattened.pairwise!less.all;
    }
    else
        alias isStrictlyMonotonic = .isStrictlyMonotonic!(naryFun!less);
}

@safe pure version(mir_test) unittest
{
    import mir.ndslice.algorithm: all;
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
    import mir.ndslice.algorithm: all;
    import mir.ndslice.topology: pairwise;

    assert([1, 2, 3][0 .. 0].sliced.pairwise!"a < b".all);
    assert([1, 2, 3][0 .. 1].sliced.pairwise!"a < b".all);
    assert([1, 2, 3].sliced.pairwise!"a < b".all);
    assert(![1, 3, 2].sliced.pairwise!"a < b".all);
    assert(![1, 1, 2].sliced.pairwise!"a < b".all);
}


/++
Sorts 1D ndslice.

See_also: $(SUBREF topology, flattened).
+/
template sort(alias less = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    {
@optmath:
        ///
        Slice!(kind, packs, Iterator) sort(SliceKind kind, size_t[] packs, Iterator)
            (Slice!(kind, packs, Iterator) slice) @safe
            if (packs.length == 1)
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
            slice.flattened.quickSortImpl!less;
            return slice;
        }

        ///
        T[] sort(T)(T[] ar)
        {
            return ar.sliced.sort.field;
        }
    }
    else
        alias sort = .sort!(naryFun!less);
}

///
@safe pure version(mir_test) unittest
{
    import mir.ndslice.algorithm: all;
    import mir.ndslice.slice;
    import mir.ndslice.sorting: sort;
    import mir.ndslice.topology: pairwise;

    int[10] arr = [7,1,3,2,9,0,5,4,8,6];

    auto data = arr[].sliced(arr.length);
    data.sort();
    assert(data.pairwise!"a <= b".all);
}

void quickSortImpl(alias less, Iterator)(Slice!(Contiguous, [1], Iterator) slice) @trusted
{
    import mir.utility : swap, swapStars;

    enum  max_depth = 64;
    enum naive_est = 1024 / slice.ElemType!0.sizeof;
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
