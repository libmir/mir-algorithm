/++
This is a submodule of $(MREF mir,ndslice).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Andrei Alexandrescu 2008-2016, Ilya Yaroshenko 2016-, 
Authors:   Ilya Yaroshenko, Andrei Alexandrescu
+/
module mir.ndslice.sorting;

import mir.ndslice.slice;
import mir.internal.utility;

@fastmath:

/++
Checks whether a slice is sorted according to the comparison
operation $(D less). Performs $(BIGOH ndslice.elementsCount) evaluations of `less`.
Unlike `isSorted`, $(LREF _isStrictlyMonotonic) does not allow for equal values,
i.e. values for which both `less(a, b)` and `less(b, a)` are false.
With either function, the predicate must be a strict ordering just like with
`isSorted`. For example, using `"a <= b"` instead of `"a < b"` is
incorrect and will cause failed assertions.

Params:
    less = Predicate the ndslice should be sorted by.
Note:
    isSorted requires predicates for floating point types looks like `!(cmp_condition)`
    to return false if the ndslice contains NaNs.
+/
template isSorted(alias less = "!(a >= b)")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    /++
    slice = A slice to check for sortedness.
    Returns:
        `true` if the ndslice is sorted, false otherwise. `isSorted` allows
        duplicates, $(LREF _isStrictlyMonotonic) not.
    +/
    @fastmath bool isSorted(SliceKind kind, size_t[] packs, Iterator)
        (Slice!(kind, packs, Iterator) slice)
        if (packs.length == 1)
    {
        import mir.functional: reverseArgs;
        import mir.ndslice.algorithm: all;
        import mir.ndslice.topology: flattened, slide;
        return slice.flattened.slide!(2, reverseArgs!less).all!"!a";
    }
    else
        alias isSorted = .isSorted!(naryFun!less);
}

/// ditto
template isStrictlyMonotonic(alias less = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    ///
    @fastmath bool isStrictlyMonotonic(SliceKind kind, size_t[] packs, Iterator)
        (Slice!(kind, packs, Iterator) slice)
        if (packs.length == 1)
    {
        import mir.ndslice.algorithm: all;
        import mir.ndslice.topology: flattened, slide;
        return slice.flattened.slide!(2, less).all!"a";
    }
    else
        alias isStrictlyMonotonic = .isStrictlyMonotonic!(naryFun!less);
}


///
unittest
{
    assert([1, 1, 2].sliced.isSorted);
    // strictly monotonic doesn't allow duplicates
    assert(![1, 1, 2].sliced.isStrictlyMonotonic);

    auto arr = [4, 3, 2, 1].sliced;
    assert(!isSorted(arr));
    assert(!isStrictlyMonotonic(arr));

    sort(arr);
    assert(isSorted(arr));
    assert(isStrictlyMonotonic(arr));
}

unittest
{
    auto a = [1, 2, 3].sliced;
    assert(isSorted(a[0 .. 0]));
    assert(isSorted(a[0 .. 1]));
    assert(isSorted(a));
    auto b = [1, 3, 2].sliced;
    assert(!isSorted(b));

    // ignores duplicates
    auto c = [1, 1, 2].sliced;
    assert(isSorted(c));
}

unittest
{
    assert([1, 2, 3][0 .. 0].sliced.isStrictlyMonotonic);
    assert([1, 2, 3][0 .. 1].sliced.isStrictlyMonotonic);
    assert([1, 2, 3].sliced.isStrictlyMonotonic);
    assert(![1, 3, 2].sliced.isStrictlyMonotonic);
    assert(![1, 1, 2].sliced.isStrictlyMonotonic);
}


///
template sort(alias less = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    ///
    @fastmath Slice!(kind, packs, Iterator) sort(SliceKind kind, size_t[] packs, Iterator)
        (Slice!(kind, packs, Iterator) slice)
        if (packs.length == 1)
    {
        import mir.ndslice.topology: flattened;
        slice.flattened.quickSortImpl!less;
        return slice;
    }
    else
        alias sort = .sort!(naryFun!less);
}

///
unittest
{
    import mir.ndslice.slice;

    int[10] arr = [7,1,3,2,9,0,5,4,8,6];

    auto data = arr[].ptr.sliced(arr.length);
    data.sort();
    assert(data.isSorted);
}

void quickSortImpl(alias less, Iterator)(Slice!(Contiguous, [1], Iterator) slice)
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

void setPivot(alias less, Iterator)(size_t length, ref Iterator l, ref Iterator mid, ref Iterator r)
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
    (ref Iterator a, ref Iterator b, ref Iterator c)
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
    (ref Iterator a, ref Iterator b, ref Iterator c, ref Iterator d, ref Iterator e)
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
