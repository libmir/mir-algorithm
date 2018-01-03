// Written in the D programming language.
/**
This is a submodule of $(MREF mir, algorithm). It contains `nothrow` `@nogc` BetterC alternative to `MultiwayMerge` from `std.algorithm.setops`.

Copyright: Andrei Alexandrescu 2008-.
License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: $(HTTP erdani.com, Andrei Alexandrescu) (original Phobos code), Ilya Yaroshenko (Mir & BetterC rework, optimization).
 */
module mir.algorithm.setops;

import mir.functional: naryFun;

/**
Merges multiple sets. The input sets are passed as a
range of ranges and each is assumed to be sorted by $(D
less). Computation is done lazily, one union element at a time. The
complexity of one $(D popFront) operation is $(BIGOH
log(ror.length)). However, the length of $(D ror) decreases as ranges
in it are exhausted, so the complexity of a full pass through $(D
MultiwayMerge) is dependent on the distribution of the lengths of ranges
contained within $(D ror). If all ranges have the same length $(D n)
(worst case scenario), the complexity of a full pass through $(D
MultiwayMerge) is $(BIGOH n * ror.length * log(ror.length)), i.e., $(D
log(ror.length)) times worse than just spanning all ranges in
turn. The output comes sorted (unstably) by $(D less).
The length of the resulting range is the sum of all lengths of
the ranges passed as input. This means that all elements (duplicates
included) are transferred to the resulting range.
For backward compatibility, `multiwayMerge` is available under
the name `nWayUnion` and `MultiwayMerge` under the name of `NWayUnion` .
Future code should use `multiwayMerge` and `MultiwayMerge` as `nWayUnion`
and `NWayUnion` will be deprecated.
Params:
    less = Predicate the given ranges are sorted by.
    ror = A range of ranges sorted by `less` to compute the union for.
Returns:
    A range of the union of the ranges in `ror`.
Warning: Because $(D MultiwayMerge) does not allocate extra memory, it
will leave $(D ror) modified. Namely, $(D MultiwayMerge) assumes ownership
of $(D ror) and discretionarily swaps and advances elements of it. If
you want $(D ror) to preserve its contents after the call, you may
want to pass a duplicate to $(D MultiwayMerge) (and perhaps cache the
duplicate in between calls).
 */
struct MultiwayMerge(alias less, RangeOfRanges)
{
    import mir.array.primitives;
    import mir.container.binaryheap;
    import std.range.primitives: ElementType;

    ///
    @disable this();
    ///
    @disable this(this);

    ///
    static bool compFront()(auto ref ElementType!RangeOfRanges a, auto ref ElementType!RangeOfRanges b)
    {
        // revert comparison order so we get the smallest elements first
        return less(b.front, a.front);
    }

    /// Heap
    BinaryHeap!(compFront, RangeOfRanges) _heap;

    ///
    this()(auto ref RangeOfRanges ror)
    {
        import std.algorithm.mutation : remove, SwapStrategy;

        // Preemptively get rid of all empty ranges in the input
        // No need for stability either
        //Build the heap across the range
        _heap = typeof(_heap)(ror.remove!("a.empty", SwapStrategy.unstable));
    }

    ///
    @property bool empty()() { return _heap.empty; }

    ///
    @property auto ref front()()
    {
        assert(!empty);
        return _heap.front.front;
    }

    ///
    void popFront()()
    {
        _heap._store.front.popFront;
        if (!_heap._store.front.empty)
            _heap.siftDown(_heap._store[], 0, _heap._length);
        else
            _heap.removeFront;
    }
}

/// Ditto
MultiwayMerge!(naryFun!less, RangeOfRanges) multiwayMerge
(alias less = "a < b", RangeOfRanges)
(auto ref RangeOfRanges ror)
{
    return typeof(return)(ror);
}

///
@safe nothrow @nogc unittest
{
    import std.algorithm.comparison : equal;

    static a =
    [
        [ 1, 4, 7, 8 ],
        [ 1, 7 ],
        [ 1, 7, 8],
        [ 4 ],
        [ 7 ],
    ];
    static witness = [
        1, 1, 1, 4, 4, 7, 7, 7, 7, 8, 8
    ];
    assert(a.multiwayMerge.equal(witness));

    static b =
    [
        // range with duplicates
        [ 1, 1, 4, 7, 8 ],
        [ 7 ],
        [ 1, 7, 8],
        [ 4 ],
        [ 7 ],
    ];
    // duplicates are propagated to the resulting range
    assert(b.multiwayMerge.equal(witness));
}

/**
Computes the union of multiple ranges. The input ranges are passed
as a range of ranges and each is assumed to be sorted by $(D
less). Computation is done lazily, one union element at a time.
`multiwayUnion(ror)` is functionally equivalent to `multiwayMerge(ror).uniq`.
"The output of multiwayUnion has no duplicates even when its inputs contain duplicates."
Params:
    less = Predicate the given ranges are sorted by.
    ror = A range of ranges sorted by `less` to compute the intersection for.
Returns:
    A range of the union of the ranges in `ror`.
See also: $(LREF multiwayMerge)
 */
auto multiwayUnion(alias less = "a < b", RangeOfRanges)(auto ref RangeOfRanges ror)
{
    import mir.functional: not;
    import mir.algorithm.iteration : Uniq;

    return Uniq!(not!less, typeof(multiwayMerge!less(ror)))(multiwayMerge!less(ror));
}

///
@system unittest
{
    import std.algorithm.comparison : equal;

    // sets
    double[][] a =
    [
        [ 1, 4, 7, 8 ],
        [ 1, 7 ],
        [ 1, 7, 8],
        [ 4 ],
        [ 7 ],
    ];

    auto witness = [1, 4, 7, 8];
    assert(a.multiwayUnion.equal(witness));

    // multisets
    double[][] b =
    [
        [ 1, 1, 1, 4, 7, 8 ],
        [ 1, 7 ],
        [ 1, 7, 7, 8],
        [ 4 ],
        [ 7 ],
    ];
    assert(b.multiwayUnion.equal(witness));
}

/++
Computes the length of union of multiple ranges. The input ranges are passed
as a range of ranges and each is assumed to be sorted by `less`.

Params:
    less = Predicate the given ranges are sorted by.
    ror = A range of ranges sorted by `less` to compute the intersection for.
Returns:
    A length of the union of the ranges in `ror`.
+/
pragma(inline, false)
size_t unionLength(alias less = "a < b", RangeOfRanges)(RangeOfRanges ror)
{
    size_t length;
    auto u = ror.multiwayUnion!less;
    if (!u.empty) do {
        length++;
        u.popFront;
    } while(!u.empty);
    return length;
}
