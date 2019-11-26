/**
This module provides a $(D BinaryHeap) (aka priority queue)
adaptor that makes a binary heap out of any user-provided random-access range.

Current implementation is suitable for Mir/BetterC concepts.

This module is a submodule of $(MREF mir, container).

Copyright: 2010- Andrei Alexandrescu. All rights reserved by the respective holders.

License: Distributed under the Boost Software License, Version 1.0.

Authors: $(HTTP erdani.com, Andrei Alexandrescu) (original Phobos code), Ilya Yaroshenko (Mir & BetterC rework).
*/
module mir.container.binaryheap;

import mir.primitives;
import mir.primitives;

import std.range.primitives: isRandomAccessRange, hasSwappableElements, ElementType;
import std.traits;

///
@system nothrow @nogc version(mir_test) unittest
{
    import mir.algorithm.iteration : equal;
    import std.range : takeExactly;
    static a = [4, 7, 3, 1, 5], b = [7, 5, 4];
    auto maxHeap = a.heapify;
    assert((&maxHeap).takeExactly(3).equal(b));

    static c = [4, 7, 3, 1, 5], d = [1, 3, 4];
    auto minHeap = c.heapify!"a > b";
    assert((&minHeap).takeExactly(3).equal(d));
}

/++
Implements a $(HTTP en.wikipedia.org/wiki/Binary_heap, binary heap)
container on top of a given random-access range type (usually $(D
T[])) or a random-access container type (usually $(D Array!T)). The
documentation of $(D BinaryHeap) will refer to the underlying range or
container as the $(I store) of the heap.

The binary heap induces structure over the underlying store such that
accessing the largest element (by using the $(D front) property) is a
$(BIGOH 1) operation and extracting it (by using the $(D
removeFront()) method) is done fast in $(BIGOH log n) time.

If $(D less) is the less-than operator, which is the default option,
then $(D BinaryHeap) defines a so-called max-heap that optimizes
extraction of the $(I largest) elements. To define a min-heap,
instantiate BinaryHeap with $(D "a > b") as its predicate.

Simply extracting elements from a $(D BinaryHeap) container is
tantamount to lazily fetching elements of $(D Store) in descending
order. Extracting elements from the $(D BinaryHeap) to completion
leaves the underlying store sorted in ascending order but, again,
yields elements in descending order.

If $(D Store) is not a container, the $(D BinaryHeap) cannot grow beyond the
size of that range. If $(D Store) is a container that supports $(D
insertBack), the $(D BinaryHeap) may grow by adding elements to the
container.
+/
struct BinaryHeap(alias less = "a < b", Store)
if (isRandomAccessRange!Store || isRandomAccessRange!(typeof(Store.init[])))
{
    import mir.utility : min;
    import mir.functional : naryFun;
    static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
    import std.algorithm.mutation : swapAt;

    static if (isRandomAccessRange!Store)
        alias Range = Store;
    else
        alias Range = typeof(Store.init[]);

    alias percolate = HeapOps!(less, Range).percolate;
    alias siftDown = HeapOps!(less, Range).siftDown;
    alias buildHeap = HeapOps!(less, Range).buildHeap;

    @disable this();
    @disable this(this);

    // Comparison predicate
    private alias comp = naryFun!(less);
    // Convenience accessors

    // Asserts that the heap property is respected.
    private void assertValid() scope
    {
        debug
        {
            if (_length < 2) return;
            for (size_t n = _length - 1; n >= 1; --n)
            {
                auto parentIdx = (n - 1) / 2;
                assert(!comp(_store[parentIdx], _store[n]));
            }
        }
    }

public:

    /// The payload includes the support store and the effective length
    size_t _length;
    /// ditto
    Store _store;


    /++
       Converts the store $(D s) into a heap. If $(D initialSize) is
       specified, only the first $(D initialSize) elements in $(D s)
       are transformed into a heap, after which the heap can grow up
       to $(D r.length) (if $(D Store) is a range) or indefinitely (if
       $(D Store) is a container with $(D insertBack)). Performs
       $(BIGOH min(r.length, initialSize)) evaluations of $(D less).
    +/
    this(Store s, size_t initialSize = size_t.max)
    {
        acquire(s, initialSize);
    }

    /++
    Takes ownership of a store. After this, manipulating $(D s) may make
    the heap work incorrectly.
    +/
    void acquire(Store s, size_t initialSize = size_t.max)
    {
        _store = move(s);
        _length = min(_store.length, initialSize);
        if (_length < 2) return;
        buildHeap(_store[]);
        assertValid();
    }

    /++
    Takes ownership of a store assuming it already was organized as a
    heap.
    +/
    void assume(Store s, size_t initialSize = size_t.max)
    {
        _store = move(s);
        _length = min(_store.length, initialSize);
        assertValid();
    }

    /++
    Returns the _length of the heap.
    +/
    @property size_t length() scope const
    {
        return _length;
    }

    /++
    Returns $(D true) if the heap is _empty, $(D false) otherwise.
    +/
    @property bool empty() scope const
    {
        return !length;
    }

    /++
    Returns the _capacity of the heap, which is the length of the
    underlying store (if the store is a range) or the _capacity of the
    underlying store (if the store is a container).
    +/
    @property size_t capacity() scope const
    {
        static if (is(typeof(_store.capacity) : size_t))
        {
            return _store.capacity;
        }
        else
        {
            return _store.length;
        }
    }

    /++
    Returns a _front of the heap, which is the largest element
    according to `less`.
    +/
    @property auto ref ElementType!Store front() scope return
    {
        assert(!empty, "Cannot call front on an empty heap.");
        return _store.front;
    }



    /++
    Inserts `value` into the store. If the underlying store is a range
    and `length == capacity`, throws an AssertException.
    +/
    size_t insert(ElementType!Store value) scope
    {
        static if (is(typeof(_store.insertBack(value))))
        {
            if (length == _store.length)
            {
                // reallocate
                _store.insertBack(value);
            }
            else
            {
                // no reallocation
                _store[_length] = value;
            }
        }
        else
        {
            // can't grow
            assert(length < _store.length, "Cannot grow a heap created over a range");
            _store[_length] = value;
        }

        // sink down the element
        for (size_t n = _length; n; )
        {
            auto parentIdx = (n - 1) / 2;
            if (!comp(_store[parentIdx], _store[n])) break; // done!
            // must swap and continue
            _store.swapAt(parentIdx, n);
            n = parentIdx;
        }
        ++_length;
        debug(BinaryHeap) assertValid();
        return 1;
    }

    /++
    Removes the largest element from the heap.
    +/
    void removeFront() scope
    {
        assert(!empty, "Cannot call removeFront on an empty heap.");
        if (--_length)
            _store.swapAt(0, _length);
        percolate(_store[], 0, _length);
    }

    /// ditto
    alias popFront = removeFront;

    /++
    Removes the largest element from the heap and returns
    it. The element still resides in the heap's store. For performance
    reasons you may want to use $(D removeFront) with heaps of objects
    that are expensive to copy.
    +/
    auto ref removeAny() scope
    {
        removeFront();
        return _store[_length];
    }

    /++
    Replaces the largest element in the store with `value`.
    +/
    void replaceFront(ElementType!Store value) scope
    {
        // must replace the top
        assert(!empty, "Cannot call replaceFront on an empty heap.");
        _store.front = value;
        percolate(_store[], 0, _length);
        debug(BinaryHeap) assertValid();
    }

    /++
    If the heap has room to grow, inserts `value` into the store and
    returns $(D true). Otherwise, if $(D less(value, front)), calls $(D
    replaceFront(value)) and returns again $(D true). Otherwise, leaves
    the heap unaffected and returns $(D false). This method is useful in
    scenarios where the smallest $(D k) elements of a set of candidates
    must be collected.
    +/
    bool conditionalInsert(ElementType!Store value) scope
    {
        if (_length < _store.length)
        {
            insert(value);
            return true;
        }

        assert(!_store.empty, "Cannot replace front of an empty heap.");
        if (!comp(value, _store.front)) return false; // value >= largest
        _store.front = value;

        percolate(_store[], 0, _length);
        debug(BinaryHeap) assertValid();
        return true;
    }

    /++
    Swapping is allowed if the heap is full. If $(D less(value, front)), the
    method exchanges store.front and value and returns $(D true). Otherwise, it
    leaves the heap unaffected and returns $(D false).
    +/
    bool conditionalSwap(ref ElementType!Store value) scope
    {
        assert(_length == _store.length);
        assert(!_store.empty, "Cannot swap front of an empty heap.");

        if (!comp(value, _store.front)) return false; // value >= largest

        import std.algorithm.mutation : swap;
        swap(_store.front, value);

        percolate(_store[], 0, _length);
        debug(BinaryHeap) assertValid();

        return true;
    }
}

/// Example from "Introduction to Algorithms" Cormen et al, p 146
@system nothrow version(mir_test) unittest
{
    import mir.algorithm.iteration : equal;
    int[] a = [ 4, 1, 3, 2, 16, 9, 10, 14, 8, 7 ];
    auto h = heapify(a);
    // largest element
    assert(h.front == 16);
    // a has the heap property
    assert(equal(a, [ 16, 14, 10, 8, 7, 9, 3, 2, 4, 1 ]));
}

/// $(D BinaryHeap) implements the standard input range interface, allowing
/// lazy iteration of the underlying range in descending order.
@system nothrow version(mir_test) unittest
{
    import mir.algorithm.iteration : equal;
    import std.range : takeExactly;
    int[] a = [4, 1, 3, 2, 16, 9, 10, 14, 8, 7];
    auto heap = heapify(a);
    auto top5 = (&heap).takeExactly(5);
    assert(top5.equal([16, 14, 10, 9, 8]));
}

/++
Convenience function that returns a $(D BinaryHeap!Store) object
initialized with $(D s) and $(D initialSize).
+/
BinaryHeap!(less, Store) heapify(alias less = "a < b", Store)(Store s,
        size_t initialSize = size_t.max)
{

    return BinaryHeap!(less, Store)(s, initialSize);
}

///
@system nothrow version(mir_test) unittest
{
    import std.range.primitives;
    {
        // example from "Introduction to Algorithms" Cormen et al., p 146
        int[] a = [ 4, 1, 3, 2, 16, 9, 10, 14, 8, 7 ];
        auto h = heapify(a);
        h = heapify!"a < b"(a);
        assert(h.front == 16);
        assert(a == [ 16, 14, 10, 8, 7, 9, 3, 2, 4, 1 ]);
        auto witness = [ 16, 14, 10, 9, 8, 7, 4, 3, 2, 1 ];
        for (; !h.empty; h.removeFront(), witness.popFront())
        {
            assert(!witness.empty);
            assert(witness.front == h.front);
        }
        assert(witness.empty);
    }
    {
        int[] a = [ 4, 1, 3, 2, 16, 9, 10, 14, 8, 7 ];
        int[] b = new int[a.length];
        BinaryHeap!("a < b", int[]) h = BinaryHeap!("a < b", int[])(b, 0);
        foreach (e; a)
        {
            h.insert(e);
        }
        assert(b == [ 16, 14, 10, 8, 7, 3, 9, 1, 4, 2 ]);
    }
}

@system nothrow version(mir_test) unittest
{
    // Test range interface.
    import std.range.primitives: isInputRange;
    import mir.algorithm.iteration : equal;
    int[] a = [4, 1, 3, 2, 16, 9, 10, 14, 8, 7];
    auto h = heapify(a);
    static assert(isInputRange!(typeof(h)));
    assert((&h).equal([16, 14, 10, 9, 8, 7, 4, 3, 2, 1]));
}

@system nothrow version(mir_test) unittest // 15675
{
    import std.container.array : Array;

    Array!int elements = [1, 2, 10, 12];
    auto heap = heapify(elements);
    assert(heap.front == 12);
}

@system nothrow version(mir_test) unittest
{
    import mir.algorithm.iteration : equal;
    import std.internal.test.dummyrange;

    alias RefRange = DummyRange!(ReturnBy.Reference, Length.Yes, RangeType.Random);

    RefRange a;
    RefRange b;
    a.reinit();
    b.reinit();

    auto heap = heapify(a);
    foreach (ref elem; b)
    {
        heap.conditionalSwap(elem);
    }

    assert(equal(&heap, [ 5, 5, 4, 4, 3, 3, 2, 2, 1, 1]));
    assert(equal(b, [10, 9, 8, 7, 6, 6, 7, 8, 9, 10]));
}

/// Heap operations for random-access ranges
template HeapOps(alias less, Range)
{
    import mir.functional;
    import std.algorithm.mutation : swapAt;

    static assert(isRandomAccessRange!Range);
    static assert(hasLength!Range);
    static assert(hasSwappableElements!Range || hasAssignableElements!Range);

    alias lessFun = naryFun!less;

    /// template because of @@@12410@@@
    void heapSort()(Range r)
    {
        // If true, there is nothing to do
        if (r.length < 2) return;
        // Build Heap
        buildHeap(r);
        // Sort
        for (size_t i = r.length - 1; i > 0; --i)
        {
            r.swapAt(0, i);
            percolate(r, 0, i);
        }
    }

    /// template because of @@@12410@@@
    void buildHeap()(Range r)
    {
        immutable n = r.length;
        for (size_t i = n / 2; i-- > 0; )
        {
            siftDown(r, i, n);
        }
        assert(isHeap(r));
    }

    ///
    bool isHeap()(Range r)
    {
        size_t parent = 0;
        foreach (child; 1 .. r.length)
        {
            if (lessFun(r[parent], r[child])) return false;
            // Increment parent every other pass
            parent += !(child & 1);
        }
        return true;
    }

    /// Sifts down r[parent] (which is initially assumed to be messed up) so the
    /// heap property is restored for r[parent .. end].
    /// template because of @@@12410@@@
    void siftDown()(Range r, size_t parent, immutable size_t end)
    {
        for (;;)
        {
            auto child = (parent + 1) * 2;
            if (child >= end)
            {
                // Leftover left child?
                if (child == end && lessFun(r[parent], r[--child]))
                    r.swapAt(parent, child);
                break;
            }
            auto leftChild = child - 1;
            if (lessFun(r[child], r[leftChild])) child = leftChild;
            if (!lessFun(r[parent], r[child])) break;
            r.swapAt(parent, child);
            parent = child;
        }
    }

    /// Alternate version of siftDown that performs fewer comparisons, see
    /// https://en.wikipedia.org/wiki/Heapsort#Bottom-up_heapsort. The percolate
    /// process first sifts the parent all the way down (without comparing it
    /// against the leaves), and then a bit up until the heap property is
    /// restored. So there are more swaps but fewer comparisons. Gains are made
    /// when the final position is likely to end toward the bottom of the heap,
    /// so not a lot of sifts back are performed.
    /// template because of @@@12410@@@
    void percolate()(Range r, size_t parent, immutable size_t end)
    {
        immutable root = parent;

        // Sift down
        for (;;)
        {
            auto child = (parent + 1) * 2;

            if (child >= end)
            {
                if (child == end)
                {
                    // Leftover left node.
                    --child;
                    r.swapAt(parent, child);
                    parent = child;
                }
                break;
            }

            auto leftChild = child - 1;
            if (lessFun(r[child], r[leftChild])) child = leftChild;
            r.swapAt(parent, child);
            parent = child;
        }

        // Sift up
        for (auto child = parent; child > root; child = parent)
        {
            parent = (child - 1) / 2;
            if (!lessFun(r[parent], r[child])) break;
            r.swapAt(parent, child);
        }
    }
}
