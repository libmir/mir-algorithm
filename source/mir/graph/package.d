/++
Basic routines to work with graphs.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2018-, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, graph, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/

module mir.graph;

import mir.math.common: optmath;

@optmath:

import mir.series;

import mir.functional: staticArray;

import mir.ndslice.iterator: SubSliceIterator, SlideIterator;

///
alias GraphIterator(I) = SubSliceIterator!(SlideIterator!(size_t*, 2, staticArray), I*);
///
alias Graph(I) = Slice!(GraphIterator!I);
///
alias GraphSeries(T, I) = Series!(T*, GraphIterator!I);

/++
Param:
    aaGraph = graph that is represented as associative array
Returns:
    A graph series composed of keys (sorted `.index`) and arrays of indeces (`.data`)
Complexity: `O(log(V) (V + E))`
+/
GraphSeries!(T, uint) graphSeries(T, Range)(in Range[T] aaGraph)
{
    import std.array: array;
    auto keys = aaGraph.byKey.array.sliced;
    import mir.ndslice.sorting;
    import mir.ndslice;
    sort(keys);
    size_t dataLength;
    foreach (ref v; aaGraph)
        dataLength += v.length;
    auto data = uninitSlice!uint(dataLength);
    auto components = uninitSlice!size_t(keys.length + 1);
    size_t dataIndex;
    // size_t componentIndex;

    foreach (i; 0 .. keys.length)
    {
        components[i] = dataIndex;
        foreach(ref elem; aaGraph[keys[i]])
        {
            import std.range: assumeSorted;
            auto index = keys.assumeSorted.lowerBound(elem).length;
            assert(index < keys.length, "graphSeries: aaGraph should contains keys for all vertixes");
            data[dataIndex++] = cast(uint) index;
        }
    }
    components[keys.length] = dataIndex; 

    return keys.series(components.pairwiseMapSubSlices(()@trusted {return data.ptr; }()));
}

///
pure version(mir_test) unittest
{
    auto gs = [
        "b" : ["a"],
        "a" : ["b", "c"],
        "c" : ["b"],
    ].graphSeries;

    assert (gs.index == ["a", "b", "c"]); // sorted
    assert (gs.data == [
        [1, 2], // a
        [0],    // b
        [1],    // c
    ]);
}
