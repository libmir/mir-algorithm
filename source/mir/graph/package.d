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
import mir.ndslice.iterator: ChopIterator;

///
alias GraphIterator(I = uint, J = size_t) = ChopIterator!(size_t*, uint*);
///
alias Graph(I = uint, J = size_t) = Slice!(GraphIterator!(I, J));
///
alias GraphSeries(T, I = uint, J = size_t) = Series!(T*, GraphIterator!(I, J));

/++
Param:
    aaGraph = graph that is represented as associative array
Returns:
    A graph series composed of keys (sorted `.index`) and arrays of indeces (`.data`)
Complexity: `O(log(V) (V + E))`
+/
GraphSeries!(T, I, J) graphSeries(I = uint, J = size_t, T, Range)(in Range[T] aaGraph)
{
    import mir.array.allocation: array;
    import mir.ndslice.sorting;
    import mir.ndslice;
    auto keys = aaGraph.byKey.array.sliced;
    sort(keys);
    size_t dataLength;
    foreach (ref v; aaGraph)
        dataLength += v.length;
    auto data = uninitSlice!I(dataLength);
    auto components = uninitSlice!J(keys.length + 1);
    size_t dataIndex;

    foreach (i; 0 .. keys.length)
    {
        components[i] = cast(J) dataIndex;
        foreach(ref elem; aaGraph[keys[i]])
        {
            import mir.ndslice.sorting: transitionIndex;
            auto index = keys.transitionIndex(elem);
            assert(index < keys.length, "graphSeries: aaGraph should contains keys for all vertixes");
            data[dataIndex++] = cast(I) index;
        }
    }
    components[keys.length] = dataIndex; 
    auto sliceable = (() @trusted => data.ptr)();
    return keys.series(sliceable.chopped(components));
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
