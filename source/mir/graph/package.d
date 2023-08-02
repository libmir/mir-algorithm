/++
Basic routines to work with graphs.

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, graph, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/

module mir.graph;

import mir.math.common: fmamath;

import mir.series;
import mir.rc.array;
import mir.ndslice.iterator: ChopIterator;

///
alias GraphIterator(I = uint, J = size_t) = ChopIterator!(size_t*, uint*);
///
alias Graph(I = uint, J = size_t) = Slice!(GraphIterator!(I, J));
///
alias GraphSeries(T, I = uint, J = size_t) = Series!(T*, GraphIterator!(I, J));

///
alias RCGraphIterator(I = uint, J = size_t) = ChopIterator!(RCI!size_t, RCI!uint);
///
alias RCGraph(I = uint, J = size_t) = Slice!(RCGraphIterator!(I, J));
///
alias RCGraphSeries(T, I = uint, J = size_t) = Series!(RCI!T, RCGraphIterator!(I, J));

private static immutable exc_msg = "graphSeries: graph should contains keys for all vertixes";
version(D_Exceptions)
{
    private static immutable exception = new Exception(exc_msg);
}

/++
Params:
    aaGraph = graph that is represented as associative array
Returns:
    A graph series composed of keys (sorted `.index`) and arrays of indeces (`.data`)
Complexity: `O(log(V) (V + E))`
+/
@fmamath
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
            if (index >= keys.length)
            {
                version(D_Exceptions)
                    { import mir.exception : toMutable; throw exception.toMutable; }
                else
                    assert(0, exc_msg);
            }
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

/++
Params:
    graph = graph that is represented a series
Returns:
    A graph as an arrays of indeces
Complexity: `O(log(V) (V + E))`
+/
@fmamath
RCGraph!(I, J) rcgraph(I = uint, J = size_t, KeyIterator, RangeIterator)(Series!(KeyIterator, RangeIterator) graph)
{
    import mir.array.allocation: array;
    import mir.ndslice.sorting;
    import mir.ndslice;
    auto scopeGraph = graph.lightScope;
    auto keys = scopeGraph.index;
    auto graphData = scopeGraph.data;
    size_t dataLength;
    foreach (ref v; graphData)
        dataLength += v.length;
    auto data = rcslice!I(dataLength);
    auto components = rcslice!J(keys.length + 1);
    size_t dataIndex;

    foreach (i; 0 .. keys.length)
    {
        components[i] = cast(J) dataIndex;
        foreach(ref elem; graphData[i])
        {
            import mir.ndslice.sorting: transitionIndex;
            auto index = keys.transitionIndex(elem);
            if (index >= keys.length)
            {
                version(D_Exceptions)
                    { import mir.exception : toMutable; throw exception.toMutable; }
                else
                    assert(0, exc_msg);
            }
            data[dataIndex++] = cast(I) index;
        }
    }
    components[keys.length] = dataIndex; 
    return data._iterator.chopped(components);
}

///
@safe pure @nogc version(mir_test)
unittest
{
    import mir.series: series;

    static immutable keys = ["a", "b", "c"];
    static immutable data = [
        ["b", "c"],
        ["a"],
        ["b"],
    ];

    static immutable graphValue = [
        [1, 2], // a
        [0],    // b
        [1],    // c
    ];

    assert (series(keys, data).rcgraph == graphValue);
}
