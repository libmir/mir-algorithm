/++
This is a submodule of $(MREF mir,graph).

Tarjan's strongly connected components algorithm.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2018-, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/

module mir.graph.tarjan;

import std.traits;

import mir.math.common: optmath;

@optmath:


/++
Classic Tarjan's strongly connected components algorithm.

Tarjan's algorithm is an algorithm in graph theory for finding the strongly connected components of a graph.
It runs in linear time, matching the time bound for alternative methods including Kosaraju's algorithm and the path-based strong component algorithm.

The implementation is loop based. It does not use recursion and does not have stack overflow issues.

Complexity: worst-case `O(|V| + |E|)`.

Params:
    graph = components (ndslice) sorted in the direction of traversal of the graph. Each component is an array of indeces.
Returns:
    components (ndslice of arrays of indexes)

Note:
    The implementation returns components sorted in the direction of traversal of the graph.
    $(NOTE Most of other Tarjan implementations returns reverse order.)

See_also:
    $(SUBREF utility, graph)
+/
pragma(inline, false)
auto tarjan(G, I = Unqual!(ForeachType!(ForeachType!G)))(G graph)
    if (isUnsigned!I)
{
    import mir.utility: min;

    static if (I.sizeof >= uint.sizeof)
        alias S = size_t;
    else
        alias S = uint;

    enum undefined = I.max;

    static struct IndexNode
    {
        I index;
        I lowlink;

@property:

        bool isRoot()()
        {
            return index == lowlink;
        }

        bool isUndefined()()
        {
            return index == undefined;
        }
    }

    static struct LoopNode
    {
        union
        {
            struct
            {
                I i;
                I j;
            }
            S index;
        }
    }

    bool[] onStack = new bool[graph.length];
    I[] stack;
    IndexNode[] indeces;
    LoopNode[] loopStack;
    I index;
    sizediff_t stackIndex;
    sizediff_t backStackIndex = graph.length;
    sizediff_t componentBackStackIndex = graph.length + 1;

    if (__ctfe)
    {
        stack = new I[graph.length];
        indeces = new IndexNode[graph.length];
        loopStack = new LoopNode[componentBackStackIndex];
    }
    else
    {
        () @trusted {
            import std.array: uninitializedArray;

            stack = uninitializedArray!(I[])(graph.length);
            indeces = uninitializedArray!(IndexNode[])(graph.length);
            loopStack = uninitializedArray!(LoopNode[])(componentBackStackIndex);
        } ();
    }

    foreach(ref node; indeces)
        node.index = undefined;

    foreach(size_t v; 0u .. graph.length)
    {
        if (indeces[v].isUndefined)
        {
            sizediff_t loopStackIndex;
        loop:
            // Set the depth index for v to the smallest unused index
            indeces[v].index = cast(I) index;
            indeces[v].lowlink = cast(I) index;
            index++;
            stack[stackIndex++] = cast(I) v;
            onStack[v] = true;

            // Consider successors of v
            auto e = graph[v];
            I w;
            size_t wi;

            for (; wi < e.length; wi++)
            {
                w = e[wi];
                if (onStack[w])
                {
                    // Successor w is in stack S and hence in the current SCC
                    // If w is not on stack, then (v, w) is a cross-edge in the DFS tree and must be ignored
                    // Note: The next line may look odd - but is correct.
                    // It says w.index not w.lowlink; that is deliberate and from the original paper
                    indeces[v].lowlink = min(indeces[v].lowlink, indeces[w].index);
                    continue;
                }
                if (indeces[w].isUndefined)
                {
                    // Successor w has not yet been visited; recurse on it
                    // strongconnect(w)
                    assert(loopStackIndex < loopStack.length);
                    loopStack[loopStackIndex] = LoopNode(cast(I) v, cast(I) wi);
                    ++loopStackIndex;
                    assert(componentBackStackIndex > loopStackIndex);
                    v = e[wi];
                    goto loop;
                retRec:
                    v = loopStack[loopStackIndex].i;
                    wi = loopStack[loopStackIndex].j;
                    e = graph[v];
                    w = e[wi];
                    indeces[v].lowlink = min(indeces[v].lowlink, indeces[w].lowlink);
                }
            }

            // If v is a root node, pop the stack and generate an SCC
            if (indeces[v].isRoot)
            {
                // start a new strongly connected component
                do
                {
                    assert(stackIndex > 0);
                    assert(backStackIndex > 0);
                    // add w to current strongly connected component
                    --backStackIndex;
                    --stackIndex;
                    w = stack[backStackIndex] = stack[stackIndex];
                    onStack[w] = false;
                }
                while (w != v);
                
                // output the current strongly connected component
                assert(componentBackStackIndex > loopStackIndex);
                --componentBackStackIndex;
                loopStack[componentBackStackIndex].index = cast(S) backStackIndex;
            }
            if (--loopStackIndex >= 0)
                goto retRec;
        }
    }

    S[] pairwiseIndex;
    if (__ctfe)
    {
        pairwiseIndex = new S[graph.length - componentBackStackIndex + 1];
    }
    else
    {
        () @trusted {
            import std.array: uninitializedArray;
            pairwiseIndex = uninitializedArray!(S[])(graph.length + 1 - componentBackStackIndex + 1);
        } ();
    }
    foreach (i, ref e; loopStack[componentBackStackIndex .. $])
    {
        pairwiseIndex[i] = e.index;
    }
    pairwiseIndex[$ - 1] = cast(I) graph.length;

    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: pairwiseMapSubSlices;
    return pairwiseIndex.sliced.pairwiseMapSubSlices(()@trusted {return stack.ptr; }());
}

/++
------
        4 <- 5 <- 6 -------> 7 -> 8 -> 11
        |    ^   ^           ^    |
        v    |   |           |    |
  0 -> 1 -> 2 -> 3 -> 10     9 <---
------
+/
pure version(mir_test) unittest
{
    import mir.graph;
    import mir.graph.tarjan;

    GraphSeries!(string, uint) gs = [
        "00": ["01"],
        "01": ["02"],
        "02": ["05", "03"],
        "03": ["06", "10"],
        "04": ["01"],
        "05": ["04"],
        "06": ["05", "07"],
        "07": ["08"],
        "08": ["09", "11"],
        "09": ["07"],
        "10": [],
        "11": [],
    ].graphSeries;

    auto components = gs.data.tarjan;

    assert(components == [
        [0],
        [1, 2, 5, 4, 3, 6],
        [10],
        [7, 8, 9],
        [11]]);
}

/++
Tests that the graph `0 -> 1 -> 2 -> 3 -> 4` returns 4 components.
+/
pure version(mir_test) unittest
{
    import mir.graph;
    import mir.graph.tarjan;

    GraphSeries!(char, uint) gs = [
        'a': ['b'],
        'b': ['c'],
        'c': ['d'],
        'd': ['q'],
        'q': [],
    ].graphSeries;

    auto scc = gs.data.tarjan;

    assert(scc == [[0], [1], [2], [3], [4]]);
}

/++
----
 0 <- 2 <-- 5 <--> 6
 |  ^ ^ ^___       
 v_|  |     |      _ 
 1 <- 3 <-> 4 <-- 7_|
----
+/
pure version(mir_test) unittest
{
    import mir.graph;
    import mir.graph.tarjan;

    auto gs = [
        0: [1],
        1: [2],
        2: [0],
        3: [1, 2, 4],
        4: [3, 2],
        5: [2, 6],
        6: [5],
        7: [4, 7],
    ].graphSeries;

    auto components = gs.data.tarjan;

    assert(components == [
        [7],
        [5, 6],
        [3, 4],
        [0, 1, 2],
	]);
}

/++
-----
 2 <-> 1
 |    ^
 v_0 /
   
-----
+/
pure version(mir_test) unittest
{
    import mir.graph;
    import mir.graph.tarjan;

    auto gs = [
        0: [1],
        1: [2],
        2: [0, 1],
    ].graphSeries;

    auto components = gs.data.tarjan;

    assert(components == [[0, 1, 2]]);
}

/++
Tests that a strongly connected graph, where components have
to get through previously visited components to get to the
graph root works properly

This test demonstrates a hard to detect bug, where vertices
were being marked 'off-stack' after they were first visited,
not when they were actually removed from the stack
+/
pure version(mir_test) unittest
{
    import mir.graph;
    import mir.graph.tarjan;

    auto root = 0;
    auto lvl1 = [1,2,3,4,5,6,7,8,9,10];
    auto lvl2 = [11,12,13,14,15,16,17,18,19,20];

    int[][int] aar;
    aar[root] = lvl1;
    foreach(int v; lvl1)
        aar[v] = lvl2;
    foreach(int v; lvl2)
        aar[v] = [root];

    auto gs = aar.graphSeries;

    auto components = gs.data.tarjan;

    assert(components == [[root] ~ [lvl1[0]] ~ lvl2 ~ lvl1[1 .. $]]);
}
