Ddoc

$(P Generic Algorithm Collection.)

$(P The following table is a quick reference guide for which Mir Algorithm modules to
use for a given category of functionality.)

$(BOOKTABLE ,
    $(TR
        $(TH Modules)
        $(TH Description)
    )
    $(LEADINGROW NDarrays and Algorithms)
    $(TR $(TDNW $(MREF mir,ndslice)★) $(TD Package for ndarrays and iteration algorithms.))
    $(LEADINGROW Containers)
    $(TR $(TDNW $(MREF mir,series)★) $(TD Generic series suitable for time-series or semi-immutable ordered maps with CPU cache friendly binary search.))
    $(TR $(TDNW $(MREF mir,container,binaryheap)★) $(TD BetterC rework of `std.container.binaryheap`.))
    $(LEADINGROW Graphs)
    $(TR $(TDNW $(MREF mir,graph)) $(TD Basic routines to work with graphs))
    $(TR $(TDNW $(MREF mir,graph,tarjan)★) $(TD Tarjan's strongly connected components algorithm))
    $(LEADINGROW Interpolation)
    $(TR $(TDNW $(MREF mir,interpolate)★) $(TD Interpolation algorithms))
    $(LEADINGROW Combinatrorics)
    $(TR $(TDNW $(MREF mir,combinatorics)★) $(TD Combinations, combinations with repeats, cartesian power, permutations.))
    $(LEADINGROW Interconnection with other languages)
    $(TR $(TDNW $(MREF mir,ndslice,connect,cpp)) $(TD Definitions suitable for `extern(C++)` functions))
    $(TR $(TDNW $(MREF mir,ndslice,connect,cpython)) $(TD Utilities for $(HTTPS docs.python.org/3/c-api/buffer.html, Python Buffer Protocol)))
    $(LEADINGROW Math)
    $(TR $(TDNW $(MREF mir,math)) $(TD Package))
    $(TR $(TDNW $(MREF mir,math,common)★) $(TD Common math functions and fp-math compiler optimization attributes))
    $(TR $(TDNW $(MREF mir,math,constant)) $(TD Constants))
    $(TR $(TDNW $(MREF mir,math,numeric)) $(TD Simple numeric algorithms))
    $(TR $(TDNW $(MREF mir,math,sum)) $(TD Various precise summation algorithms))
    $(LEADINGROW Accessories)
    $(TR $(TDNW $(MREF mir,utility)) $(TD Everyday utilities))
    $(TR $(TDNW $(MREF mir,array,primitives)) $(TD Array range primitives with ndslice-like API))
    $(TR $(TDNW $(MREF mir,bitmanip)) $(TD Bit fields manipulations))
    $(TR $(TDNW $(MREF mir,conv)) $(TD Conversion utilities))
    $(TR $(TDNW $(MREF mir,functional)) $(TD Functions that manipulate other functions))
    $(TR $(TDNW $(MREF mir,primitives)) $(TD Templates used to check primitives))
    $(TR $(TDNW $(MREF mir,range)) $(TD Ranges))
)

Copyright: Copyright © 2016-, Ilya Yaroshenko.

Macros:
        TITLE=Mir Algorithm
        WIKI=Mir Algorithm
        DDOC_BLANKLINE=
        _=
