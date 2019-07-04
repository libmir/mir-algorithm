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
    $(TR $(TDNW $(MREF mir,range)) $(TD Additoinal primitive ranges. See also $(MREF mir,ndslice), which contains a lot of range constructos.))
    $(TR $(TDNW $(MREF mir,algorithm,setops)) $(TD Mir & BetterC rework of Phobos.))
    $(TR $(TDNW $(MREF mir,algorithm,iteration)) $(TD Mir & BetterC rework of Phobos.))
    $(LEADINGROW Math)
    $(TR $(TDNW $(MREF mir,numeric)) $(TD Basic numeric optimisations))
    $(TR $(TDNW $(MREF mir,math,numeric)) $(TD Simple numeric algorithms))
    $(TR $(TDNW $(MREF mir,math,sum)★) $(TD Various precise summation algorithms))
    $(TR $(TDNW $(MREF mir,math,constant)) $(TD Math constants))
    $(LEADINGROW Reference counting)
    $(TR $(TDNW $(MREF mir,rc,array)) $(TD Thread safe reference count array and the iterator to adopt it to ndslice.))
    $(TR $(TDNW $(MREF mir,rc,ptr)) $(TD Thread safe reference count pointer for strucs and objects.))
    $(LEADINGROW Containers)
    $(TR $(TDNW $(MREF mir,series)★) $(TD Generic series suitable for time-series or semi-immutable ordered maps with CPU cache friendly binary search.))
    $(TR $(TDNW $(MREF mir,container,binaryheap)★) $(TD Mir & BetterC rework of Phobos.))
    $(LEADINGROW Graphs)
    $(TR $(TDNW $(MREF mir,graph)) $(TD Basic routines to work with graphs))
    $(TR $(TDNW $(MREF mir,graph,tarjan)★) $(TD Tarjan's strongly connected components algorithm))
    $(LEADINGROW Interpolation)
    $(TR $(TDNW $(MREF mir,interpolate)★) $(TD Interpolation algorithms))
    $(LEADINGROW Combinatrorics)
    $(TR $(TDNW $(MREF mir,combinatorics)★) $(TD Combinations, combinations with repeats, cartesian power, permutations.))
    $(LEADINGROW Interconnection with other languages)
    $(TR $(TDNW $(MREF mir,ndslice,connect,cpython)) $(TD Utilities for $(HTTPS docs.python.org/3/c-api/buffer.html, Python Buffer Protocol)))
    $(LEADINGROW Accessories)
    $(TR $(TDNW $(MREF mir,small_string)) Generic Small Strings)
    $(TR $(TDNW $(MREF mir,array,allocation)) $(TD `std.array` reworked for Mir))
    $(TR $(TDNW $(MREF mir,range)) $(TD Ranges))
)

Copyright: Copyright © 2016-, Ilya Yaroshenko.

Macros:
        TITLE=Mir Algorithm
        WIKI=Mir Algorithm
        DDOC_BLANKLINE=
        _=
