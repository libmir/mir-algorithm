Ddoc

$(P Generic Algorithm Collection.)

$(P The following table is a quick reference guide for which Mir Algorithm modules to
use for a given category of functionality.)

$(BOOKTABLE ,
    $(TR
        $(TH Modules)
        $(TH Description)
    )
    $(LEADINGROW Accessories)
    $(TR $(TDNW $(MREF mir,variant)) $(TD Variant Type (aka Algebraic Type) with clever member access))
    $(TR $(TDNW $(MREF mir,exception)) $(TD @nogc MirException with formatting))
    $(TR $(TDNW $(MREF mir,format)) $(TD @nogc Formatting Utilities))
    $(TR $(TDNW $(MREF mir,parse)) $(TD @nogc Parsing Utilities))
    $(TR $(TDNW $(MREF mir,small_array)) $(TD Generic Small Arrays))
    $(TR $(TDNW $(MREF mir,small_string)) $(TD Generic Small Strings))
    $(TR $(TDNW $(MREF mir,array,allocation)) $(TD `std.array` reworked for Mir))
    $(TR $(TDNW $(MREF mir,range)) $(TD Ranges))
    $(TR $(TDNW $(MREF mir,serde)) $(TD Utilities for serialization libraries ))
    $(LEADINGROW Date and time)
    $(TR $(TDNW $(MREF mir,date)) $(TD Fast BetterC Date type with Boost ABI and mangling compatability))
    $(LEADINGROW NDarrays and Algorithms)
    $(TR $(TDNW $(MREF mir,ndslice)★) $(TD Package for ndarrays and iteration algorithms.))
    $(TR $(TDNW $(MREF mir,range)) $(TD Additoinal primitive ranges. See also $(MREF mir,ndslice), which contains a lot of range constructos.))
    $(TR $(TDNW $(MREF mir,algorithm,setops)) $(TD Mir & BetterC rework of Phobos.))
    $(TR $(TDNW $(MREF mir,algorithm,iteration)) $(TD Mir & BetterC rework of Phobos.))
    $(LEADINGROW Math)
    $(TR $(TDNW $(MREF mir,numeric)) $(TD Basic numeric optimisations))
    $(TR $(TDNW $(MREF mir,math,numeric)) $(TD Simple numeric algorithms))
    $(TR $(TDNW $(MREF mir,math,sum)) $(TD Various precise summation algorithms))
    $(TR $(TDNW $(MREF mir,math,stat)) $(TD Basic API for statistics))
    $(TR $(TDNW $(MREF mir,polynomial)) $(TD Polynomial ref-counted structure))
    $(TR $(TDNW $(MREF mir,interpolate)★) $(TD Interpolation algorithms))
    $(LEADINGROW Reference counting)
    $(TR $(TDNW $(MREF mir,rc)) $(TD Reference counting package and RC conversion utilities.))
    $(TR $(TDNW $(MREF mir,rc,array)) $(TD Thread safe reference count array and the iterator to adopt it to ndslice.))
    $(TR $(TDNW $(MREF mir,rc,ptr)) $(TD Thread safe reference count pointer with polymorphism support for strucs and objects.))
    $(TR $(TDNW $(MREF mir,rc,slim_ptr)) $(TD Thread safe reference count pointer for strucs and objects.))
    $(LEADINGROW Containers)
    $(TR $(TDNW $(MREF mir,series)★) $(TD Generic series suitable for time-series or semi-immutable ordered maps with CPU cache friendly binary search.))
    $(TR $(TDNW $(MREF mir,container,binaryheap)★) $(TD Mir & BetterC rework of Phobos.))
    $(TR $(TDNW $(MREF mir,appender)) $(TD Scoped Buffer.))
    $(LEADINGROW Graphs)
    $(TR $(TDNW $(MREF mir,graph)) $(TD Basic routines to work with graphs))
    $(TR $(TDNW $(MREF mir,graph,tarjan)★) $(TD Tarjan's strongly connected components algorithm))
    $(LEADINGROW Big Numbers (partial implementation))
    $(TR $(TDNW $(MREF mir,bignum, decimal)) $(TD Stack-allocated decimal type))
    $(TR $(TDNW $(MREF mir,bignum, fixed)) $(TD Stack-allocated fixed length unsigned integer type (like 256bit integers).))
    $(TR $(TDNW $(MREF mir,bignum, fp)) $(TD Stack-allocated fixed length software floating point type.))
    $(TR $(TDNW $(MREF mir,bignum, integer)) $(TD Stack-allocated integer type.))
    $(TR $(TDNW $(MREF mir,bignum, low_level_view)) $(TD Low-level universal number representation formats.))
    $(LEADINGROW Combinatrorics)
    $(TR $(TDNW $(MREF mir,combinatorics)★) $(TD Combinations, combinations with repeats, cartesian power, permutations.))
    $(LEADINGROW Interconnection with other languages)
    $(TR $(TDNW $(MREF mir,ndslice,connect,cpython)) $(TD Utilities for $(HTTPS docs.python.org/3/c-api/buffer.html, Python Buffer Protocol)))
)

Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments

Macros:
        TITLE=Mir Algorithm
        WIKI=Mir Algorithm
        DDOC_BLANKLINE=
        _=
