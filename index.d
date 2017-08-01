Ddoc

$(P Generic Algorithm Collection.)

$(P The following table is a quick reference guide for which Mir Algorithm modules to
use for a given category of functionality.)

$(BOOKTABLE ,
    $(TR
        $(TH Modules)
        $(TH Description)
    )
    $(LEADINGROW Algorithms constructors, multidimensional arrays, iterators)
    $(TR $(TDNW $(MREF mir,ndslice)) $(TD Package))
    $(TR $(TDNW $(MREF mir,ndslice,algorithm)) $(TD Loop free programming))
    $(TR $(TDNW $(MREF mir,ndslice,allocation)) $(TD Allocation utilities))
    $(TR $(TDNW $(MREF mir,ndslice,chunks)) $(TD Multi-dimensional random access range with slicing))
    $(TR $(TDNW $(MREF mir,ndslice,concatenation)) $(TD Concatenation and padding))
    $(TR $(TDNW $(MREF mir,ndslice,dynamic)) $(TD Dynamic dimension manipulators))
    $(TR $(TDNW $(MREF mir,ndslice,field)) $(TD Field declarations))
    $(TR $(TDNW $(MREF mir,ndslice,iterator)) $(TD Iterator declarations))
    $(TR $(TDNW $(MREF mir,ndslice,ndfield)) $(TD NdField declarations))
    $(TR $(TDNW $(MREF mir,ndslice,slice)) $(TD Slice structure, basic constructors))
    $(TR $(TDNW $(MREF mir,ndslice,sorting)) $(TD Sorting utilities))
    $(TR $(TDNW 🔷 $(MREF mir,ndslice,topology) 🔷) $(TD Advanced ndslice constructors (key module).))
    $(TR $(TDNW $(MREF mir,ndslice,traits)) $(TD Multi-dimensional traits))
    $(LEADINGROW Finance)
    $(TR $(TDNW $(MREF mir,timeseries)) $(TD Time-series))
    $(LEADINGROW Math)
    $(TR $(TDNW $(MREF mir,math,common)) $(TD Common math functions))
    $(TR $(TDNW $(MREF mir,math,constant)) $(TD Constants))
    $(TR $(TDNW $(MREF mir,math,numeric)) $(TD Simple numeric algorithms))
    $(TR $(TDNW $(MREF mir,math,sum)) $(TD Various precise summation algorithms))
    $(LEADINGROW Interpolation)
    $(TR $(TDNW $(MREF mir,interpolation)) $(TD Interpolation algorithms))
    $(LEADINGROW Accessories)
    $(TR $(TDNW $(MREF mir,utility)) $(TD Everyday utilities))
    $(TR $(TDNW $(MREF mir,array,primitives)) $(TD Array range primitives with ndslice-like API))
    $(TR $(TDNW $(MREF mir,bitmanip)) $(TD Bit fields manipulations))
    $(TR $(TDNW $(MREF mir,conv)) $(TD Conversion utilities))
    $(TR $(TDNW $(MREF mir,functional)) $(TD Functions that manipulate other functions))
    $(TR $(TDNW $(MREF mir,primitives)) $(TD Templates used to check primitives))
)

Copyright: Copyright © 2016-, Ilya Yaroshenko.

Macros:
        TITLE=Mir Algorithm
        WIKI=Mir Algorithm
        DDOC_BLANKLINE=
        _=
