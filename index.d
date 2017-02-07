Ddoc

$(P Generic Algorithm Collection.)

$(P The following table is a quick reference guide for which Mir Algorithm modules to
use for a given category of functionality.)

$(BOOKTABLE ,
    $(TR
        $(TH Modules)
        $(TH Description)
    )
    $(LEADINGROW Multidimensional ndslices, iterators, and algorithms)
    $(TR
        $(TDNW $(MREF mir,ndslice))
        $(TD Package)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,slice))
        $(TD Slice structure, basic constructors)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,allocation))
        $(TD Allocation utilities)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,topology))
        $(TD Advanced constructors, SliceKind conversion utilities)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,algorithm))
        $(TD Loop free programming)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,dynamic))
        $(TD Dynamic dimension manipulators)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,sorting))
        $(TD Sorting utilities)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,iterator))
        $(TD Iterator declarations)
    )
    $(TR
        $(TDNW $(MREF mir,ndslice,field))
        $(TD Field declarations)
    )
    $(LEADINGROW Accessories)
    $(TR
        $(TDNW $(MREF mir,conv))
        $(TD Conversion utilities)
    )
    $(TR
        $(TDNW $(MREF mir,functional))
        $(TD Functions that manipulate other functions)
    )
    $(TR
        $(TDNW $(MREF mir,primitives))
        $(TD Templates used to check primitives)
    )
    $(TR
        $(TDNW $(MREF mir,utility))
        $(TD Everyday utilities)
    )
)

Copyright: Copyright © 2016-, Ilya Yaroshenko.

Macros:
        TITLE=Mir Algorithm
        WIKI=Mir Algorithm
        DDOC_BLANKLINE=
        _=
