Ddoc

$(P Professional Random Number Generators.)

$(P The following table is a quick reference guide for which Mir Random modules to
use for a given category of functionality.)

$(BOOKTABLE ,
    $(TR
        $(TH Modules)
        $(TH Description)
    )
    $(LEADINGROW Basic API)
    $(TR
        $(TDNW $(MREF mir,algorithm))
        $(TD Basic API to generate algorithm numbers. Contains generic
            $(REF_ALTTEXT $(TT rand), rand, mir, algorithm)
            function that generates real, integral, boolean, and enumerated uniformly distributed values.
            Publicly includes $(MREF mir,algorithm,engine).)
    )
)

Copyright: Copyright © 2016-, Ilya Yaroshenko.

Macros:
        TITLE=Mir Random
        WIKI=Mir Random
        DDOC_BLANKLINE=
        _=