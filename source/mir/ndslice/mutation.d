/++
$(H2 Multidimensional mutation algorithms)

This is a submodule of $(MREF mir,ndslice).

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
$(T2 transposeInPlace, Transposes square matrix in place.)
)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.mutation;

import mir.ndslice.algorithm: eachUploPair;
import mir.utility: swap;

deprecated("use eachUploPair!swap instead")
alias transposeInPlace = eachUploPair!swap;
