/+
$(H2 Multidimensional iteration algorithms)

This is a submodule of $(MREF mir,ndslice).


All operators are suitable to change slices using `ref` argument qualification in a function declaration.
Note, that string lambdas in Mir are `auto ref` functions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-2018, Ilya Yaroshenko, 2018-, Mir community
Authors:   Ilya Yaroshenko, John Michael Hall

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/

deprecated("import mir.algorithm.iteration instead")
module mir.ndslice.algorithm;

public import mir.algorithm.iteration;
