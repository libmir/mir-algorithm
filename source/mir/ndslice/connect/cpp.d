/++
This is a submodule of $(MREF mir, ndslice).

The module provides wrappers for $(SUBREF slice, Slice) that
can be used as arguments for `extern(C++)` functions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
STD = $(TD $(SMALL $0))
+/
module mir.ndslice.connect.cpp;

/++
CppSlice definition. It is not shown in the docs because of a DDOC bug.
See also C++ $(HTTPS github.com/libmir/mir-algorithm/blob/master/include/ndslice.h, ndslice header).
+/
unittest
{
    // extern(C++, ndslice) - ndslice namespace
    struct CppSlice(Iterator, size_t N = 1, Kind kind = Contiguous)
    {extern(D):
        ///
        Slice!(Iterator, N, kind) _slice;
        ///
        alias _slice this;
        ///
        this()(Slice!(Iterator, N, kind) slice)
        {
            this._slice = slice;
        }
    }
}

///
unittest
{
    static extern(C++) void fillEye(CppSlice!(double*, 2) matrix)
    {
        import mir.ndslice.topology: diagonal;
        matrix[] = 0;
        matrix.diagonal[] = 1;
    }

    import mir.ndslice.allocation;

    auto mat = stdcUninitSlice!double(2, 3).cppSlice;
    fillEye(mat);
    mat.stdcFreeSlice;
}

public import mir.ndslice.slice: Kind, Universal, Contiguous, Canonical;
import mir.ndslice.slice;

/// Converts $(SUBREF _slice, Slice) to appropriate $(LREF CppSlice) type.
CppSlice!(Iterator, N, kind) cppSlice(Iterator, size_t N, Kind kind)(Slice!(Iterator, N, kind) slice)
{
    return typeof(return)(slice);
}

/// Wrapper for C++ mangling
extern(C++, ndslice) struct CppSlice(Iterator, size_t N = 1, Kind kind = Contiguous)
{extern(D):
    ///
    Slice!(Iterator, N, kind) _slice;
    ///
    alias _slice this;
    ///
    this()(Slice!(Iterator, N, kind) slice)
    {
        this._slice = slice;
    }
}
