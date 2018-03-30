/++
$(H2 Multidimensional traits)

This is a submodule of $(MREF mir,ndslice).

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))

$(T2 isVector, Test if type is a one-dimensional slice.)
$(T2 isMatrix, Test if type is a two-dimensional slice.)
$(T2 isContiguousSlice, Test if type is a contiguous slice.)
$(T2 isCanonicalSlice, Test if type is a canonical slice.)
$(T2 isUniversalSlice, Test if type is a universal slice.)
$(T2 isContiguousVector, Test if type is a contiguous one-dimensional slice.)
$(T2 isUniversalVector, Test if type is a universal one-dimensional slice.)
$(T2 isContiguousMatrix, Test if type is a contiguous two-dimensional slice.)
$(T2 isCanonicalMatrix, Test if type is a canonical two-dimensional slice.)
$(T2 isUniversalMatrix, Test if type is a universal two-dimensional slice.)
)

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright $(COPYRIGHT) 2016-, Ilya Yaroshenko, John Hall
Authors:   John Hall


Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/

module mir.ndslice.traits;

import mir.ndslice.slice : Slice, SliceKind, Contiguous, Universal, Canonical;

/// Test if type is a one-dimensional slice.
enum bool isVector(T) = is(T : Slice!(kind, [1], Iterator), SliceKind kind, Iterator);
                                    
/// Test if type is a two-dimensional slice.
enum bool isMatrix(T) = is(T : Slice!(kind, [2], Iterator), SliceKind kind, Iterator);
                                    
/// Test if type is a contiguous slice.
enum bool isContiguousSlice(T) = is(T : Slice!(Contiguous, packs, Iterator), size_t[] packs, Iterator);
                                            
/// Test if type is a canonical slice.
enum bool isCanonicalSlice(T) = is(T : Slice!(Canonical, packs, Iterator), size_t[] packs, Iterator);
                                            
/// Test if type is a universal slice.
enum bool isUniversalSlice(T) = is(T : Slice!(Universal, packs, Iterator), size_t[] packs, Iterator);
                                            
/// Test if type is a contiguous one-dimensional slice.
enum bool isContiguousVector(T) = is(T : Slice!(Contiguous, [1], Iterator), Iterator);
                                                    
/// Test if type is a universal one-dimensional slice.
enum bool isUniversalVector(T) = is(T : Slice!(Universal, [1], Iterator), Iterator);
                                                    
/// Test if type is a contiguous two-dimensional slice.
enum bool isContiguousMatrix(T) = is(T : Slice!(Contiguous, [2], Iterator), Iterator);
                                                    
/// Test if type is a canonical two-dimensional slice.
enum bool isCanonicalMatrix(T) = is(T : Slice!(Canonical, [2], Iterator), Iterator);
                                                    
/// Test if type is a universal two-dimensional slice.
enum bool isUniversalMatrix(T) = is(T : Slice!(Universal, [2], Iterator), Iterator);

///
@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : ContiguousVector;

    alias S1 = ContiguousVector!int;
    static assert(isContiguousVector!S1);
    static assert(!isUniversalVector!S1);
    
    static assert(!isContiguousMatrix!S1);
    static assert(!isCanonicalMatrix!S1);
    static assert(!isUniversalMatrix!S1);
    
    static assert(isVector!S1);
    static assert(!isMatrix!S1);
    
    static assert(isContiguousSlice!S1);
    static assert(!isCanonicalSlice!S1);
    static assert(!isUniversalSlice!S1);
}

@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : UniversalVector;

    alias S2 = UniversalVector!float;
    static assert(!isContiguousVector!S2);
    static assert(isUniversalVector!S2);
    
    static assert(!isContiguousMatrix!S2);
    static assert(!isCanonicalMatrix!S2);
    static assert(!isUniversalMatrix!S2);
    
    static assert(isVector!S2);
    static assert(!isMatrix!S2);
    
    static assert(!isContiguousSlice!S2);
    static assert(!isCanonicalSlice!S2);
    static assert(isUniversalSlice!S2);
}

@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : ContiguousMatrix;

    alias S3 = ContiguousMatrix!byte;
    static assert(!isContiguousVector!S3);
    static assert(!isUniversalVector!S3);
    
    static assert(isContiguousMatrix!S3);
    static assert(!isCanonicalMatrix!S3);
    static assert(!isUniversalMatrix!S3);
    
    static assert(!isVector!S3);
    static assert(isMatrix!S3);
    
    static assert(isContiguousSlice!S3);
    static assert(!isCanonicalSlice!S3);
    static assert(!isUniversalSlice!S3);
}

@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : CanonicalMatrix;

    alias S4 = CanonicalMatrix!uint;
    static assert(!isContiguousVector!S4);
    static assert(!isUniversalVector!S4);
    
    static assert(!isContiguousMatrix!S4);
    static assert(isCanonicalMatrix!S4);
    static assert(!isUniversalMatrix!S4);
    
    static assert(!isVector!S4);
    static assert(isMatrix!S4);
    
    static assert(!isContiguousSlice!S4);
    static assert(isCanonicalSlice!S4);
    static assert(!isUniversalSlice!S4);
}

@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : UniversalMatrix;

    alias S5 = UniversalMatrix!double;
    static assert(!isContiguousVector!S5);
    static assert(!isUniversalVector!S5);
    
    static assert(!isContiguousMatrix!S5);
    static assert(!isCanonicalMatrix!S5);
    static assert(isUniversalMatrix!S5);
    
    static assert(!isVector!S5);
    static assert(isMatrix!S5);
    
    static assert(!isContiguousSlice!S5);
    static assert(!isCanonicalSlice!S5);
    static assert(isUniversalSlice!S5);
}

@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : ContiguousSlice;

    alias S6 = ContiguousSlice!(3, ubyte);
    
    static assert(!isContiguousVector!S6);
    static assert(!isUniversalVector!S6);
    
    static assert(!isContiguousMatrix!S6);
    static assert(!isCanonicalMatrix!S6);
    static assert(!isUniversalMatrix!S6);
    
    static assert(!isVector!S6);
    static assert(!isMatrix!S6);
    
    static assert(isContiguousSlice!S6);
    static assert(!isCanonicalSlice!S6);
    static assert(!isUniversalSlice!S6);
}

@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : CanonicalSlice;

    alias S7 = CanonicalSlice!(3, real);
    
    static assert(!isContiguousVector!S7);
    static assert(!isUniversalVector!S7);
    
    static assert(!isContiguousMatrix!S7);
    static assert(!isCanonicalMatrix!S7);
    static assert(!isUniversalMatrix!S7);
    
    static assert(!isVector!S7);
    static assert(!isMatrix!S7);
    
    static assert(!isContiguousSlice!S7);
    static assert(isCanonicalSlice!S7);
    static assert(!isUniversalSlice!S7);
}

@safe pure nothrow @nogc 
version(mir_test) unittest
{
    import mir.ndslice.slice : UniversalSlice;

    alias S8 = UniversalSlice!(3, long);
    
    static assert(!isContiguousVector!S8);
    static assert(!isUniversalVector!S8);
    
    static assert(!isContiguousMatrix!S8);
    static assert(!isCanonicalMatrix!S8);
    static assert(!isUniversalMatrix!S8);
    
    static assert(!isVector!S8);
    static assert(!isMatrix!S8);
    
    static assert(!isContiguousSlice!S8);
    static assert(!isCanonicalSlice!S8);
    static assert(isUniversalSlice!S8);
}
