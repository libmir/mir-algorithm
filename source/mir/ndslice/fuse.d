/++
This is a submodule of $(MREF mir,ndslice).

Allocation routines that construct ndslices from ndranges.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2018-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

See_also: $(SUBMODULE concatenation) submodule.

Macros:
SUBMODULE = $(MREF_ALTTEXT $1, mir, ndslice, $1)
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.fuse;

import mir.ndslice.slice;
import mir.primitives;
import mir.internal.utility;
import std.traits;
import std.meta;

import mir.math.common: optmath;

@optmath:

/++
Fuses ndrange `r` into GC-allocated ndslice. Can be used to join rows or columns into a matrix.

Params:
    Dimensions = (optional) indexes of dimensions to be brought to the first position
Returns:
    ndslice
+/
template fuse(Dimensions...)
{
    import mir.ndslice.internal: isSize_t, toSize_t;
    static if (!allSatisfy!(isSize_t, Dimensions))
        alias fuse = .fuse!(staticMap!(toSize_t, Dimensions));
    else
    /++
    Params:
        r = parallelotope (ndrange) with length/shape and input range primitives.
    +/
    @optmath Slice!(FuseElementType!NDRange*, fuseDimensionCount!NDRange) fuse(NDRange)(NDRange r)
        if (hasShape!NDRange)
    {
        import mir.conv: emplaceRef;
        import mir.algorithm.iteration: each;
        import mir.ndslice.allocation;
        auto shape = fuseShape(r);
        alias T = FuseElementType!NDRange;
        alias UT = Unqual!T;
        alias R = typeof(return);
        Slice!(UT*, fuseDimensionCount!NDRange) ret;
        static if (Dimensions.length)
        {
            import mir.ndslice.topology: iota;
            import mir.ndslice.dynamic: transposed, completeTranspose;
            enum perm = completeTranspose!(shape.length)([Dimensions]);
            size_t[shape.length] shapep;
            foreach(i; Iota!(shape.length))
                shapep[i] = shape[perm[i]];
            // enum iperm = perm.length.iota[completeTranspose!(shape.length)([Dimensions])[].sliced].slice;
            alias InverseDimensions = aliasSeqOf!(
                (size_t[] perm){
                    auto ar = new size_t[perm.length];
                    ar.sliced[perm.sliced] = perm.length.iota;
                    return ar;
                }(perm)
            );
            if (__ctfe)
            {
                ret = shapep.slice!UT;
                ret.transposed!InverseDimensions.each!"a = b"(r);
            }
            else
            {
                ret = shapep.uninitSlice!UT;
                ret.transposed!InverseDimensions.each!(emplaceRef!T)(r);
            }
        }
        else
        {
            if (__ctfe)
            {
                ret = shape.slice!UT;
                ret.each!"a = b"(r);
            }
            else
            {
                ret = shape.uninitSlice!UT;
                ret.each!(emplaceRef!T)(r);
            }
        }
        return R(ret._structure, (() @trusted => cast(T*)ret._iterator)());
    }
}

///
unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;
    import mir.ndslice.slice : Contiguous, Slice;

    enum ror = [
            [0, 1, 2, 3],
            [4, 5, 6, 7],
            [8, 9,10,11]];

    //  0  1  2  3
    //  4  5  6  7
    //  8  9 10 11
    auto matrix = ror.fuse;

    assert(matrix == [3, 4].iota);
    static assert(ror.fuse == [3, 4].iota); // CTFE-able
    // matrix is contiguos
    static assert(is(typeof(matrix) == Slice!(int*, 2)));
}

/// Transposed
unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;
    import mir.ndslice.dynamic: transposed;
    import mir.ndslice.slice : Contiguous, Slice;

    enum ror = [
        [0, 1, 2, 3],
        [4, 5, 6, 7],
        [8, 9,10,11]];

    //  0  4  8
    //  1  5  9
    //  2  6 10
    //  3  7 11
    
    // `!1` brings dimensions under index 1 to the front (0 index).
    auto matrix = ror.fuse!1;

    assert(matrix == [3, 4].iota.transposed!1);
    // TODO: CTFE
    // static assert(ror.fuse!1 == [3, 4].iota.transposed!1); // CTFE-able
    // matrix is contiguos
    static assert(is(typeof(matrix) == Slice!(int*, 2)));
}


/// 3D
unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;
    import mir.ndslice.dynamic: transposed;

    auto ror =
      [[[ 0, 1, 2, 3],
        [ 4, 5, 6, 7]],
       [[ 8, 9,10,11],
        [12,13,14,15]]];

    auto nd = [2, 2, 4].iota;

    assert(ror.fuse == nd);
    assert(ror.fuse!2 == nd.transposed!2);
    assert(ror.fuse!(1, 2) == nd.transposed!(1, 2));
    assert(ror.fuse!(2, 1) == nd.transposed!(2, 1));
}

private template fuseDimensionCount(R)
{
    static if (is(typeof(R.init.shape) : size_t[N], size_t N) && (isDynamicArray!R || __traits(hasMember, R, "front")))
    {
        import mir.ndslice.topology: repeat;
        enum size_t fuseDimensionCount = N + fuseDimensionCount!(typeof(mixin("R.init" ~ ".front".repeat(N).fuseCells.field)));
    }
    else
        enum size_t fuseDimensionCount = 0;
}

/+
TODO docs
+/
size_t[fuseDimensionCount!Range] fuseShape(Range)(Range r)
    if (hasShape!Range)
{
    // auto outerShape = r.shape;
    enum N = r.shape.length;
    static if (N == typeof(return).length)
    {
        return r.shape;
    }
    else
    {
        import mir.ndslice.topology: repeat;
        typeof(return) ret;
        ret[0 .. N] = r.shape;
        if (!ret[0 .. N].anyEmptyShape)
            ret[N .. $] = fuseShape(mixin("r" ~ ".front".repeat(N).fuseCells.field));
        return ret;
    }
}

private template FuseElementType(NDRange)
{
    import mir.ndslice.topology: repeat;
    alias FuseElementType = typeof(mixin("NDRange.init" ~ ".front".repeat(fuseDimensionCount!NDRange).fuseCells.field));
}

/++
Fuses `cells` into GC-allocated ndslice.

Params:
    cells = ndrange of ndcells, ndrange and ndcell should have `shape` and multidimensional input range primivies (`front!d`, `empty!d`, `popFront!d`).
Returns: ndslice composed of fused cells.
See_also: $(SUBREF chunks, chunks)
+/
auto fuseCells(S)(S cells)
{
    alias T = DeepElementType!(DeepElementType!S);
    alias UT = Unqual!T;
    if (__ctfe)
    {
        import mir.ndslice.allocation: slice;
        auto ret = cells.fuseCellsShape.slice!UT;
        ret.fuseCellsAssign!"a = b" = cells;
        static if (is(T == immutable))
            return (() @trusted => cast(immutable) ret)()[];
        else
        static if (is(T == const))
            return (() @trusted => cast(const) ret)()[];
        else
            return ret;
    }
    else
    {
        import mir.ndslice.allocation: uninitSlice;
        import mir.conv;
        auto ret = cells.fuseCellsShape.uninitSlice!UT;
        ret.fuseCellsAssign!(emplaceRef!T) = cells;
        alias R = Slice!(T*, ret.N);
        return R(ret._structure, (() @trusted => cast(T*)ret._iterator)());
    }
}

/// 1D
@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.topology: iota;
    enum ar = [[0, 1], [], [2, 3, 4, 5], [6], [7, 8, 9]];
    static assert ([[0, 1], [], [2, 3, 4, 5], [6], [7, 8, 9]].fuseCells == 10.iota);
    assert (ar.fuseCells == 10.iota);
}

/// 2D
@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.topology: iota;
    import mir.ndslice.chunks;

    auto sl = iota(11, 17);
    assert(sl.chunks!(0, 1)(3, 4).fuseCells == sl);
}

/+
TODO docs
+/
auto fuseCellsAssign(alias fun = "a = b", Iterator, size_t N, SliceKind kind, S)(Slice!(Iterator, N, kind) to, S cells)
{
    assert(to.shape == cells.fuseCellsShape, "'cells.fuseCellsShape' should be equal to 'to.shape'");

    if (cells.anyEmpty)
        goto R;

    import mir.functional: naryFun;
    import mir.ndslice.topology: canonical;
    static if (kind == Contiguous)
        fuseCellsEmplaceImpl!(naryFun!fun, 0, N)(to.canonical, cells);
    else
        fuseCellsEmplaceImpl!(naryFun!fun, 0, N)(to, cells);
    R: return to;
}

/+
TODO docs
+/
size_t[S.init.shape.length] fuseCellsShape(S)(S cells) @property
{
    typeof(return) ret;
    enum N = ret.length;
    static if (N == 1)
    {
        foreach (ref e; cells)
            ret[0] += e.length;
    }
    else
    {
        import mir.ndslice.topology: repeat;
        enum expr = "e" ~ ".front".repeat(N).fuseCells.field;
        foreach (i; Iota!N)
            for (auto e = cells.save; !e.empty!i; e.popFront!i)
                ret[i] += mixin(expr).length!i;
    }
    return ret;
}

private auto fuseCellsEmplaceImpl(alias fun, size_t i, size_t M, Iterator, size_t N, SliceKind kind, S)(Slice!(Iterator, N, kind) to, S cells)
{
    do
    {
        auto from = cells.front;
        static if (M == 1)
        {
            auto n = from.length!i;
        }
        else
        {
            import mir.ndslice.topology: repeat;
            enum expr = "from" ~ ".front".repeat(N - 1 - i).fuseCells.field;
            auto n = mixin(expr).length!i;
        }
        assert (to.length!i >= n);
        static if (i + 1 == M)
        {
            import mir.algorithm.iteration: each;
            each!fun(to.selectFront!i(n), from);
        }
        else
        {
            .fuseCellsEmplaceImpl!(fun, i + 1, N)(to.selectFront!i(n), from);
        }
        to.popFrontExactly!i(n);
        cells.popFront;
    }
    while(!cells.empty);
    return to;
}
