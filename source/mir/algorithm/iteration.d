// Written in the D programming language.
/**
This is a submodule of $(MREF std, algorithm).
It contains generic _iteration algorithms.
$(SCRIPT inhibitQuickIndex = 1;)

$(BOOKTABLE $(H2 Function),
$(TR $(TH Function Name) $(TH Description))
$(T2 all, Checks if all elements satisfy to a predicate.)
$(T2 any, Checks if at least one element satisfy to a predicate.)
$(T2 cmp, Compares two slices.)
$(T2 count, Counts elements in a slices according to a predicate.)
$(T2 each, Iterates all elements.)
$(T2 eachLower, Iterates lower triangle of matrix.)
$(T2 eachUploPair, Iterates upper and lower pairs of elements in square matrix.)
$(T2 eachUpper, Iterates upper triangle of matrix.)
$(T2 equal, Compares two slices for equality.)
$(T2 find, Finds backward index.)
$(T2 findIndex, Finds index.)
$(T2 isSymmetric, Checks if the matrix is symmetric.)
$(T2 maxIndex, Finds index of the maximum.)
$(T2 maxPos, Finds backward index of the maximum.)
$(T2 minIndex, Finds index of the minimum.)
$(T2 minmaxIndex, Finds indexes of the minimum and the maximum.)
$(T2 minmaxPos, Finds backward indexes of the minimum and the maximum.)
$(T2 minPos, Finds backward index of the minimum.)
$(T2 nBitsToCount, Сount bits until set bit count is reached.)
$(T2 reduce, Accumulates all elements.)
$(T2 uniq, Iterates over the unique elements in a range, which is assumed sorted.)
)

All operators are suitable to change slices using `ref` argument qualification in a function declaration.
Note, that string lambdas in Mir are `auto ref` functions.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-2018, Ilya Yaroshenko, 2018-, Mir community
Authors:   Ilya Yaroshenko, John Michael Hall, Andrei Alexandrescu (original Phobos code)

Copyright: Andrei Alexandrescu 2008-. Ilya Yaroshenko 2017-
License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: , Ilya Yaroshenko (Mir & BetterC rework).
Source: $(PHOBOSSRC std/algorithm/_iteration.d)
Macros:
    NDSLICEREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
    T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
 */
module mir.algorithm.iteration;

import mir.primitives;
import mir.functional: naryFun;
import mir.internal.utility;
import mir.math.common: optmath;
import mir.ndslice.field: BitField;
import mir.ndslice.internal;
import mir.ndslice.iterator: FieldIterator, RetroIterator;
import mir.ndslice.slice;
import mir.primitives;
import std.meta;
import std.range.primitives: isInputRange, isBidirectionalRange, isInfinite, isForwardRange, ElementType;
import std.traits;

@optmath:


/+
Bitslice representation for accelerated bitwise algorithm.
1-dimensional contiguousitslice can be split into three chunks: head bits, body chunks, and tail bits.

Bitslice can have head bits because it has slicing and the zero bit may not be aligned to the zero of a body chunk.
+/
private struct BitSliceAccelerator(Field, I = typeof(Field.init[size_t.init]))
    if (__traits(isUnsigned, I))
{
    import mir.bitop;
    import mir.qualifier: lightConst;
    import mir.ndslice.traits: isIterator;
    import mir.ndslice.iterator: FieldIterator;
    import mir.ndslice.field: BitField;

    ///
    alias U = typeof(I + 1u);
    /// body bits chunks
    static if (isIterator!Field)
        Slice!Field bodyChunks;
    else
        Slice!(FieldIterator!Field) bodyChunks;
    /// head length
    int headLength;
    /// tail length
    int tailLength;

@optmath:

    this(Slice!(FieldIterator!(BitField!(Field, I))) slice)
    {
        enum mask = bitShiftMask!I;
        enum shift = bitElemShift!I;
        size_t length = slice.length;
        size_t index = slice._iterator._index;
        if (auto hlen = index & mask)
        {
            auto l = I.sizeof * 8 - hlen;
            if (l > length)
            {
                // central problem
                headLength = -cast(int) length;
                tailLength = cast(int) hlen;
                goto F;
            }
            else
            {
                headLength = cast(uint) l;
                length -= l;
                index += l;
            }
        }
        tailLength = cast(int) (length & mask);
    F:
        length >>= shift;
        index >>= shift;
        bodyChunks._lengths[0] = length;
        static if (isIterator!Field)
        {
            bodyChunks._iterator = slice._iterator._field._field;
            bodyChunks._iterator += index;
        }
        else
        {
            bodyChunks._iterator._index = index;
            bodyChunks._iterator._field = slice._iterator._field._field;
        }
    }

scope const:

    bool isCentralProblem()
    {
        return headLength < 0;
    }

    U centralBits()
    {
        assert(isCentralProblem);
        return *bodyChunks._iterator.lightConst >>> tailLength;
    }

    uint centralLength()
    {
        assert(isCentralProblem);
        return -headLength;
    }

    /// head bits (last `headLength` bits are valid).
    U headBits()
    {
        assert(!isCentralProblem);
        if (headLength == 0)
            return U.init;
        static if (isIterator!Field)
            return bodyChunks._iterator.lightConst[-1];
        else
            return bodyChunks._iterator._field.lightConst[bodyChunks._iterator._index - 1];
    }

    /// tail bits (first `tailLength` bits are valid).
    U tailBits()
    {
        assert(!isCentralProblem);
        if (tailLength == 0)
            return U.init;
        static if (isIterator!Field)
            return bodyChunks._iterator.lightConst[bodyChunks.length];
        else
            return bodyChunks._iterator._field.lightConst[bodyChunks._iterator._index + bodyChunks.length];
    }

    U negCentralMask()
    {
        return U.max << centralLength;
    }

    U negHeadMask()
    {
        return U.max << headLength;
    }

    U negTailMask()
    {
        return U.max << tailLength;
    }

    U negCentralMaskS()
    {
        return U.max >> centralLength;
    }

    U negHeadMaskS()
    {
        return U.max >> headLength;
    }

    U negTailMaskS()
    {
        return U.max >> tailLength;
    }

    U centralBitsWithRemainingZeros()
    {
        return centralBits & ~negCentralMask;
    }

    U centralBitsWithRemainingZerosS()
    {
        return centralBits << (U.sizeof * 8 - centralLength);
    }

    U headBitsWithRemainingZeros()
    {
        return headBits >>> (I.sizeof * 8 - headLength);
    }

    U headBitsWithRemainingZerosS()
    {
        static if (U.sizeof > I.sizeof)
            return (headBits << (U.sizeof - I.sizeof) * 8) & ~negTailMaskS;
        else
            return headBits & ~negTailMaskS;
    }

    U tailBitsWithRemainingZeros()
    {
        return tailBits & ~negTailMask;
    }

    U tailBitsWithRemainingZerosS()
    {
        return tailBits << (U.sizeof * 8 - tailLength);
    }

    U centralBitsWithRemainingOnes()
    {
        return centralBits | negCentralMask;
    }

    U centralBitsWithRemainingOnesS()
    {
        return centralBitsWithRemainingZerosS | negCentralMaskS;
    }

    U headBitsWithRemainingOnes()
    {
        return headBitsWithRemainingZeros | negHeadMask;
    }

    U headBitsWithRemainingOnesS()
    {
        return headBitsWithRemainingZerosS | negHeadMaskS;
    }

    U tailBitsWithRemainingOnes()
    {
        return tailBits | negTailMask;
    }

    U tailBitsWithRemainingOnesS()
    {
        return tailBitsWithRemainingZerosS | negTailMaskS;
    }

    size_t ctpop()
    {
        import mir.bitop: ctpop;
        if (isCentralProblem)
            return centralBitsWithRemainingZeros.ctpop;
        size_t ret;
        if (headLength)
            ret = cast(size_t) headBitsWithRemainingZeros.ctpop;
        if (bodyChunks.length)
        {
            auto bc = bodyChunks.lightConst;
            do
            {
                ret += cast(size_t) bc.front.ctpop;
                bc.popFront;
            }
            while(bc.length);
        }
        if (tailBits)
            ret += cast(size_t) tailBitsWithRemainingZeros.ctpop;
        return ret;
    }

    bool any()
    {
        if (isCentralProblem)
            return centralBitsWithRemainingZeros != 0;
        if (headBitsWithRemainingZeros != 0)
            return true;
        if (bodyChunks.length)
        {
            auto bc = bodyChunks.lightConst;
            do
            {
                if (bc.front != 0)
                    return true;
                bc.popFront;
            }
            while(bc.length);
        }
        if (tailBitsWithRemainingZeros != 0)
            return true;
        return false;
    }

    bool all()
    {
        if (isCentralProblem)
            return centralBitsWithRemainingOnes != U.max;
        size_t ret;
        if (headBitsWithRemainingOnes != U.max)
            return false;
        if (bodyChunks.length)
        {
            auto bc = bodyChunks.lightConst;
            do
            {
                if (bc.front != I.max)
                    return false;
                bc.popFront;
            }
            while(bc.length);
        }
        if (tailBitsWithRemainingOnes != U.max)
            return false;
        return true;
    }

    size_t cttz()
    {
        U v;
        size_t ret;
        if (isCentralProblem)
        {
            v = centralBitsWithRemainingOnes;
            if (v)
                goto R;
            ret = centralLength;
            goto L;
        }
        v = headBitsWithRemainingOnes;
        if (v)
            goto R;
        ret = headLength;
        if (bodyChunks.length)
        {
            auto bc = bodyChunks.lightConst;
            do
            {
                v = bc.front;
                if (v)
                    goto R;
                ret += I.sizeof * 8;
                bc.popFront;
            }
            while(bc.length);
        }
        v = tailBitsWithRemainingOnes;
        if (v)
            goto R;
        ret += tailLength;
        goto L;
    R:
        ret += v.cttz;
    L:
        return ret;
    }

    size_t ctlz()
    {
        U v;
        size_t ret;
        if (isCentralProblem)
        {
            v = centralBitsWithRemainingOnes;
            if (v)
                goto R;
            ret = centralLength;
            goto L;
        }
        v = tailBitsWithRemainingOnesS;
        if (v)
            goto R;
        ret = tailLength;
        if (bodyChunks.length)
        {
            auto bc = bodyChunks.lightConst;
            do
            {
                v = bc.back;
                if (v)
                    goto R;
                ret += I.sizeof * 8;
                bc.popBack;
            }
            while(bc.length);
        }
        v = headBitsWithRemainingOnesS;
        if (v)
            goto R;
        ret += headLength;
        goto L;
    R:
        ret += v.ctlz;
    L:
        return ret;
    }

    sizediff_t nBitsToCount(size_t count)
    {
        size_t ret;
        if (count == 0)
            return count;
        U v, cnt;
        if (isCentralProblem)
        {
            v = centralBitsWithRemainingZeros;
            goto E;
        }
        v = headBitsWithRemainingZeros;
        cnt = v.ctpop;
        if (cnt >= count)
            goto R;
        ret += headLength;
        count -= cast(size_t) cnt;
        if (bodyChunks.length)
        {
            auto bc = bodyChunks.lightConst;
            do
            {
                v = bc.front;
                cnt = v.ctpop;
                if (cnt >= count)
                    goto R;
                ret += I.sizeof * 8;
                count -= cast(size_t) cnt;
                bc.popFront;
            }
            while(bc.length);
        }
        v = tailBitsWithRemainingZeros;
    E:
        cnt = v.ctpop;
        if (cnt >= count)
            goto R;
        return -1;
    R:
        return ret + v.nTrailingBitsToCount(count);
    }

    sizediff_t retroNBitsToCount(size_t count)
    {
        if (count == 0)
            return count;
        size_t ret;
        U v, cnt;
        if (isCentralProblem)
        {
            v = centralBitsWithRemainingZerosS;
            goto E;
        }
        v = tailBitsWithRemainingZerosS;
        cnt = v.ctpop;
        if (cnt >= count)
            goto R;
        ret += tailLength;
        count -= cast(size_t) cnt;
        if (bodyChunks.length)
        {
            auto bc = bodyChunks.lightConst;
            do
            {
                v = bc.back;
                cnt = v.ctpop;
                if (cnt >= count)
                    goto R;
                ret += I.sizeof * 8;
                count -= cast(size_t) cnt;
                bc.popBack;
            }
            while(bc.length);
        }
        v = headBitsWithRemainingZerosS;
    E:
        cnt = v.ctpop;
        if (cnt >= count)
            goto R;
        return -1;
    R:
        return ret + v.nLeadingBitsToCount(count);
    }
}

/++
Сount bits until set bit count is reached. Works with ndslices created with $(REF bitwise, mir,ndslice,topology), $(REF bitSlice, mir,ndslice,allocation).
Returns: bit count if set bit count is reached or `-1` otherwise.
+/
sizediff_t nBitsToCount(Field, I)(scope Slice!(FieldIterator!(BitField!(Field, I))) bitSlice, size_t count)
{
    return BitSliceAccelerator!(Field, I)(bitSlice).nBitsToCount(count);
}

///ditto
sizediff_t nBitsToCount(Field, I)(scope Slice!(RetroIterator!(FieldIterator!(BitField!(Field, I)))) bitSlice, size_t count)
{
    import mir.ndslice.topology: retro;
    return BitSliceAccelerator!(Field, I)(bitSlice.retro).retroNBitsToCount(count);
}

///
pure unittest
{
    import mir.ndslice.allocation: bitSlice;
    import mir.ndslice.topology: retro;
    auto s = bitSlice(1000);
    s[50] = true;
    s[100] = true;
    s[200] = true;
    s[300] = true;
    s[400] = true;
    assert(s.nBitsToCount(4) == 301);
    assert(s.retro.nBitsToCount(4) == 900);
}

private void checkShapesMatch(
    string fun = __FUNCTION__,
    string pfun = __PRETTY_FUNCTION__,
    Slices...)
    (scope ref const Slices slices)
    if (Slices.length > 1)
{
    enum msg = "all arguments must be slices" ~ tailErrorMessage!(fun, pfun);
    enum msgShape = "all slices must have the same shape"  ~ tailErrorMessage!(fun, pfun);
    enum N = slices[0].shape.length;
    foreach (i, Slice; Slices)
    {
        static if (i == 0)
            continue;
        else
        static if (slices[i].shape.length == N)
            assert(slices[i].shape == slices[0].shape, msgShape);
        else
        {
            import mir.ndslice.fuse: fuseShape;
            static assert(slices[i].fuseShape.length >= N);
            assert(slices[i].fuseShape[0 .. N] == slices[0].shape, msgShape);
        }
    }
}

template frontOf(size_t N)
{
    static if (N == 0)
        enum frontOf = "";
    else
    {
        enum i = N - 1;
        enum frontOf = frontOf!i ~ "slices[" ~ i.stringof ~ "].front, ";
    }
}

template allFlattened(size_t N)
 if (N)
{
    enum  i = N - 1;
    static if (i)
        enum allFlattened = .allFlattened!i ~ ("slices[" ~ i.stringof ~ "].flattened, ");
    else
        enum allFlattened = "slices[" ~ i.stringof ~ "].flattened, ";
}

private template areAllContiguousSlices(Slices...)
{
    import mir.ndslice.traits: isContiguousSlice;
     static if (allSatisfy!(isContiguousSlice, Slices))
        enum areAllContiguousSlices = Slices[0].N > 1;
     else
        enum areAllContiguousSlices = false;
}

version(LDC) {}
else version(GNU) {}
else version (Windows) {}
else version (X86_64)
{
    //Compiling with DMD for x86-64 for Linux & OS X with optimizations enabled,
    //"Tensor mutation on-the-fly" unittest was failing. Disabling inlining
    //caused it to succeed.
    //TODO: Rework so this is unnecessary!
    version = Mir_disable_inlining_in_reduce;
}

version(Mir_disable_inlining_in_reduce)
{
    private enum Mir_disable_inlining_in_reduce = true;

    private template _naryAliases(size_t n)
    {
        static if (n == 0)
            enum _naryAliases = "";
        else
        {
            enum i = n - 1;
            enum _naryAliases = _naryAliases!i ~ "alias " ~ cast(char)('a' + i) ~ " = args[" ~ i.stringof ~ "];\n";
        }
    }

    private template nonInlinedNaryFun(alias fun)
    {
        import mir.math.common : optmath;
        static if (is(typeof(fun) : string))
        {
            /// Specialization for string lambdas
            @optmath auto ref nonInlinedNaryFun(Args...)(auto ref Args args)
                if (args.length <= 26)
            {
                pragma(inline,false);
                mixin(_naryAliases!(Args.length));
                return mixin(fun);
            }
        }
        else static if (is(typeof(fun.opCall) == function))
        {
            @optmath auto ref nonInlinedNaryFun(Args...)(auto ref Args args)
                if (is(typeof(fun.opCall(args))))
            {
                pragma(inline,false);
                return fun.opCall(args);
            }
        }
        else
        {
            @optmath auto ref nonInlinedNaryFun(Args...)(auto ref Args args)
                if (is(typeof(fun(args))))
            {
                pragma(inline,false);
                return fun(args);
            }
        }
    }
}
else
{
    private enum Mir_disable_inlining_in_reduce = false;
}

S reduceImpl(alias fun, S, Slices...)(S seed, scope Slices slices)
{
    do
    {
        static if (DimensionCount!(Slices[0]) == 1)
            seed = mixin("fun(seed, " ~ frontOf!(Slices.length) ~ ")");
        else
            seed = mixin(".reduceImpl!fun(seed," ~ frontOf!(Slices.length) ~ ")");
        foreach_reverse(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return seed;
}

/++
Implements the homonym function (also known as `accumulate`,
`compress`, `inject`, or `fold`) present in various programming
languages of functional flavor. The call `reduce!(fun)(seed, slice1, ..., sliceN)`
first assigns `seed` to an internal variable `result`,
also called the accumulator. Then, for each set of element `x1, ..., xN` in
`slice1, ..., sliceN`, `result = fun(result, x1, ..., xN)` gets evaluated. Finally,
`result` is returned.

`reduce` allows to iterate multiple slices in the lockstep.

Note:
    $(NDSLICEREF topology, pack) can be used to specify dimensions.
Params:
    fun = A function.
See_Also:
    $(HTTP llvm.org/docs/LangRef.html#fast-math-flags, LLVM IR: Fast Math Flags)

    $(HTTP en.wikipedia.org/wiki/Fold_(higher-order_function), Fold (higher-order function))
+/
template reduce(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun)
        && !Mir_disable_inlining_in_reduce)
    /++
    Params:
        seed = An initial accumulation value.
        slices = One or more slices, range, and arrays.
    Returns:
        the accumulated `result`
    +/
    @optmath auto reduce(S, Slices...)(S seed, scope Slices slices)
        if (Slices.length)
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        static if (areAllContiguousSlices!Slices)
        {
            import mir.ndslice.topology: flattened;
            return mixin(`.reduce!fun(seed, ` ~ allFlattened!(Slices.length) ~`)`);
        }
        else
        {
            if (slices[0].anyEmpty)
                return cast(Unqual!S) seed;
            static if (is(S : Unqual!S))
                alias UT = Unqual!S;
            else
                alias UT = S;
            return reduceImpl!(fun, UT, Slices)(seed, slices);
        }
    }
    else version(Mir_disable_inlining_in_reduce)
    //As above, but with inlining disabled.
    @optmath auto reduce(S, Slices...)(S seed, scope Slices slices)
        if (Slices.length)
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        static if (areAllContiguousSlices!Slices)
        {
            import mir.ndslice.topology: flattened;
            return mixin(`.reduce!fun(seed, ` ~ allFlattened!(Slices.length) ~`)`);
        }
        else
        {
            if (slices[0].anyEmpty)
                return cast(Unqual!S) seed;
            static if (is(S : Unqual!S))
                alias UT = Unqual!S;
            else
                alias UT = S;
            return reduceImpl!(nonInlinedNaryFun!fun, UT, Slices)(seed, slices);
        }
    }
    else
        alias reduce = .reduce!(naryFun!fun);
}

/// Ranges and arrays
version(mir_test)
unittest
{
    auto ar = [1, 2, 3];
    auto s = 0.reduce!"a + b"(ar);
    assert (s == 6);
}

/// Single slice
version(mir_test)
unittest
{
    import mir.ndslice.topology : iota;

    //| 0 1 2 | => 3  |
    //| 3 4 5 | => 12 | => 15
    auto sl = iota(2, 3);

    // sum of all element in the slice
    auto res = size_t(0).reduce!"a + b"(sl);

    assert(res == 15);
}

/// Multiple slices, dot product
version(mir_test)
unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto a = iota([2, 3], 0).as!double.slice;
    //| 1 2 3 |
    //| 4 5 6 |
    auto b = iota([2, 3], 1).as!double.slice;

    alias dot = reduce!"a + b * c";
    auto res = dot(0.0, a, b);

    // check the result:
    import mir.ndslice.topology : flattened;
    import std.numeric : dotProduct;
    assert(res == dotProduct(a.flattened, b.flattened));
}

/// Zipped slices, dot product
pure
version(mir_test) unittest
{
    import std.typecons : Yes;
    import std.numeric : dotProduct;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota, zip, universal;
    import mir.math.common : optmath;

    static @optmath T fmuladd(T, Z)(const T a, Z z)
    {
        return a + z.a * z.b;
    }

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3).as!double.slice.universal;
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1).as!double.slice;

    // slices must have the same strides for `zip!true`.
    assert(sl1.strides == sl2.strides);

    auto z = zip!true(sl1, sl2);

    auto dot = reduce!fmuladd(0.0, z);

    assert(dot == dotProduct(iota(6), iota([6], 1)));
}

/// Tensor mutation on-the-fly
version(mir_test)
unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;
    import mir.math.common : optmath;

    static @optmath T fun(T)(const T a, ref T b)
    {
        return a + b++;
    }

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota(2, 3).as!double.slice;

    auto res = reduce!fun(double(0), sl);

    assert(res == 15);

    //| 1 2 3 |
    //| 4 5 6 |
    assert(sl == iota([2, 3], 1));
}

/++
Packed slices.

Computes minimum value of maximum values for each row.
+/
version(mir_test)
unittest
{
    import mir.math.common;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.dynamic : transposed;
    import mir.ndslice.topology : as, iota, pack, map, universal;

    alias maxVal = (a) => reduce!fmax(-double.infinity, a);
    alias minVal = (a) => reduce!fmin(double.infinity, a);
    alias minimaxVal = (a) => minVal(a.pack!1.map!maxVal);

    auto sl = iota(2, 3).as!double.slice;

    // Vectorized computation: row stride equals 1.
    //| 0 1 2 | => | 2 |
    //| 3 4 5 | => | 5 | => 2
    auto res = minimaxVal(sl);
    assert(res == 2);

    // Common computation: row stride does not equal 1.
    //| 0 1 2 |    | 0 3 | => | 3 |
    //| 3 4 5 | => | 1 4 | => | 4 |
    //             | 2 5 | => | 5 | => 3
    auto resT = minimaxVal(sl.universal.transposed);
    assert(resT == 3);
}

/// Dlang Range API support.
version(mir_test)
unittest
{
    import mir.algorithm.iteration: each;
    import std.range: phobos_iota = iota;

    int s;
    // 0 1 2 3
    4.phobos_iota.each!(i => s += i);
    assert(s == 6);
}

@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    auto a = reduce!"a + b"(size_t(7), iota([0, 1], 1));
    assert(a == 7);
}

void eachImpl(alias fun, Slices...)(scope Slices slices)
{
    foreach(ref slice; slices)
        assert(!slice.empty);
    do
    {
        static if (DimensionCount!(Slices[0]) == 1)
            mixin("fun(" ~ frontOf!(Slices.length) ~ ");");
        else
            mixin(".eachImpl!fun(" ~ frontOf!(Slices.length) ~ ");");
        foreach_reverse(i; Iota!(Slices.length))
            slices[i].popFront;
    }
    while(!slices[0].empty);
}

/++
The call `each!(fun)(slice1, ..., sliceN)`
evaluates `fun` for each set of elements `x1, ..., xN` in
`slice1, ..., sliceN` respectively.

`each` allows to iterate multiple slices in the lockstep.
Params:
    fun = A function.
Note:
    $(NDSLICEREF dynamic, transposed) and
    $(NDSLICEREF topology, pack) can be used to specify dimensions.
See_Also:
    This is functionally similar to $(LREF reduce) but has not seed.
+/
template each(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    /++
    Params:
        slices = One or more slices, ranges, and arrays.
    +/
    @optmath auto each(Slices...)(scope Slices slices)
        if (Slices.length)
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        static if (areAllContiguousSlices!Slices)
        {
            import mir.ndslice.topology: flattened;
            mixin(`.each!fun(` ~ allFlattened!(Slices.length) ~`);`);
        }
        else
        {
            if (slices[0].anyEmpty)
                return;
            eachImpl!fun(slices);
        }
    }
    else
        alias each = .each!(naryFun!fun);
}

/// Ranges and arrays
version(mir_test)
unittest
{
    auto ar = [1, 2, 3];
    ar.each!"a *= 2";
    assert (ar == [2, 4, 6]);
}

/// Single slice, multiply-add
version(mir_test)
unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota(2, 3).as!double.slice;

    sl.each!((ref a) { a = a * 10 + 5; });

    assert(sl ==
        [[ 5, 15, 25],
         [35, 45, 55]]);
}

/// Swap two slices
version(mir_test)
unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto a = iota([2, 3], 0).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    auto b = iota([2, 3], 10).as!double.slice;

    each!swap(a, b);

    assert(a == iota([2, 3], 10));
    assert(b == iota([2, 3], 0));
}

/// Swap two zipped slices
version(mir_test)
unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, zip, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto a = iota([2, 3], 0).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    auto b = iota([2, 3], 10).as!double.slice;

    auto z = zip(a, b);

    z.each!(z => swap(z.a, z.b));

    assert(a == iota([2, 3], 10));
    assert(b == iota([2, 3], 0));
}

@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    size_t i;
    iota(0, 2).each!((a){i++;});
    assert(i == 0);
}

/++
The call `eachUploPair!(fun)(matrix)`
evaluates `fun` for each pair (`matrix[j, i]`, `matrix[i, j]`),
for i <= j (default) or i < j (if includeDiagonal is false).

Params:
    fun = A function.
    includeDiagonal = true if applying function to diagonal,
                      false (default) otherwise.
+/
template eachUploPair(alias fun, bool includeDiagonal = false)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    {
        /++
        Params:
            matrix = Square matrix.
        +/
        auto eachUploPair(Iterator, SliceKind kind)(scope Slice!(Iterator, 2, kind) matrix)
        in
        {
            assert(matrix.length!0 == matrix.length!1, "matrix must be square.");
        }
        body
        {
            static if (kind == Contiguous)
            {
                import mir.ndslice.topology: canonical;
                .eachUploPair!(fun, includeDiagonal)(matrix.canonical);
            }
            else
            {
                static if (includeDiagonal == true)
                {
                    if (matrix.length) do
                    {
                        eachImpl!fun(matrix.front!0, matrix.front!1);
                        matrix.popFront!1;
                        matrix.popFront!0;
                        // hint for optimizer
                        matrix._lengths[1] = matrix._lengths[0];
                    }
                    while (matrix.length);
                }
                else
                {
                    if (matrix.length) for(;;)
                    {
                        assert(!matrix.empty!0);
                        assert(!matrix.empty!1);
                        auto l = matrix.front!1;
                        auto u = matrix.front!0;
                        matrix.popFront!1;
                        matrix.popFront!0;
                        l.popFront;
                        u.popFront;
                        // hint for optimizer
                        matrix._lengths[1] = matrix._lengths[0] = l._lengths[0] = u._lengths[0];
                        if (u.length == 0)
                            break;
                        eachImpl!fun(u, l);
                    }
                }
            }
        }
    }
    else
    {
        alias eachUploPair = .eachUploPair!(naryFun!fun, includeDiagonal);
    }
}

/// Transpose matrix in place.
version(mir_test)
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota, universal;
    import mir.ndslice.dynamic: transposed;
    import mir.utility: swap;

    auto m = iota(4, 4).slice;

    m.eachUploPair!swap;

    assert(m == iota(4, 4).universal.transposed);
}

/// Reflect Upper matrix part to lower part.
version(mir_test)
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota, universal;
    import mir.ndslice.dynamic: transposed;
    import mir.utility: swap;

    // 0 1 2
    // 3 4 5
    // 6 7 8
    auto m = iota(3, 3).slice;

    m.eachUploPair!((u, ref l) { l = u; });

    assert(m == [
        [0, 1, 2],
        [1, 4, 5],
        [2, 5, 8]]);
}

/// Fill lower triangle and diagonal with zeroes.
version(mir_test)
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    // 1 2 3
    // 4 5 6
    // 7 8 9
    auto m = iota([3, 3], 1).slice;

    m.eachUploPair!((u, ref l) { l = 0; }, true);

    assert(m == [
        [0, 2, 3],
        [0, 0, 6],
        [0, 0, 0]]);
}

version(mir_test)
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    // 0 1 2
    // 3 4 5
    // 6 7 8
    auto m = iota(3, 3).slice;
    m.eachUploPair!((u, ref l) { l = l + 1; }, true);
    assert(m == [
        [1, 1, 2],
        [4, 5, 5],
        [7, 8, 9]]);
}

version(mir_test)
unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    // 0 1 2
    // 3 4 5
    // 6 7 8
    auto m = iota(3, 3).slice;
    m.eachUploPair!((u, ref l) { l = l + 1; }, false);

    assert(m == [
        [0, 1, 2],
        [4, 4, 5],
        [7, 8, 8]]);
}

/++
Checks if the matrix is symmetric.
+/
template isSymmetric(alias fun = "a == b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    /++
    Params:
        matrix = 2D ndslice.
    +/
    bool isSymmetric(Iterator, SliceKind kind)(Slice!(Iterator, 2, kind) matrix)
    {
        static if (kind == Contiguous)
        {
            import mir.ndslice.topology: canonical;
            return .isSymmetric!fun(matrix.canonical);
        }
        else
        {
            if (matrix.length!0 != matrix.length!1)
                return false;
            if (matrix.length) do
            {
                if (!allImpl!fun(matrix.front!0, matrix.front!1))
                {
                    return false;
                }
                matrix.popFront!1;
                matrix.popFront!0;
                matrix._lengths[1] = matrix._lengths[0];
            }
            while (matrix.length);
            return true;
        }
    }
    else
        alias isSymmetric = .isSymmetric!(naryFun!fun);
}

///
version(mir_test)
unittest
{
    import mir.ndslice.topology: iota;
    assert(iota(2, 2).isSymmetric == false);

    assert(
        [1, 2,
         2, 3].sliced(2, 2).isSymmetric == true);
}

bool minPosImpl(alias fun, Iterator, size_t N, SliceKind kind)(scope ref size_t[N] backwardIndex, scope ref Iterator iterator, Slice!(Iterator, N, kind) slice)
{
    bool found;
    do
    {
        static if (slice.shape.length == 1)
        {
            if (fun(*slice._iterator, *iterator))
            {
                backwardIndex[0] = slice.length;
                iterator = slice._iterator;
                found = true;
            }
        }
        else
        {
            if (minPosImpl!(fun, Iterator, N - 1, kind)(backwardIndex[1 .. $], iterator, slice.front))
            {
                backwardIndex[0] = slice.length;
                found = true;
            }
        }
        slice.popFront;
    }
    while(!slice.empty);
    return found;
}

bool[2] minmaxPosImpl(alias fun, Iterator, size_t N, SliceKind kind)(scope ref size_t[2][N] backwardIndex, scope ref Iterator[2] iterator, Slice!(Iterator, N, kind) slice)
{
    bool[2] found;
    do
    {
        static if (slice.shape.length == 1)
        {
            if (fun(*slice._iterator, *iterator[0]))
            {
                backwardIndex[0][0] = slice.length;
                iterator[0] = slice._iterator;
                found[0] = true;
            }
            else
            if (fun(*iterator[1], *slice._iterator))
            {
                backwardIndex[0][1] = slice.length;
                iterator[1] = slice._iterator;
                found[1] = true;
            }
        }
        else
        {
            auto r = minmaxPosImpl!(fun, Iterator, N - 1, kind)(backwardIndex[1 .. $], iterator, slice.front);
            if (r[0])
            {
                backwardIndex[0][0] = slice.length;
            }
            if (r[1])
            {
                backwardIndex[0][1] = slice.length;
            }
        }
        slice.popFront;
    }
    while(!slice.empty);
    return found;
}

/++
Finds a positions (ndslices) such that
`position[0].first` is minimal and `position[1].first` is maximal elements in the slice.

Position is sub-ndslice of the same dimension in the right-$(RPAREN)down-$(RPAREN)etc$(LPAREN)$(LPAREN) corner.

Params:
    pred = A predicate.

See_also:
    $(LREF minmaxIndex),
    $(LREF minPos),
    $(LREF maxPos),
    $(NDSLICEREF slice, Slice.backward).
+/
template minmaxPos(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        2 subslices with minimal and maximal `first` elements.
    +/
    @optmath Slice!(Iterator, N, kind == Contiguous && N > 1 ? Canonical : kind)[2]
        minmaxPos(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        typeof(return) pret;
        if (!slice.anyEmpty)
        {
            size_t[2][N] ret;
            auto it = slice._iterator;
            Iterator[2] iterator = [it, it];
            minmaxPosImpl!(pred, Iterator, N, kind)(ret, iterator, slice);
            foreach (i; Iota!N)
            {
                pret[0]._lengths[i] = ret[i][0];
                pret[1]._lengths[i] = ret[i][1];
            }
            pret[0]._iterator = iterator[0];
            pret[1]._iterator = iterator[1];
        }
        auto strides = slice.strides;
        foreach(i; Iota!(0, pret[0].S))
        {
            pret[0]._strides[i] = strides[i];
            pret[1]._strides[i] = strides[i];
        }
        return pret;
    }
    else
        alias minmaxPos = .minmaxPos!(naryFun!pred);
}

///
version(mir_test)
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 2,
        ].sliced(3, 4);

    auto pos = s.minmaxPos;

    assert(pos[0] == s[$ - 2 .. $, $ - 3 .. $]);
    assert(pos[1] == s[$ - 1 .. $, $ - 2 .. $]);

    assert(pos[0].first == -4);
    assert(s.backward(pos[0].shape) == -4);
    assert(pos[1].first ==  7);
    assert(s.backward(pos[1].shape) ==  7);
}

/++
Finds a backward indexes such that
`slice[indexes[0]]` is minimal and `slice[indexes[1]]` is maximal elements in the slice.

Params:
    pred = A predicate.

See_also:
    $(LREF minmaxIndex),
    $(LREF minPos),
    $(LREF maxPos),
    $(REF Slice.backward, mir,ndslice,slice).
+/
template minmaxIndex(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        Subslice with minimal (maximal) `first` element.
    +/
    @optmath size_t[N][2] minmaxIndex(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        typeof(return) pret = size_t.max;
        if (!slice.anyEmpty)
        {
            auto shape = slice.shape;
            size_t[2][N] ret;
            foreach (i; Iota!N)
            {
                ret[i][1] = ret[i][0] = shape[i];
            }
            auto it = slice._iterator;
            Iterator[2] iterator = [it, it];
            minmaxPosImpl!(pred, Iterator, N, kind)(ret, iterator, slice);
            foreach (i; Iota!N)
            {
                pret[0][i] = slice._lengths[i] - ret[i][0];
                pret[1][i] = slice._lengths[i] - ret[i][1];
            }
        }
        return pret;
    }
    else
        alias minmaxIndex = .minmaxIndex!(naryFun!pred);
}

///
version(mir_test)
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 8,
        ].sliced(3, 4);

    auto indexes = s.minmaxIndex;

    assert(indexes == [[1, 1], [2, 3]]);
    assert(s[indexes[0]] == -4);
    assert(s[indexes[1]] ==  8);
}

/++
Finds a backward index such that
`slice.backward(index)` is minimal(maximal).

Params:
    pred = A predicate.

See_also:
    $(LREF minIndex),
    $(LREF maxPos),
    $(LREF maxIndex),
    $(REF Slice.backward, mir,ndslice,slice).
+/
template minPos(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        Multidimensional backward index such that element is minimal(maximal).
        Backward index equals zeros, if slice is empty.
    +/
    @optmath Slice!(Iterator, N, kind == Contiguous && N > 1 ? Canonical : kind)
        minPos(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        typeof(return) ret = { _iterator : slice._iterator };
        if (!slice.anyEmpty)
        {
            minPosImpl!(pred, Iterator, N, kind)(ret._lengths, ret._iterator, slice);
        }
        auto strides = slice.strides;
        foreach(i; Iota!(0, ret.S))
        {
            ret._strides[i] = strides[i];
        }
        return ret;
    }
    else
        alias minPos = .minPos!(naryFun!pred);
}

/// ditto
template maxPos(alias pred = "a < b")
{
    import mir.functional: naryFun, reverseArgs;
    alias maxPos = minPos!(reverseArgs!(naryFun!pred));
}

///
version(mir_test)
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 2,
        ].sliced(3, 4);

    auto pos = s.minPos;

    assert(pos == s[$ - 2 .. $, $ - 3 .. $]);
    assert(pos.first == -4);
    assert(s.backward(pos.shape) == -4);

    pos = s.maxPos;

    assert(pos == s[$ - 1 .. $, $ - 2 .. $]);
    assert(pos.first == 7);
    assert(s.backward(pos.shape) == 7);
}

/++
Finds an index such that
`slice[index]` is minimal(maximal).

Params:
    pred = A predicate.

See_also:
    $(LREF minIndex),
    $(LREF maxPos),
    $(LREF maxIndex).
+/
template minIndex(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slice = ndslice.
    Returns:
        Multidimensional index such that element is minimal(maximal).
        Index elements equal to `size_t.max`, if slice is empty.
    +/
    @optmath size_t[N] minIndex(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
    {
        size_t[N] ret = size_t.max;
        if (!slice.anyEmpty)
        {
            ret = slice.shape;
            minPosImpl!(pred, Iterator, N, kind)(ret, slice._iterator, slice);
            foreach (i; Iota!N)
                ret[i] = slice._lengths[i] - ret[i];
        }
        return ret;
    }
    else
        alias minIndex = .minIndex!(naryFun!pred);
}

/// ditto
template maxIndex(alias pred = "a < b")
{
    import mir.functional: naryFun, reverseArgs;
    alias maxIndex = minIndex!(reverseArgs!(naryFun!pred));
}

///
version(mir_test)
unittest
{
    auto s = [
        2, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 8,
        ].sliced(3, 4);

    auto index = s.minIndex;

    assert(index == [1, 1]);
    assert(s[index] == -4);

    index = s.maxIndex;

    assert(index == [2, 3]);
    assert(s[index] == 8);
}

///
version(mir_test)
unittest
{
    auto s = [
        -8, 6, 4, -3,
        0, -4, -3, 3,
        -3, -2, 7, 8,
        ].sliced(3, 4);

    auto index = s.minIndex;

    assert(index == [0, 0]);
    assert(s[index] == -8);
}

version(mir_test)
unittest
{
    auto s = [
            0, 1, 2, 3,
            4, 5, 6, 7,
            8, 9, 10, 11
            ].sliced(3, 4);

    auto index = s.minIndex;
    assert(index == [0, 0]);
    assert(s[index] == 0);

    index = s.maxIndex;
    assert(index == [2, 3]);
    assert(s[index] == 11);
}

bool findImpl(alias fun, size_t N, Slices...)(scope ref size_t[N] backwardIndex, Slices slices)
    if (Slices.length)
{
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(FieldIterator!(BitField!(Field, I))), Field, I))
    {
        auto cnt = BitSliceAccelerator!(Field, I)(slices[0]).cttz;
        if (cnt = -1)
            return false;
        backwardIndex[0] = slices[0].length - cnt;
    }
    else
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(RetroIterator!(FieldIterator!(BitField!(Field, I)))), Field, I))
    {
        import mir.ndslice.topology: retro;
        auto cnt = BitSliceAccelerator!(Field, I)(slices[0].retro).ctlz;
        if (cnt = -1)
            return false;
        backwardIndex[0] = slices[0].length - cnt;
    }
    else
    {
        do
        {
            static if (DimensionCount!(Slices[0]) == 1)
            {
                if (mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
                {
                    backwardIndex[0] = slices[0].length;
                    return true;
                }
            }
            else
            {
                if (mixin("findImpl!fun(backwardIndex[1 .. $], " ~ frontOf!(Slices.length) ~ ")"))
                {
                    backwardIndex[0] = slices[0].length;
                    return true;
                }
            }
            foreach_reverse(ref slice; slices)
                slice.popFront;
        }
        while(!slices[0].empty);
        return false;
    }
}

/++
Finds an index such that
`pred(slices[0][index], ..., slices[$-1][index])` is `true`.

Params:
    pred = A predicate.

See_also:
    $(LREF find),
    $(LREF any).
Optimization:
    `findIndex!"a"` has accelerated specialization for slices created with $(REF bitwise, mir,ndslice,topology), $(REF bitSlice, mir,ndslice,allocation).
+/
template findIndex(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        Multidimensional index such that the predicate is true.
        Index equals `size_t.max`, if the predicate evaluates `false` for all indexes.
    Constraints:
        All slices must have the same shape.
    +/
    @optmath Select!(DimensionCount!(Slices[0]) > 1, size_t[DimensionCount!(Slices[0])], size_t) findIndex(Slices...)(Slices slices)
        if (Slices.length)
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        size_t[DimensionCount!(Slices[0])] ret = -1;
        auto lengths = slices[0].shape;
        if (!slices[0].anyEmpty && findImpl!pred(ret, slices))
            foreach (i; Iota!(DimensionCount!(Slices[0])))
                ret[i] = lengths[i] - ret[i];
        static if (DimensionCount!(Slices[0]) > 1)
            return ret;
        else
            return ret[0];
    }
    else
        alias findIndex = .findIndex!(naryFun!pred);
}

/// Ranges and arrays
version(mir_test)
unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto sl = iota(5);
    size_t index = sl.findIndex!"a == 3";

    assert(index == 3);
    assert(sl[index] == 3);

    assert(sl.findIndex!(a => a == 8) == size_t.max);
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);
    size_t[2] index = sl.findIndex!(a => a == 3);

    assert(sl[index] == 3);

    index = sl.findIndex!"a == 6";
    assert(index[0] == size_t.max);
    assert(index[1] == size_t.max);
}

/++
Finds a backward index such that
`pred(slices[0].backward(index), ..., slices[$-1].backward(index))` is `true`.

Params:
    pred = A predicate.

Optimization:
    To check if any element was found
    use the last dimension (row index).
    This will slightly optimize the code.
--------
// $-1 instead of 0
if (backwardIndex[$-1])
{
    auto elem1 = slice1.backward(backwardIndex);
    //...
    auto elemK = sliceK.backward(backwardIndex);
}
else
{
    // not found
}
--------

See_also:
    $(LREF findIndex),
    $(LREF any),
    $(REF Slice.backward, mir,ndslice,slice).

Optimization:
    `find!"a"` has accelerated specialization for slices created with $(REF bitwise, mir,ndslice,topology), $(REF bitSlice, mir,ndslice,allocation).
+/
template find(alias pred)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        Multidimensional backward index such that the predicate is true.
        Backward index equals zeros, if the predicate evaluates `false` for all indexes.
    Constraints:
        All slices must have the same shape.
    +/
    @optmath Select!(DimensionCount!(Slices[0]) > 1, size_t[DimensionCount!(Slices[0])], size_t) find(Slices...)(auto ref Slices slices)
        if (Slices.length && allSatisfy!(hasShape, Slices))
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        size_t[DimensionCount!(Slices[0])] ret;
        if (!slices[0].anyEmpty)
            findImpl!pred(ret, slices);
        static if (DimensionCount!(Slices[0]) > 1)
            return ret;
        else
            return ret[0];
    }
    else
        alias find = .find!(naryFun!pred);
}

/// Ranges and arrays
version(mir_test)
unittest
{
    import std.range : iota;

    auto sl = iota(10);
    size_t index = sl.find!"a == 3";

    assert(sl[$ - index] == 3);
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);
    size_t[2] bi = sl.find!"a == 3";
    assert(sl.backward(bi) == 3);
    assert(sl[$ - bi[0], $ - bi[1]] == 3);

    bi = sl.find!"a == 6";
    assert(bi[0] == 0);
    assert(bi[1] == 0);
}

/// Multiple slices
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    size_t[2] bi = find!((a, b) => a * b == 39)(a, b);
    assert(a.backward(bi) == 3);
    assert(b.backward(bi) == 13);
}

/// Zipped slices
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    size_t[2] bi = zip!true(a, b).find!"a.a * a.b == 39";

    assert(a.backward(bi) == 3);
    assert(b.backward(bi) == 13);
}

/// Mutation on-the-fly
pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3).as!double.slice;

    static bool pred(T)(ref T a)
    {
        if (a == 5)
            return true;
        a = 8;
        return false;
    }

    size_t[2] bi = sl.find!pred;

    assert(bi == [1, 1]);
    assert(sl.backward(bi) == 5);

    // sl was changed
    assert(sl == [[8, 8, 8],
                  [8, 8, 5]]);
}

@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    size_t i;
    size_t[2] bi = iota(2, 0).find!((elem){i++; return true;});
    assert(i == 0);
    assert(bi == [0, 0]);
}

size_t anyImpl(alias fun, Slices...)(scope Slices slices)
    if (Slices.length)
{
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(FieldIterator!(BitField!(Field, I))), Field, I))
    {
        return BitSliceAccelerator!(Field, I)(slices[0]).any;
    }
    else
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(RetroIterator!(FieldIterator!(BitField!(Field, I)))), Field, I))
    {
        // pragma(msg, S);
        import mir.ndslice.topology: retro;
        return .anyImpl!fun(slices[0].retro);
    }
    else
    {
        do
        {
            static if (DimensionCount!(Slices[0]) == 1)
            {
                if (mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
                    return true;
            }
            else
            {
                if (mixin("anyImpl!fun(" ~ frontOf!(Slices.length) ~ ")"))
                    return true;
            }
            foreach_reverse(ref slice; slices)
                slice.popFront;
        }
        while(!slices[0].empty);
        return false;
    }
}

/++
Like $(LREF find), but only returns whether or not the search was successful.

Params:
    pred = The predicate.
Optimization:
    `any!"a"` has accelerated specialization for slices created with $(REF bitwise, mir,ndslice,topology), $(REF bitSlice, mir,ndslice,allocation).
+/
template any(alias pred = "a")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices, ranges, and arrays.
    Returns:
        `true` if the search was successful and `false` otherwise.
    Constraints:
        All slices must have the same shape.
    +/
    @optmath bool any(Slices...)(scope Slices slices)
        if ((Slices.length == 1 || !__traits(isSame, pred, "a")) && Slices.length)
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        static if (areAllContiguousSlices!Slices)
        {
            import mir.ndslice.topology: flattened;
            return mixin(`.any!pred(` ~ allFlattened!(Slices.length) ~`)`);
        }
        else
        {
            return !slices[0].anyEmpty && anyImpl!pred(slices);
        }
    }
    else
        alias any = .any!(naryFun!pred);
}

/// Ranges and arrays
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto r = iota(6);

    assert(r.any!"a == 3");
    assert(!r.any!"a == 6");
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    assert(sl.any!"a == 3");
    assert(!sl.any!"a == 6");
}

/// Multiple slices
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    assert(any!((a, b) => a * b == 39)(a, b));
}

/// Zipped slices
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto a = iota(2, 3);
    // 10 11 12
    // 13 14 15
    auto b = iota([2, 3], 10);

    // slices must have the same strides

    assert(zip!true(a, b).any!"a.a * a.b == 39");
}

/// Mutation on-the-fly
pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3).as!double.slice;

    static bool pred(T)(ref T a)
    {
        if (a == 5)
            return true;
        a = 8;
        return false;
    }

    assert(sl.any!pred);

    // sl was changed
    assert(sl == [[8, 8, 8],
                  [8, 8, 5]]);
}

size_t allImpl(alias fun, Slices...)(scope Slices slices)
    if (Slices.length)
{
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(FieldIterator!(BitField!(Field, I))), Field, I))
    {
        return BitSliceAccelerator!(Field, I)(slices[0]).all;
    }
    else
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(RetroIterator!(FieldIterator!(BitField!(Field, I)))), Field, I))
    {
        // pragma(msg, S);
        import mir.ndslice.topology: retro;
        return .allImpl!fun(slices[0].retro);
    }
    else
    {
        do
        {
            static if (DimensionCount!(Slices[0]) == 1)
            {
                if (!mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
                    return false;
            }
            else
            {
                if (!mixin("allImpl!fun(" ~ frontOf!(Slices.length) ~ ")"))
                    return false;
            }
            foreach_reverse(ref slice; slices)
                slice.popFront;
        }
        while(!slices[0].empty);
        return true;
    }
}

/++
Checks if all of the elements verify `pred`.

Params:
    pred = The predicate.
Optimization:
    `all!"a"` has accelerated specialization for slices created with $(REF bitwise, mir,ndslice,topology), $(REF bitSlice, mir,ndslice,allocation).
+/
template all(alias pred = "a")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = One or more slices.
    Returns:
        `true` all of the elements verify `pred` and `false` otherwise.
    Constraints:
        All slices must have the same shape.
    +/
    @optmath bool all(Slices...)(scope Slices slices)
        if ((Slices.length == 1 || !__traits(isSame, pred, "a")) && Slices.length)
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        static if (areAllContiguousSlices!Slices)
        {
            import mir.ndslice.topology: flattened;
            return mixin(`.all!pred(` ~ allFlattened!(Slices.length) ~`)`);
        }
        else
        {
            return slices[0].anyEmpty || allImpl!pred(slices);
        }
    }
    else
        alias all = .all!(naryFun!pred);
}

/// Ranges and arrays
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto r = iota(6);

    assert(r.all!"a < 6");
    assert(!r.all!"a < 5");
}

///
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    assert(sl.all!"a < 6");
    assert(!sl.all!"a < 5");
}

/// Multiple slices
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);

    assert(all!"a - b == 0"(sl, sl));
}

/// Zipped slices
@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota, zip;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3);


    assert(zip!true(sl, sl).all!"a.a - a.b == 0");
}

/// Mutation on-the-fly
pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    // 0 1 2
    // 3 4 5
    auto sl = iota(2, 3).as!double.slice;

    static bool pred(T)(ref T a)
    {
        if (a < 4)
        {
            a = 8;
            return true;
        }
        return false;
    }

    assert(!sl.all!pred);

    // sl was changed
    assert(sl == [[8, 8, 8],
                  [8, 4, 5]]);
}

@safe pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;
    size_t i;
    assert(iota(2, 0).all!((elem){i++; return true;}));
    assert(i == 0);
}

/++
Counts elements in slices according to the `fun`.
Params:
    fun = A predicate.

Optimization:
    `count!"a"` has accelerated specialization for slices created with $(REF bitwise, mir,ndslice,topology), $(REF bitSlice, mir,ndslice,allocation).
+/
template count(alias fun)
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!fun, fun))
    /++
    Params:
        slices = One or more slices, ranges, and arrays.

    Returns: The number elements according to the `fun`.

    Constraints:
        All slices must have the same shape.
    +/
    @optmath size_t count(Slices...)(scope Slices slices)
        if (Slices.length)
    {
        static if (Slices.length > 1)
            slices.checkShapesMatch;
        static if (__traits(isSame, fun, naryFun!"true"))
        {
            return slices[0].elementCount;
        }
        else
        static if (areAllContiguousSlices!Slices)
        {
            import mir.ndslice.topology: flattened;
            return mixin(`.count!fun(` ~ allFlattened!(Slices.length) ~`)`);
        }
        else
        {
            if (slices[0].anyEmpty)
                return 0;
            return countImpl!(fun, Slices)(slices);
        }
    }
    else
        alias count = .count!(naryFun!fun);

}

/// Ranges and arrays
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import std.range : iota;
    // 0 1 2 3 4 5
    auto r = iota(6);

    assert(r.count!"true" == 6);
    assert(r.count!"a" == 5);
    assert(r.count!"a % 2" == 3);
}

/// Single slice
version(mir_test)
unittest
{
    import mir.ndslice.topology : iota;

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota(2, 3);

    assert(sl.count!"true" == 6);
    assert(sl.count!"a" == 5);
    assert(sl.count!"a % 2" == 3);
}

/// Accelerated set bit count
version(mir_test)
unittest
{
    import mir.ndslice.topology: retro, iota, bitwise;
    import mir.ndslice.allocation: slice;

    //| 0 1 2 |
    //| 3 4 5 |
    auto sl = iota!size_t(2, 3).bitwise;

    assert(sl.count!"true" == 6 * size_t.sizeof * 8);

    assert(sl.slice.count!"a" == 7);

    // accelerated
    assert(sl.count!"a" == 7);
    assert(sl.retro.count!"a" == 7);

    auto sl2 = iota!ubyte([6], 128).bitwise;
    // accelerated
    assert(sl2.count!"a" == 13);
    assert(sl2[4 .. $].count!"a" == 13);
    assert(sl2[4 .. $ - 1].count!"a" == 12);
    assert(sl2[4 .. $ - 1].count!"a" == 12);
    assert(sl2[41 .. $ - 1].count!"a" == 1);
}

unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: bitwise, assumeFieldsHaveZeroShift;
    auto sl = slice!uint([6]).bitwise;
    auto slb = slice!ubyte([6]).bitwise;
    slb[4] = true;
    auto d = slb[4];
    auto c = assumeFieldsHaveZeroShift(slb & ~slb);
    // pragma(msg, typeof(c));
    assert(!sl.any);
    assert((~sl).all);
    // pragma(msg, typeof(~slb));
    // pragma(msg, typeof(~slb));
    // assert(sl.findIndex);
}

/++
Compares two or more slices for equality, as defined by predicate `pred`.

See_also: $(NDSLICEREF slice, Slice.opEquals)

Params:
    pred = The predicate.
+/
template equal(alias pred = "a == b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        slices = Two or more slices, slices, ranges, and arrays.

    Returns:
        `true` any of the elements verify `pred` and `false` otherwise.
    +/
    bool equal(Slices...)(scope Slices slices)
        if (Slices.length >= 2)
    {
        enum msg = "all arguments must be slices" ~ tailErrorMessage!();
        enum msgShape = "all slices must have the same dimension count"  ~ tailErrorMessage!();
        import mir.internal.utility;
        foreach (i, Slice; Slices)
        {
            // static assert (isSlice!Slice, msg);
            static if (i)
            {
                static assert (DimensionCount!(Slices[i]) == DimensionCount!(Slices[0]));
                foreach (j; Iota!(DimensionCount!(Slices[0])))
                    if (slices[i].shape[j] != slices[0].shape[j])
                        goto False;
            }
        }
        return all!pred(slices);
        False: return false;
    }
    else
        alias equal = .equal!(naryFun!pred);
}

/// Ranges and arrays
@safe pure nothrow
version(mir_test) unittest
{
    import std.range : iota;
    auto r = iota(6);
    assert(r.equal([0, 1, 2, 3, 4, 5]));
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    assert(equal(sl1, sl1));
    assert(sl1 == sl1); //can also use opEquals for two Slices
    assert(equal!"2 * a == b + c"(sl1, sl1, sl1));
    
    assert(equal!"a < b"(sl1, sl2));

    assert(!equal(sl1[0 .. $ - 1], sl1));
    assert(!equal(sl1[0 .. $, 0 .. $ - 1], sl1));
}

ptrdiff_t cmpImpl(alias pred, A, B)
    (scope A sl1, scope B sl2)
    if (DimensionCount!A == DimensionCount!B)
{
    for (;;)
    {
        static if (DimensionCount!A == 1)
        {
            import mir.functional : naryFun;
            if (naryFun!pred(sl1.front, sl2.front))
                return -1;
            if (naryFun!pred(sl2.front, sl1.front))
                return 1;
        }
        else
        {
            if (auto res = .cmpImpl!pred(sl1.front, sl2.front))
                return res;
        }
        sl1.popFront;
        if (sl1.empty)
            return -cast(ptrdiff_t)(sl2.length > 1);
        sl2.popFront;
        if (sl2.empty)
            return 1;
    }
}

/++
Performs three-way recursive lexicographical comparison on two slices according to predicate `pred`.
Iterating `sl1` and `sl2` in lockstep, `cmp` compares each `N-1` dimensional element `e1` of `sl1`
with the corresponding element `e2` in `sl2` recursively.
If one of the slices has been finished,`cmp` returns a negative value if `sl1` has fewer elements than `sl2`,
a positive value if `sl1` has more elements than `sl2`,
and `0` if the ranges have the same number of elements.

Params:
    pred = The predicate.
+/
template cmp(alias pred = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!pred, pred))
    /++
    Params:
        sl1 = First slice, range, or array.
        sl2 = Second slice, range, or array.

    Returns:
        `0` if both ranges compare equal.
        Negative value if the first differing element of `sl1` is less than the corresponding
        element of `sl2` according to `pred`.
        Positive value if the first differing element of `sl2` is less than the corresponding
        element of `sl1` according to `pred`.
    +/
    ptrdiff_t cmp(A, B)
        (scope A sl1, scope B sl2)
        if (DimensionCount!A == DimensionCount!B)
    {
        auto b = sl2.anyEmpty;
        if (sl1.anyEmpty)
        {
            if (!b)
                return -1;
            auto sh1 = sl1.shape;
            auto sh2 = sl2.shape;
            foreach (i; Iota!(DimensionCount!A))
                if (ptrdiff_t ret = sh1[i] - sh2[i])
                    return ret;
            return 0;
        }
        if (b)
            return 1;
        return cmpImpl!pred(sl1, sl2);
    }
    else
        alias cmp = .cmp!(naryFun!pred);
}

/// Ranges and arrays
@safe pure nothrow
version(mir_test) unittest
{
    import std.range : iota;

    // 0 1 2 3 4 5
    auto r1 = iota(0, 6);
    // 1 2 3 4 5 6
    auto r2 = iota(1, 7);

    assert(cmp(r1, r1) == 0);
    assert(cmp(r1, r2) < 0);
    assert(cmp!"a >= b"(r1, r2) > 0);
}

///
@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    // 0 1 2
    // 3 4 5
    auto sl1 = iota(2, 3);
    // 1 2 3
    // 4 5 6
    auto sl2 = iota([2, 3], 1);

    assert(cmp(sl1, sl1) == 0);
    assert(cmp(sl1, sl2) < 0);
    assert(cmp!"a >= b"(sl1, sl2) > 0);
}

@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.ndslice.topology : iota;

    auto sl1 = iota(2, 3);
    auto sl2 = iota([2, 3], 1);

    assert(cmp(sl1[0 .. $ - 1], sl1) < 0);
    assert(cmp(sl1, sl1[0 .. $, 0 .. $ - 1]) > 0);

    assert(cmp(sl1[0 .. $ - 2], sl1) < 0);
    assert(cmp(sl1, sl1[0 .. $, 0 .. $ - 3]) > 0);
    assert(cmp(sl1[0 .. $, 0 .. $ - 3], sl1[0 .. $, 0 .. $ - 3]) == 0);
    assert(cmp(sl1[0 .. $, 0 .. $ - 3], sl1[0 .. $ - 1, 0 .. $ - 3]) > 0);
    assert(cmp(sl1[0 .. $ - 1, 0 .. $ - 3], sl1[0 .. $, 0 .. $ - 3]) < 0);
}

size_t countImpl(alias fun, Slices...)(scope Slices slices)
{
    size_t ret;
    alias S = Slices[0];
    import mir.functional: naryFun;
    import mir.ndslice.iterator: FieldIterator, RetroIterator;
    import mir.ndslice.field: BitField;
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(FieldIterator!(BitField!(Field, I))), Field, I))
    {
        ret = BitSliceAccelerator!(Field, I)(slices[0]).ctpop;
    }
    else
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(RetroIterator!(FieldIterator!(BitField!(Field, I)))), Field, I))
    {
        // pragma(msg, S);
        import mir.ndslice.topology: retro;
        ret = .countImpl!fun(slices[0].retro);
    }
    else
    do
    {
        static if (DimensionCount!(Slices[0]) == 1)
        {
            if(mixin("fun(" ~ frontOf!(Slices.length) ~ ")"))
                ret++;
        }
        else
            ret += mixin(".countImpl!fun(" ~ frontOf!(Slices.length) ~ ")");
        foreach_reverse(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return ret;
}

private template selectBackOf(size_t N, string input)
{
    static if (N == 0)
        enum selectBackOf = "";
    else
    {
        enum i = N - 1;
        enum selectBackOf = selectBackOf!(i, input) ~
                     "slices[" ~ i.stringof ~ "].selectBack!0(" ~ input ~ "), ";
    }
}

private template frontSelectFrontOf(size_t N, string input)
{
    static if (N == 0)
        enum frontSelectFrontOf = "";
    else
    {
        enum i = N - 1;
        enum frontSelectFrontOf = frontSelectFrontOf!(i, input) ~
            "slices[" ~ i.stringof ~ "].front!0.selectFront!0(" ~ input ~ "), ";
    }
}

/++
Returns: max length across all dimensions.
+/
size_t maxLength(S)(auto ref scope S s)
 if (hasShape!S)
{
    auto shape = s.shape;
    size_t length = 0;
    foreach(i; Iota!(shape.length))
        if (shape[i] > length)
            length = shape[i];
    return length;
}

/++
The call `eachLower!(fun)(slice1, ..., sliceN)` evaluates `fun` on the lower
triangle in `slice1, ..., sliceN` respectively.

`eachLower` allows iterating multiple slices in the lockstep.

Params:
    fun = A function
See_Also:
    This is functionally similar to $(LREF each).
+/
template eachLower(alias fun)
{
    import mir.functional : naryFun;

    static if (__traits(isSame, naryFun!fun, fun))
    {
        /++
        Params:
            inputs = One or more two-dimensional slices and an optional
                     integer, `k`.

            The value `k` determines which diagonals will have the function
            applied:
            For k = 0, the function is also applied to the main diagonal
            For k = 1 (default), only the non-main diagonals below the main
            diagonal will have the function applied.
            For k > 1, fewer diagonals below the main diagonal will have the
            function applied.
            For k < 0, more diagonals above the main diagonal will have the
            function applied.
        +/
        void eachLower(Inputs...)(scope Inputs inputs)
            if (((Inputs.length > 1) && 
                 (isIntegral!(Inputs[$ - 1]))) || 
                (Inputs.length))
        {
            import mir.ndslice.traits : isMatrix;

            size_t val;

            static if ((Inputs.length > 1) && (isIntegral!(Inputs[$ - 1])))
            {
                immutable(sizediff_t) k = inputs[$ - 1];
                alias Slices = Inputs[0..($ - 1)];
                alias slices = inputs[0..($ - 1)];
            }
            else
            {
                enum sizediff_t k = 1;
                alias Slices = Inputs;
                alias slices = inputs;
            }

            static assert (allSatisfy!(isMatrix, Slices),
                "eachLower: Every slice input must be a two-dimensional slice");
            static if (Slices.length > 1)
                slices.checkShapesMatch;
            if (slices[0].anyEmpty)
                return;

            foreach(ref slice; slices)
                assert(!slice.empty);

            immutable(size_t) m = slices[0].length!0;
            immutable(size_t) n = slices[0].length!1;

            if ((n + k) < m)
            {
                val = m - (n + k);
                mixin(".eachImpl!fun(" ~ selectBackOf!(Slices.length, "val") ~ ");");
            }

            size_t i;

            if (k > 0)
            {
                foreach(ref slice; slices)
                    slice.popFrontExactly!0(k);
                i = k;
            }

            do
            {
                val = i - k + 1;
                mixin(".eachImpl!fun(" ~ frontSelectFrontOf!(Slices.length, "val") ~ ");");

                foreach(ref slice; slices)
                        slice.popFront!0;
                i++;
            } while ((i < (n + k)) && (i < m));
        }
    }
    else
    {
        alias eachLower = .eachLower!(naryFun!fun);
    }
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota, canonical, universal;
    alias AliasSeq(T...) = T;

    pure nothrow
    void test(alias func)()
    {
        //| 1 2 3 |
        //| 4 5 6 |
        //| 7 8 9 |
        auto m = func(iota([3, 3], 1).slice);
        m.eachLower!"a = 0"(0);
        assert(m == [
            [0, 2, 3],
            [0, 0, 6],
            [0, 0, 0]]);
    }

    @safe pure nothrow @nogc
    T identity(T)(T x)
    {
        return x;
    }

    alias kinds = AliasSeq!(identity, canonical, universal);
    test!(kinds[0]);
    test!(kinds[1]);
    test!(kinds[2]);
}

///
pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachLower!"a = 0";
    assert(m == [
        [1, 2, 3],
        [0, 5, 6],
        [0, 0, 9]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachLower!"a = 0"(-1);
    assert(m == [
        [0, 0, 3],
        [0, 0, 0],
        [0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachLower!"a = 0"(2);
    assert(m == [
        [1, 2, 3],
        [4, 5, 6],
        [0, 8, 9]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachLower!"a = 0"(-2);
    assert(m == [
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachLower!"a = 0"(0);
    assert(m == [
        [0, 2, 3, 4],
        [0, 0, 7, 8],
        [0, 0, 0, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachLower!"a = 0";
    assert(m == [
        [1, 2, 3, 4],
        [0, 6, 7, 8],
        [0, 0, 11, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachLower!"a = 0"(-1);
    assert(m == [
        [0, 0, 3, 4],
        [0, 0, 0, 8],
        [0, 0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachLower!"a = 0"(2);
    assert(m == [
        [1, 2, 3, 4],
        [5, 6, 7, 8],
        [0, 10, 11, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachLower!"a = 0"(-2);
    assert(m == [
        [0, 0, 0, 4],
        [0, 0, 0, 0],
        [0, 0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachLower!"a = 0"(0);
    assert(m == [
        [0, 2, 3],
        [0, 0, 6],
        [0, 0, 0],
        [0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachLower!"a = 0";
    assert(m == [
        [1, 2, 3],
        [0, 5, 6],
        [0, 0, 9],
        [0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachLower!"a = 0"(-1);
    assert(m == [
        [0, 0, 3],
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachLower!"a = 0"(2);
    assert(m == [
        [1, 2, 3],
        [4, 5, 6],
        [0, 8, 9],
        [0, 0, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachLower!"a = 0"(-2);
    assert(m == [
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0]]);
}

/// Swap two slices
pure nothrow
version(mir_test) unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    //| 6 7 8 |
    auto a = iota([3, 3]).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    //| 16 17 18 |
    auto b = iota([3, 3], 10).as!double.slice;

    eachLower!swap(a, b);

    assert(a == [
        [ 0,  1, 2],
        [13,  4, 5],
        [16, 17, 8]]);
    assert(b == [
        [10, 11, 12],
        [ 3, 14, 15],
        [ 6,  7, 18]]);
}

/// Swap two zipped slices
pure nothrow
version(mir_test) unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, zip, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    //| 6 7 8 |
    auto a = iota([3, 3]).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    //| 16 17 18 |
    auto b = iota([3, 3], 10).as!double.slice;

    auto z = zip(a, b);

    z.eachLower!(z => swap(z.a, z.b));

    assert(a == [
        [ 0,  1, 2],
        [13,  4, 5],
        [16, 17, 8]]);
    assert(b == [
        [10, 11, 12],
        [ 3, 14, 15],
        [ 6,  7, 18]]);
}

private template frontSelectBackOf(size_t N, string input)
{
    static if (N == 0)
        enum frontSelectBackOf = "";
    else
    {
        enum i = N - 1;
        enum frontSelectBackOf = frontSelectBackOf!(i, input) ~
               "slices[" ~ i.stringof ~ "].front.selectBack!0(" ~ input ~ "), ";
    }
}

private template selectFrontOf(size_t N, string input)
{
    static if (N == 0)
        enum selectFrontOf = "";
    else
    {
        enum i = N - 1;
        enum selectFrontOf = selectFrontOf!(i, input) ~
                    "slices[" ~ i.stringof ~ "].selectFront!0(" ~ input ~ "), ";
    }
}

/++
The call `eachUpper!(fun)(slice1, ..., sliceN)` evaluates `fun` on the upper
triangle in `slice1, ..., sliceN`, respectively.

`eachUpper` allows iterating multiple slices in the lockstep.

Params:
    fun = A function
See_Also:
    This is functionally similar to $(LREF each).
+/
template eachUpper(alias fun)
{
    import mir.functional: naryFun;

    static if (__traits(isSame, naryFun!fun, fun))
    {
        /++
        Params:
            inputs = One or more two-dimensional slices and an optional
                     integer, `k`.

            The value `k` determines which diagonals will have the function
            applied:
            For k = 0, the function is also applied to the main diagonal
            For k = 1 (default), only the non-main diagonals above the main
            diagonal will have the function applied.
            For k > 1, fewer diagonals below the main diagonal will have the
            function applied.
            For k < 0, more diagonals above the main diagonal will have the
            function applied.
        +/
        void eachUpper(Inputs...)(scope Inputs inputs)
            if (((Inputs.length > 1) && 
                 (isIntegral!(Inputs[$ - 1]))) || 
                (Inputs.length))
        {
            import mir.ndslice.traits : isMatrix;

            size_t val;

            static if ((Inputs.length > 1) && (isIntegral!(Inputs[$ - 1])))
            {
                immutable(sizediff_t) k = inputs[$ - 1];
                alias Slices = Inputs[0..($ - 1)];
                alias slices = inputs[0..($ - 1)];
            }
            else
            {
                enum sizediff_t k = 1;
                alias Slices = Inputs;
                alias slices = inputs;
            }

            static assert (allSatisfy!(isMatrix, Slices),
                "eachUpper: Every slice input must be a two-dimensional slice");
            static if (Slices.length > 1)
                slices.checkShapesMatch;
            if (slices[0].anyEmpty)
                return;

            foreach(ref slice; slices)
                assert(!slice.empty);

            immutable(size_t) m = slices[0].length!0;
            immutable(size_t) n = slices[0].length!1;

            size_t i;

            if (k < 0)
            {
                val = -k;
                mixin(".eachImpl!fun(" ~ selectFrontOf!(Slices.length, "val") ~ ");");

                foreach(ref slice; slices)
                    slice.popFrontExactly!0(-k);
                i = -k;
            }

            do
            {
                val = (n - k) - i;
                mixin(".eachImpl!fun(" ~ frontSelectBackOf!(Slices.length, "val") ~ ");");

                foreach(ref slice; slices)
                    slice.popFront;
                i++;
            } while ((i < (n - k)) && (i < m));
        }
    }
    else
    {
        alias eachUpper = .eachUpper!(naryFun!fun);
    }
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota, canonical, universal;

    pure nothrow
    void test(alias func)()
    {
        //| 1 2 3 |
        //| 4 5 6 |
        //| 7 8 9 |
        auto m = func(iota([3, 3], 1).slice);
        m.eachUpper!"a = 0"(0);
        assert(m == [
            [0, 0, 0],
            [4, 0, 0],
            [7, 8, 0]]);
    }

    @safe pure nothrow @nogc
    T identity(T)(T x)
    {
        return x;
    }

    alias kinds = AliasSeq!(identity, canonical, universal);
    test!(kinds[0]);
    test!(kinds[1]);
    test!(kinds[2]);
}

///
pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachUpper!"a = 0";
    assert(m == [
        [1, 0, 0],
        [4, 5, 0],
        [7, 8, 9]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachUpper!"a = 0"(-1);
    assert(m == [
        [0, 0, 0],
        [0, 0, 0],
        [7, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachUpper!"a = 0"(2);
    assert(m == [
        [1, 2, 0],
        [4, 5, 6],
        [7, 8, 9]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1 2 3 |
    //| 4 5 6 |
    //| 7 8 9 |
    auto m = iota([3, 3], 1).slice;
    m.eachUpper!"a = 0"(-2);
    assert(m == [
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachUpper!"a = 0"(0);
    assert(m == [
        [0, 0, 0, 0],
        [5, 0, 0, 0],
        [9, 10, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachUpper!"a = 0";
    assert(m == [
        [1, 0, 0, 0],
        [5, 6, 0, 0],
        [9, 10, 11, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachUpper!"a = 0"(-1);
    assert(m == [
        [0, 0, 0, 0],
        [0, 0, 0, 0],
        [9, 0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachUpper!"a = 0"(2);
    assert(m == [
        [1, 2, 0, 0],
        [5, 6, 7, 0],
        [9, 10, 11, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //| 1  2  3  4 |
    //| 5  6  7  8 |
    //| 9 10 11 12 |
    auto m = iota([3, 4], 1).slice;
    m.eachUpper!"a = 0"(-2);
    assert(m == [
        [0, 0, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 0, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachUpper!"a = 0"(0);
    assert(m == [
        [0, 0, 0],
        [4, 0, 0],
        [7, 8, 0],
        [10, 11, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachUpper!"a = 0";
    assert(m == [
        [1, 0, 0],
        [4, 5, 0],
        [7, 8, 9],
        [10, 11, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachUpper!"a = 0"(-1);
    assert(m == [
        [0, 0, 0],
        [0, 0, 0],
        [7, 0, 0],
        [10, 11, 0]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachUpper!"a = 0"(2);
    assert(m == [
        [1, 2, 0],
        [4, 5, 6],
        [7, 8, 9],
        [10, 11, 12]]);
}

pure nothrow
version(mir_test) unittest
{
    import mir.ndslice.allocation: slice;
    import mir.ndslice.topology: iota;

    //|  1  2  3 |
    //|  4  5  6 |
    //|  7  8  9 |
    //| 10 11 12 |
    auto m = iota([4, 3], 1).slice;
    m.eachUpper!"a = 0"(-2);
    assert(m == [
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0],
        [10, 0, 0]]);
}

/// Swap two slices
pure nothrow
version(mir_test) unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    //| 6 7 8 |
    auto a = iota([3, 3]).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    //| 16 17 18 |
    auto b = iota([3, 3], 10).as!double.slice;

    eachUpper!swap(a, b);

    assert(a == [
        [0, 11, 12],
        [3,  4, 15],
        [6,  7,  8]]);
    assert(b == [
        [10,  1,  2],
        [13, 14,  5],
        [16, 17, 18]]);
}

/// Swap two zipped slices
pure nothrow
version(mir_test) unittest
{
    import mir.utility : swap;
    import mir.ndslice.allocation : slice;
    import mir.ndslice.topology : as, zip, iota;

    //| 0 1 2 |
    //| 3 4 5 |
    //| 6 7 8 |
    auto a = iota([3, 3]).as!double.slice;
    //| 10 11 12 |
    //| 13 14 15 |
    //| 16 17 18 |
    auto b = iota([3, 3], 10).as!double.slice;

    auto z = zip(a, b);

    z.eachUpper!(z => swap(z.a, z.b));

    assert(a == [
        [0, 11, 12],
        [3,  4, 15],
        [6,  7,  8]]);
    assert(b == [
        [10,  1,  2],
        [13, 14,  5],
        [16, 17, 18]]);
}

// uniq
/**
Lazily iterates unique consecutive elements of the given range (functionality
akin to the $(HTTP wikipedia.org/wiki/_Uniq, _uniq) system
utility). Equivalence of elements is assessed by using the predicate
$(D pred), by default $(D "a == b"). The predicate is passed to
$(REF nary, mir,functional), and can either accept a string, or any callable
that can be executed via $(D pred(element, element)). If the given range is
bidirectional, $(D uniq) also yields a
`std,range,primitives`.
Params:
    pred = Predicate for determining equivalence between range elements.
    r = An input range of elements to filter.
Returns:
    An input range of
    consecutively unique elements in the original range. If `r` is also a
    forward range or bidirectional range, the returned range will be likewise.
*/
Uniq!(naryFun!pred, Range) uniq(alias pred = "a == b", Range)(auto ref Range r)
if (isInputRange!Range && is(typeof(naryFun!pred(r.front, r.front)) == bool))
{
    return typeof(return)(r);
}

///
@safe version(mir_test) unittest
{
    import std.algorithm.comparison : equal;
    import std.algorithm.mutation : copy;

    int[] arr = [ 1, 2, 2, 2, 2, 3, 4, 4, 4, 5 ];
    assert(equal(uniq(arr), [ 1, 2, 3, 4, 5 ][]));

    // Filter duplicates in-place using copy
    arr.length -= arr.uniq().copy(arr).length;
    assert(arr == [ 1, 2, 3, 4, 5 ]);

    // Note that uniqueness is only determined consecutively; duplicated
    // elements separated by an intervening different element will not be
    // eliminated:
    assert(equal(uniq([ 1, 1, 2, 1, 1, 3, 1]), [1, 2, 1, 3, 1]));
}

/++
Authros: $(HTTP erdani.com, Andrei Alexandrescu) (original Phobos code), Ilya Yaroshenko (betterC rework)
+/
struct Uniq(alias pred, Range)
{
    Range _input;

    // this()(auto ref Range input)
    // {
    //     alias AliasSeq(T...) = T;
    //     import mir.functional: forward;
    //     AliasSeq!_input = forward!input;
    // }

    ref opSlice() inout
    {
        return this;
    }

    void popFront() scope
    {
        assert(!empty, "Attempting to popFront an empty uniq.");
        auto last = _input.front;
        do
        {
            _input.popFront();
        }
        while (!_input.empty && pred(last, _input.front));
    }

    @property ElementType!Range front()
    {
        assert(!empty, "Attempting to fetch the front of an empty uniq.");
        return _input.front;
    }

    static if (isBidirectionalRange!Range)
    {
        void popBack() scope
        {
            assert(!empty, "Attempting to popBack an empty uniq.");
            auto last = _input.back;
            do
            {
                _input.popBack();
            }
            while (!_input.empty && pred(last, _input.back));
        }

        @property ElementType!Range back() scope return
        {
            assert(!empty, "Attempting to fetch the back of an empty uniq.");
            return _input.back;
        }
    }

    static if (isInfinite!Range)
    {
        enum bool empty = false;  // Propagate infiniteness.
    }
    else
    {
        @property bool empty() const { return _input.empty; }
    }

    static if (isForwardRange!Range)
    {
        @property typeof(this) save() scope return {
            return typeof(this)(_input.save);
        }
    }
}

version(none)
@safe version(mir_test) unittest
{
    import std.algorithm.comparison : equal;
    import std.internal.test.dummyrange;
    import std.range;

    int[] arr = [ 1, 2, 2, 2, 2, 3, 4, 4, 4, 5 ];
    auto r = uniq(arr);
    static assert(isForwardRange!(typeof(r)));

    assert(equal(r, [ 1, 2, 3, 4, 5 ][]));
    assert(equal(retro(r), retro([ 1, 2, 3, 4, 5 ][])));

    foreach (DummyType; AllDummyRanges)
    {
        DummyType d;
        auto u = uniq(d);
        assert(equal(u, [1,2,3,4,5,6,7,8,9,10]));

        static assert(d.rt == RangeType.Input || isForwardRange!(typeof(u)));

        static if (d.rt >= RangeType.Bidirectional)
        {
            assert(equal(retro(u), [10,9,8,7,6,5,4,3,2,1]));
        }
    }
}

@safe version(mir_test) unittest // https://issues.dlang.org/show_bug.cgi?id=17264
{
    import std.algorithm.comparison : equal;

    const(int)[] var = [0, 1, 1, 2];
    assert(var.uniq.equal([0, 1, 2]));
}
