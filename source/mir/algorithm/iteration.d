// Written in the D programming language.
/**
This module contains generic _iteration algorithms.
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
$(T2 filter, Filters elements in a range or an ndslice.)
$(T2 find, Finds backward index.)
$(T2 findIndex, Finds index.)
$(T2 fold, Accumulates all elements (different parameter order than `reduce`).)
$(T2 isSymmetric, Checks if the matrix is symmetric.)
$(T2 maxIndex, Finds index of the maximum.)
$(T2 maxPos, Finds backward index of the maximum.)
$(T2 minIndex, Finds index of the minimum.)
$(T2 minmaxIndex, Finds indices of the minimum and the maximum.)
$(T2 minmaxPos, Finds backward indices of the minimum and the maximum.)
$(T2 minPos, Finds backward index of the minimum.)
$(T2 nBitsToCount, Сount bits until set bit count is reached.)
$(T2 reduce, Accumulates all elements.)
$(T2 uniq, Iterates over the unique elements in a range or an ndslice, which is assumed sorted.)
)

Transform function is represented by $(NDSLICEREF topology, map).

All operators are suitable to change slices using `ref` argument qualification in a function declaration.
Note, that string lambdas in Mir are `auto ref` functions.

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilya Yaroshenko, John Michael Hall, Andrei Alexandrescu (original Phobos code)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments

Authors: , Ilya Yaroshenko (Mir & BetterC rework).
Source: $(PHOBOSSRC std/algorithm/_iteration.d)
Macros:
    NDSLICEREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
    T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
 */
module mir.algorithm.iteration;

import mir.functional: naryFun;
import mir.internal.utility;
import mir.math.common: optmath;
import mir.ndslice.field: BitField;
import mir.ndslice.internal;
import mir.ndslice.iterator: FieldIterator, RetroIterator;
import mir.ndslice.slice;
import mir.primitives;
import mir.qualifier;
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
sizediff_t nBitsToCount(Field, I)(Slice!(FieldIterator!(BitField!(Field, I))) bitSlice, size_t count)
{
    return BitSliceAccelerator!(Field, I)(bitSlice).nBitsToCount(count);
}

///ditto
sizediff_t nBitsToCount(Field, I)(Slice!(RetroIterator!(FieldIterator!(BitField!(Field, I)))) bitSlice, size_t count)
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
            assert(cast(size_t[N])slices[i].fuseShape[0 .. N] == slices[0].shape, msgShape);
        }
    }
}


package(mir) template allFlattened(args...)
{
    static if (args.length)
    {
        alias arg = args[0];
        @optmath @property ls()()
        {
            import mir.ndslice.topology: flattened;
            return flattened(arg);
        }
        alias allFlattened = AliasSeq!(ls, allFlattened!(args[1..$]));
    }
    else
        alias allFlattened = AliasSeq!();
}

private template areAllContiguousSlices(Slices...)
{
    import mir.ndslice.traits: isContiguousSlice;
     static if (allSatisfy!(isContiguousSlice, Slices))
        enum areAllContiguousSlices = Slices[0].N > 1 && areAllContiguousSlicesImpl!(Slices[0].N, Slices[1 .. $]);
     else
        enum areAllContiguousSlices = false;
}

private template areAllContiguousSlicesImpl(size_t N, Slices...)
{
     static if (Slices.length == 0)
        enum areAllContiguousSlicesImpl = true;
     else
        enum areAllContiguousSlicesImpl = Slices[0].N == N && areAllContiguousSlicesImpl!(N, Slices[1 .. $]);
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
            seed = fun(seed, frontOf!slices);
        else
            seed = .reduceImpl!fun(seed, frontOf!slices);
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
            return .reduce!fun(seed, allFlattened!(allLightScope!slices));
        }
        else
        {
            if (slices[0].anyEmpty)
                return cast(Unqual!S) seed;
            static if (is(S : Unqual!S))
                alias UT = Unqual!S;
            else
                alias UT = S;
            return reduceImpl!(fun, UT, Slices)(seed, allLightScope!slices);
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
            return .reduce!fun(seed, allFlattened!(allLightScope!slices));
        }
        else
        {
            if (slices[0].anyEmpty)
                return cast(Unqual!S) seed;
            static if (is(S : Unqual!S))
                alias UT = Unqual!S;
            else
                alias UT = S;
            return reduceImpl!(nonInlinedNaryFun!fun, UT, Slices)(seed, allLightScope!slices);
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
            fun(frontOf!slices);
        else
            .eachImpl!fun(frontOf!slices);
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
            .each!fun(allFlattened!(allLightScope!slices));
        }
        else
        {
            if (slices[0].anyEmpty)
                return;
            eachImpl!fun(allLightScope!slices);
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
        auto eachUploPair(Iterator, SliceKind kind)(Slice!(Iterator, 2, kind) matrix)
        in
        {
            assert(matrix.length!0 == matrix.length!1, "matrix must be square.");
        }
        do
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
                        eachImpl!fun(matrix.lightScope.front!0, matrix.lightScope.front!1);
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
                        auto l = matrix.lightScope.front!1;
                        auto u = matrix.lightScope.front!0;
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
                if (!allImpl!fun(matrix.lightScope.front!0, matrix.lightScope.front!1))
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
            if (minPosImpl!(fun, LightScopeOf!Iterator, N - 1, kind)(backwardIndex[1 .. $], iterator, lightScope(slice).front))
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
            auto r = minmaxPosImpl!(fun, LightScopeOf!Iterator, N - 1, kind)(backwardIndex[1 .. $], iterator, lightScope(slice).front);
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
            auto scopeSlice = lightScope(slice);
            auto it = scopeSlice._iterator;
            LightScopeOf!Iterator[2] iterator = [it, it];
            minmaxPosImpl!(pred, LightScopeOf!Iterator, N, kind)(ret, iterator, scopeSlice);
            foreach (i; Iota!N)
            {
                pret[0]._lengths[i] = ret[i][0];
                pret[1]._lengths[i] = ret[i][1];
            }
            pret[0]._iterator = slice._iterator + (iterator[0] - scopeSlice._iterator);
            pret[1]._iterator = slice._iterator + (iterator[1] - scopeSlice._iterator);
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
Finds a backward indices such that
`slice[indices[0]]` is minimal and `slice[indices[1]]` is maximal elements in the slice.

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
            auto scopeSlice = lightScope(slice);
            auto it = scopeSlice._iterator;
            LightScopeOf!Iterator[2] iterator = [it, it];
            minmaxPosImpl!(pred, LightScopeOf!Iterator, N, kind)(ret, iterator, scopeSlice);
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

    auto indices = s.minmaxIndex;

    assert(indices == [[1, 1], [2, 3]]);
    assert(s[indices[0]] == -4);
    assert(s[indices[1]] ==  8);
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
        typeof(return) ret;
        auto iterator = slice.lightScope._iterator;
        if (!slice.anyEmpty)
        {
            minPosImpl!(pred, LightScopeOf!Iterator, N, kind)(ret._lengths, iterator, lightScope(slice));
            ret._iterator = slice._iterator + (iterator - slice.lightScope._iterator);
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
            auto scopeSlice = lightScope(slice);
            auto iterator = scopeSlice._iterator;
            minPosImpl!(pred, LightScopeOf!Iterator, N, kind)(ret, iterator, scopeSlice);
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
                if (fun(frontOf!slices))
                {
                    backwardIndex[0] = slices[0].length;
                    return true;
                }
            }
            else
            {
                if (findImpl!fun(backwardIndex[1 .. $], frontOf!slices))
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
        Index equals `size_t.max`, if the predicate evaluates `false` for all indices.
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
        if (!slices[0].anyEmpty && findImpl!pred(ret, allLightScope!slices))
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
if (backwardIndex)
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
        Backward index equals zeros, if the predicate evaluates `false` for all indices.
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
            findImpl!pred(ret, allLightScope!slices);
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
        return .anyImpl!fun(lightScope(slices[0]).retro);
    }
    else
    {
        do
        {
            static if (DimensionCount!(Slices[0]) == 1)
            {
                if (fun(frontOf!slices))
                    return true;
            }
            else
            {
                if (anyImpl!fun(frontOf!slices))
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
            return .any!pred(allFlattened!(allLightScope!slices));
        }
        else
        {
            return !slices[0].anyEmpty && anyImpl!pred(allLightScope!slices);
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
        return BitSliceAccelerator!(LightScopeOf!Field, I)(lightScope(slices[0])).all;
    }
    else
    static if (__traits(isSame, fun, naryFun!"a") && is(S : Slice!(RetroIterator!(FieldIterator!(BitField!(Field, I)))), Field, I))
    {
        // pragma(msg, S);
        import mir.ndslice.topology: retro;
        return .allImpl!fun(lightScope(slices[0]).retro);
    }
    else
    {
        do
        {
            static if (DimensionCount!(Slices[0]) == 1)
            {
                if (!fun(frontOf!slices))
                    return false;
            }
            else
            {
                if (!allImpl!fun(frontOf!slices))
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
            return .all!pred(allFlattened!(allLightScope!slices));
        }
        else
        {
            return slices[0].anyEmpty || allImpl!pred(allLightScope!slices);
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
            return .count!fun(allFlattened!(allLightScope!slices));
        }
        else
        {
            if (slices[0].anyEmpty)
                return 0;
            return countImpl!(fun)(allLightScope!slices);
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
    {
        /++
        Params:
            slices = Two or more ndslices, ranges, and arrays.

        Returns:
            `true` any of the elements verify `pred` and `false` otherwise.
        +/
        bool equal(Slices...)(scope Slices slices)
            if (Slices.length >= 2)
        {
            import mir.internal.utility;
            static if (allSatisfy!(hasShape, Slices))
            {
                auto shape0 = slices[0].shape;
                enum N = DimensionCount!(Slices[0]);
                foreach (ref slice; slices[1 .. $])
                {
                    if (slice.shape != shape0)
                        goto False;
                }
                return all!pred(allLightScope!slices);
            }
            else
            {
                for(;;)
                {
                    auto empty = slices[0].empty;
                    foreach (ref slice; slices[1 .. $])
                    {
                        if (slice.empty != empty)
                            goto False;
                    }
                    if (empty)
                        return true;
                    if (!pred(frontOf!slices))
                        goto False;
                    foreach (ref slice; slices)
                        slice.popFront;
                }
            }
            False: return false;
        }
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

@safe pure nothrow @nogc
version(mir_test) unittest
{
    import mir.math.common: approxEqual;
    import mir.ndslice.allocation: rcslice;
    import mir.ndslice.topology: as, iota;

    auto x = 5.iota.as!double.rcslice;
    auto y = x.rcslice;

    assert(equal(x, y));
    assert(equal!approxEqual(x, y));
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
        return cmpImpl!pred(lightScope(sl1), lightScope(sl2));
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
        ret = .countImpl!fun(lightScope(slices[0]).retro);
    }
    else
    do
    {
        static if (DimensionCount!(Slices[0]) == 1)
        {
            if(fun(frontOf!slices))
                ret++;
        }
        else
            ret += .countImpl!fun(frontOf!slices);
        foreach_reverse(ref slice; slices)
            slice.popFront;
    }
    while(!slices[0].empty);
    return ret;
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
                .eachImpl!fun(selectBackOf!(val, slices));
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
                .eachImpl!fun(frontSelectFrontOf!(val, slices));

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
                .eachImpl!fun(selectFrontOf!(val, slices));

                foreach(ref slice; slices)
                    slice.popFrontExactly!0(-k);
                i = -k;
            }

            do
            {
                val = (n - k) - i;
                .eachImpl!fun(frontSelectBackOf!(val, slices));

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
*/
template uniq(alias pred = "a == b")
{
    static if (__traits(isSame, naryFun!pred, pred))
    {
        /++
        Params:
            r = An input range of elements to filter.
        Returns:
            An input range of
            consecutively unique elements in the original range. If `r` is also a
            forward range or bidirectional range, the returned range will be likewise.
        +/
        Uniq!(naryFun!pred, Range) uniq(Range)(Range r)
         if (isInputRange!Range && !isSlice!Range)
        {
            import core.lifetime: move;
            return typeof(return)(r.move);
        }

        /// ditto
        auto uniq(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
        {
            import mir.ndslice.topology: flattened; 
            import core.lifetime: move;
            auto r = slice.move.flattened;
            return Uniq!(pred, typeof(r))(move(r));
        }
    }
    else
        alias uniq = .uniq!(naryFun!pred);
}

///
@safe version(mir_test) unittest
{
    int[] arr = [ 1, 2, 2, 2, 2, 3, 4, 4, 4, 5 ];
    assert(equal(uniq(arr), [ 1, 2, 3, 4, 5 ]));

    import std.algorithm.mutation : copy;
    // Filter duplicates in-place using copy
    arr.length -= arr.uniq.copy(arr).length;
    assert(arr == [ 1, 2, 3, 4, 5 ]);

    // Note that uniqueness is only determined consecutively; duplicated
    // elements separated by an intervening different element will not be
    // eliminated:
    assert(equal(uniq([ 1, 1, 2, 1, 1, 3, 1]), [1, 2, 1, 3, 1]));
}

/// N-dimensional case
version(mir_test)
@safe pure unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: byDim, map, iota;

    auto matrix = [ [1, 2, 2], [2, 2, 3], [4, 4, 4] ].fuse;

    assert(matrix.uniq.equal([ 1, 2, 3, 4 ]));

    // unique elements for each row
    assert(matrix.byDim!0.map!uniq.equal!equal([ [1, 2], [2, 3], [4] ]));
}

/++
Authros: $(HTTP erdani.com, Andrei Alexandrescu) (original Phobos code), Ilya Yaroshenko (betterC rework)
+/
struct Uniq(alias pred, Range)
{
    Range _input;

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

    auto ref front() @property
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

        auto ref back() scope return @property
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
        @property typeof(this) save() scope return
        {
            return typeof(this)(_input.save);
        }
    }
}

version(none)
@safe version(mir_test) unittest
{
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
    const(int)[] var = [0, 1, 1, 2];
    assert(var.uniq.equal([0, 1, 2]));
}

@safe version(mir_test) unittest {
    import mir.ndslice.allocation;
    import mir.math.common: approxEqual;
    auto x = rcslice!double(2);
    auto y = rcslice!double(2);
    x[] = [2, 3];
    y[] = [2, 3];
    assert(equal!approxEqual(x,y));
}

/++
Implements the higher order filter function. The predicate is passed to
`mir.functional.naryFun`, and can either accept a string, or any callable
that can be executed via `pred(element)`.
Params:
    pred = Function to apply to each element of range
Returns:
    `filter!(pred)(range)` returns a new range containing only elements `x` in `range` for
    which `pred(x)` returns `true`.
See_Also:
    $(HTTP en.wikipedia.org/wiki/Filter_(higher-order_function), Filter (higher-order function))
Note:
    $(RED User and library code MUST call `empty` method ahead each call of pair or one of `front` and `popFront` methods.)
+/
template filter(alias pred = "a")
{
    static if (__traits(isSame, naryFun!pred, pred))
    {
        /++
        Params:
            r = An input range of elements to filter.
        Returns:
            A new range containing only elements `x` in `range` for which `predicate(x)` returns `true`.
        +/
        Filter!(naryFun!pred, Range) filter(Range)(Range r)
            if (isInputRange!Range && !isSlice!Range)
        {
            import core.lifetime: move;
            return typeof(return)(r.move);
        }

        /// ditto
        auto filter(Iterator, size_t N, SliceKind kind)(Slice!(Iterator, N, kind) slice)
        {
            import mir.ndslice.topology: flattened; 
            import core.lifetime: move;
            auto r = slice.move.flattened;
            return Filter!(pred, typeof(r))(move(r));
        }
    }
    else
        alias filter = .filter!(naryFun!pred);
}

/// ditto
struct Filter(alias pred, Range)
{
    Range _input;
    version(assert) bool _freshEmpty;

    ref opSlice() inout
    {
        return this;
    }

    void popFront() scope
    {
        assert(!_input.empty, "Attempting to popFront an empty Filter.");
        version(assert) assert(_freshEmpty, "Attempting to pop the front of a Filter without calling '.empty' method ahead.");
        version(assert) _freshEmpty = false;
        _input.popFront;
    }

    auto ref front() @property
    {
        assert(!_input.empty, "Attempting to fetch the front of an empty Filter.");
        version(assert) assert(_freshEmpty, "Attempting to fetch the front of a Filter without calling '.empty' method ahead.");
        return _input.front;
    }

    bool empty() @property
    {
        version(assert) _freshEmpty = true;
        for (;;)
        {
            if (auto r = _input.empty)
                return true;
            if (pred(_input.front))
                return false;
            _input.popFront;
        }
    }

    static if (isForwardRange!Range)
    {
        @property typeof(this) save() scope return
        {
            return typeof(this)(_input.save);
        }
    }
}

///
version(mir_test)
@safe pure nothrow unittest
{
    int[] arr = [ 0, 1, 2, 3, 4, 5 ];

    // Filter below 3
    auto small = filter!(a => a < 3)(arr);
    assert(equal(small, [ 0, 1, 2 ]));

    // Filter again, but with Uniform Function Call Syntax (UFCS)
    auto sum = arr.filter!(a => a < 3);
    assert(equal(sum, [ 0, 1, 2 ]));

    // Filter with the default predicate
    auto nonZeros = arr.filter;
    assert(equal(nonZeros, [ 1, 2, 3, 4, 5 ]));

    // In combination with concatenation() to span multiple ranges
    import mir.ndslice.concatenation;

    int[] a = [ 3, -2, 400 ];
    int[] b = [ 100, -101, 102 ];
    auto r = concatenation(a, b).filter!(a => a > 0);
    assert(equal(r, [ 3, 400, 100, 102 ]));

    // Mixing convertible types is fair game, too
    double[] c = [ 2.5, 3.0 ];
    auto r1 = concatenation(c, a, b).filter!(a => cast(int) a != a);
    assert(equal(r1, [ 2.5 ]));
}

/// N-dimensional filtering
version(mir_test)
@safe pure unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: byDim, map;

    auto matrix =
        [[   3,   -2, 400 ],
         [ 100, -101, 102 ]].fuse;

    alias filterPositive = filter!"a > 0";

    // filter all elements in the matrix
    auto r = filterPositive(matrix);
    assert(equal(r, [ 3, 400, 100, 102 ]));

    // filter all elements for each row
    auto rr = matrix.byDim!0.map!filterPositive;
    assert(equal!equal(rr, [ [3, 400], [100, 102] ]));

    // filter all elements for each column
    auto rc = matrix.byDim!1.map!filterPositive;
    assert(equal!equal(rc, [ [3, 100], [], [400, 102] ]));
}

/++
Implements the homonym function (also known as `accumulate`, $(D
compress), `inject`, or `foldl`) present in various programming
languages of functional flavor. The call `fold!(fun)(slice, seed)`
first assigns `seed` to an internal variable `result`,
also called the accumulator. Then, for each element `x` in $(D
slice), `result = fun(result, x)` gets evaluated. Finally, $(D
result) is returned.

Params:
    fun = the predicate function to apply to the elements

See_Also:
    $(HTTP en.wikipedia.org/wiki/Fold_(higher-order_function), Fold (higher-order function))
    $(LREF sum) is similar to `fold!((a, b) => a + b)` that offers
    precise summing of floating point numbers.
    This is functionally equivalent to $(LREF reduce) with the argument order
    reversed.
+/
template fold(alias fun)
{
    /++
    Params:
        slice = A slice, range, and array.
        seed = An initial accumulation value.
    Returns:
        the accumulated result
    +/
    @optmath auto fold(Slice, S)(scope Slice slice, S seed)
    {
        import core.lifetime: move;
        return reduce!fun(seed, slice.move);
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: map;

    auto arr = [1, 2, 3, 4, 5].sliced;

    // Sum all elements
    assert(arr.fold!((a, b) => a + b)(0) == 15);
    assert(arr.fold!((a, b) => a + b)(6) == 21);

    // Can be used in a UFCS chain
    assert(arr.map!(a => a + 1).fold!((a, b) => a + b)(0) == 20);

    // Return the last element of any range
    assert(arr.fold!((a, b) => b)(0) == 5);
}

/// Works for matrices
version(mir_test)
@safe pure
unittest
{
    import mir.ndslice.fuse: fuse;

    auto arr = [
        [1, 2, 3], 
        [4, 5, 6]
    ].fuse;

    assert(arr.fold!((a, b) => a + b)(0) == 21);
}

version(mir_test)
@safe pure nothrow
unittest
{
    import mir.ndslice.topology: map;

    int[] arr = [1, 2, 3, 4, 5];

    // Sum all elements
    assert(arr.fold!((a, b) => a + b)(0) == 15);
    assert(arr.fold!((a, b) => a + b)(6) == 21);

    // Can be used in a UFCS chain
    assert(arr.map!(a => a + 1).fold!((a, b) => a + b)(0) == 20);

    // Return the last element of any range
    assert(arr.fold!((a, b) => b)(0) == 5);
}

version(mir_test)
@safe pure nothrow 
unittest
{
    int[] arr = [1];
    static assert(!is(typeof(arr.fold!()(0))));
    static assert(!is(typeof(arr.fold!(a => a)(0))));
    static assert(is(typeof(arr.fold!((a, b) => a)(0))));
    assert(arr.length == 1);
}

unittest
{
    import mir.rc.array: RCArray;
    import mir.algorithm.iteration: minmaxPos, minPos, maxPos, minmaxIndex, minIndex, maxIndex;

    static immutable a = [0.0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    auto x = RCArray!double(12);
    foreach(i, ref e; x)
        e = a[i];
    auto y = x.asSlice;
    auto z0 = y.minmaxPos;
    auto z1 = y.minPos;
    auto z2 = y.maxPos;
    auto z3 = y.minmaxIndex;
    auto z4 = y.minIndex;
    auto z5 = y.maxIndex;
}
