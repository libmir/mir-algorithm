module mir.ndslice.internal;

import std.range.primitives;
import std.traits;
import std.meta;
import mir.ndslice.slice;
import mir.internal.utility;

@fastmath:

private template _prod(size_t len)
    if (len)
{
    static if (len == 1)
        enum _prod = "elems[0]";
    else
    {
        enum i = len - 1;
        enum _prod = ._prod!i ~ " * elems[" ~ i.stringof ~ "]";
    }
}

auto product(Elems...)(auto ref Elems elems)
{   
    return mixin(_prod!(Elems.length));
}


template _iotaArgs(size_t length, string prefix, string suffix)
{
    static if (length)
    {
        enum i = length - 1;
        enum _iotaArgs = _iotaArgs!(i, prefix, suffix) ~ prefix ~ i.stringof ~ suffix;
    }
    else
        enum _iotaArgs = "";
}

alias _IteratorOf(T : Slice!(kind, packs, Iterator), SliceKind kind, size_t[] packs, Iterator) = Iterator;

E maxElem(E)(E[] arr...)
{
    auto ret = Unqual!E.min;
    foreach(e; arr)
        if (e > ret)
            ret = e;
    return ret;
}

E minElem(E)(E[] arr...)
{
    auto ret = Unqual!E.max;
    foreach(e; arr)
        if (e < ret)
            ret = e;
    return ret;
}

T sum(T)(T[] packs)
{
    T s = 0;
    foreach(pack; packs)
        s += pack;
    return s;
}

size_t[] decDim()(size_t[] packs)
{
    packs[0]--;
    if (packs[0] == 0)
        packs = packs[1 .. $];
    return packs;
}

size_t[] reverse(size_t[] packs)
{
    foreach(i, e; packs[0..$/2])
    {
        packs[i] = packs[$ - i - 1];
        packs[$ - i - 1] = e;
    }
    return packs;
}


/+
fastmath do nothing here,
but remove constraint for LDC that operations for pointer's computations
maybe mixed up with callers computations if both computations has fastmath attribute.
So, it is just a bridge between two fastmath functions.
fmb alias is used to relax users.
+/
package alias fmb = fastmath;

version(LDC)
{
    static import ldc.attributes;
    alias fastmath = ldc.attributes.fastmath;
}
else
{
    alias fastmath = fastmathDummy;
}

enum FastmathDummy { init }
FastmathDummy fastmathDummy() { return FastmathDummy.init; }

template PtrTuple(Names...)
{
    @LikePtr struct PtrTuple(Ptrs...)
        if (allSatisfy!(isSlicePointer, Ptrs) && Ptrs.length == Names.length)
    {
        @fmb:

        Ptrs ptrs;

        void opOpAssign(string op)(sizediff_t shift)
            if (op == `+` || op == `-`)
        {
            foreach (ref ptr; ptrs)
                mixin (`ptr ` ~ op ~ `= shift;`);
        }

        auto opBinary(string op)(sizediff_t shift)
            if (op == `+` || op == `-`)
        {
            auto ret = this;
            ret.opOpAssign!op(shift);
            return ret;
        }

        public struct Index
        {
            Ptrs _ptrs__;
            mixin (PtrTupleFrontMembers!Names);
        }

        auto opIndex(sizediff_t index)
        {
            auto p = ptrs;
            foreach (ref ptr; p)
                ptr += index;
            return Index(p);
        }
    }
}

//// ISSUE 16501
//unittest
//{
//    import mir.ndslice;
//    alias sab = sliced!("a", "b");
//    auto sl = sab(new double[12], new double[12], 3, 4);
//    auto psl = sl.pack!1;
//}


struct PtrShell(Range)
{
    sizediff_t _shift;
    Range _range;
    @fmb:

    enum hasAccessByRef = isPointer!Range ||
        __traits(compiles, &_range[0]);

    void opOpAssign(string op)(sizediff_t shift)
        if (op == `+` || op == `-`)
    {
        mixin (`_shift ` ~ op ~ `= shift;`);
    }

    auto opBinary(string op)(sizediff_t shift)
        if (op == `+` || op == `-`)
    {
        mixin (`return typeof(this)(_shift ` ~ op ~ ` shift, _range);`);
    }

    auto opUnary(string op)()
        if (op == `++` || op == `--`)
    {
        mixin(op ~ `_shift;`);
        return this;
    }

    auto ref opIndex(sizediff_t index)
    in
    {
        assert(_shift + index >= 0);
        static if (hasLength!Range)
            assert(_shift + index <= _range.length);
    }
    body
    {
        return _range[_shift + index];
    }

    static if (!hasAccessByRef)
    {
        auto ref opIndexAssign(T)(T value, sizediff_t index)
        in
        {
            assert(_shift + index >= 0);
            static if (hasLength!Range)
                assert(_shift + index <= _range.length);
        }
        body
        {
            return _range[_shift + index] = value;
        }

        auto ref opIndexOpAssign(string op, T)(T value, sizediff_t index)
        in
        {
            assert(_shift + index >= 0);
            static if (hasLength!Range)
                assert(_shift + index <= _range.length);
        }
        body
        {
            mixin (`return _range[_shift + index] ` ~ op ~ `= value;`);
        }

        auto ref opIndexUnary(string op)(sizediff_t index)
        in
        {
            assert(_shift + index >= 0);
            static if (hasLength!Range)
                assert(_shift + index <= _range.length);
        }
        body
        {
            mixin (`return ` ~ op ~ `_range[_shift + index];`);
        }
    }

    auto save() @property
    {
        return this;
    }
}

auto ptrShell(Range)(Range range, sizediff_t shift = 0)
{
    return PtrShell!Range(shift, range);
}

@safe pure nothrow unittest
{
    import std.internal.test.dummyrange;
    foreach (RB; AliasSeq!(ReturnBy.Reference, ReturnBy.Value))
    {
        DummyRange!(RB, Length.Yes, RangeType.Random) range;
        range.reinit;
        assert(range.length >= 10);
        auto ptr = range.ptrShell;
        assert(ptr[0] == range[0]);
        auto save0 = range[0];
        ptr[0] += 10;
        ++ptr[0];
        assert(ptr[0] == save0 + 11);
        (ptr + 5)[2] = 333;
        assert(range[7] == 333);

        auto ptrCopy = ptr.save;
        ptrCopy._range.popFront;
        ptr[1] = 2;
        assert(ptr[0] == save0 + 11);
        assert(ptrCopy[0] == 2);
    }
}

//unittest
//{
//    import mir.ndslice.slice : PtrTuple;
//    import mir.ndslice.selection : Map;
//    static assert(isMemory!(int*));
//    alias R = PtrTuple!("a", "b");
//    alias F = R!(double*, double*);
//    static assert(isMemory!F);
//    static assert(isMemory!(Map!(F, a => a)));
//}

enum indexError(size_t pos, size_t N) =
    "index at position " ~ pos.stringof
    ~ " from the range [0 .." ~ N.stringof ~ ")"
    ~ " must be less than corresponding length.";

enum string tailErrorMessage(
    string fun = __FUNCTION__,
    string pfun = __PRETTY_FUNCTION__) =
"
- - -
Error in function
" ~ fun ~ "
- - -
Function prototype
" ~ pfun ~ "
_____";

mixin template _DefineRet()
{
    alias Ret = typeof(return);
    mixin _DefineRet_;
}

mixin template _DefineRet_()
{
    static if (hasElaborateAssign!(typeof(Ret._iterator)))
        Ret ret;
    else
        Ret ret = void;
}


mixin template DimensionsCountCTError()
{
    static assert(Dimensions.length <= packs[0],
        "Dimensions list length = " ~ Dimensions.length.stringof
        ~ " should be less than or equal to packs[0] = " ~ packs[0].stringof
        ~ tailErrorMessage!());
}

enum DimensionsCountRTError = q{
    assert(dimensions.length <= packs[0],
        "Dimensions list length should be less than or equal to packs[0] = " ~ packs[0].stringof
        ~ tailErrorMessage!());
};

mixin template DimensionCTError()
{
    static assert(dimension >= 0,
        "dimension = " ~ dimension.stringof ~ " at position "
        ~ i.stringof ~ " should be greater than or equal to 0"
        ~ tailErrorMessage!());
    static assert(dimension < packs[0],
        "dimension = " ~ dimension.stringof ~ " at position "
        ~ i.stringof ~ " should be less than packs[0] = " ~ packs[0].stringof
        ~ tailErrorMessage!());
    static assert(dimension < slice.S,
        "dimension = " ~ dimension.stringof ~ " at position "
        ~ i.stringof ~ " should be less than " ~ slice.S.stringof ~ ". "
        ~ "`universal` and `canonical` from `mir.ndslice.topology` can be used to relax slice kind."
        ~ tailErrorMessage!());
}

enum DimensionRTError = q{
    static if (isSigned!(typeof(dimension)))
    assert(dimension >= 0, "dimension should be greater than or equal to 0"
        ~ tailErrorMessage!());
    assert(dimension < packs[0], "dimension should be less than packs[0] = " ~ packs[0].stringof
        ~ tailErrorMessage!());
    assert(dimension < slice.S,
        "dimension should be less than " ~ slice.S.stringof ~ ". "
        ~ "`universal` and `canonical` from `mir.ndslice.topology` can be used to relax slice kind."
        ~ tailErrorMessage!());
};

private alias IncFront(Seq...) = AliasSeq!(Seq[0] + 1, Seq[1 .. $]);

private alias DecFront(Seq...) = AliasSeq!(Seq[0] - 1, Seq[1 .. $]);

private enum bool isNotZero(alias t) = t != 0;

alias NSeqEvert(Seq...) = Filter!(isNotZero, DecFront!(Reverse!(IncFront!Seq)));

//alias Parts(Seq...) = DecAll!(IncFront!Seq);

alias Snowball(Seq...) = AliasSeq!(size_t.init, SnowballImpl!(size_t.init, Seq));

private template SnowballImpl(size_t val, Seq...)
{
    static if (Seq.length == 0)
        alias SnowballImpl = AliasSeq!();
    else
        alias SnowballImpl = AliasSeq!(Seq[0] + val, SnowballImpl!(Seq[0] +  val, Seq[1 .. $]));
}

private template DecAll(Seq...)
{
    static if (Seq.length == 0)
        alias DecAll = AliasSeq!();
    else
        alias DecAll = AliasSeq!(Seq[0] - 1, DecAll!(Seq[1 .. $]));
}

//template SliceFromSeq(Range, Seq...)
//{
//    static if (Seq.length == 0)
//        alias SliceFromSeq = Range;
//    else
//    {
//        import mir.ndslice.slice : Slice;
//        alias SliceFromSeq = SliceFromSeq!(Slice!(Seq[$ - 1], Range), Seq[0 .. $ - 1]);
//    }
//}

template DynamicArrayDimensionsCount(T)
{
    static if (isDynamicArray!T)
        enum size_t DynamicArrayDimensionsCount = 1 + DynamicArrayDimensionsCount!(typeof(T.init[0]));
    else
        enum size_t DynamicArrayDimensionsCount = 0;
}

bool isPermutation(size_t N)(auto ref in size_t[N] perm)
{
    int[N] mask;
    return isValidPartialPermutationImpl(perm, mask);
}

unittest
{
    assert(isPermutation([0, 1]));
    // all numbers 0..N-1 need to be part of the permutation
    assert(!isPermutation([1, 2]));
    assert(!isPermutation([0, 2]));
    // duplicates are not allowed
    assert(!isPermutation([0, 1, 1]));

    size_t[0] emptyArr;
    // empty permutations are not allowed either
    assert(!isPermutation(emptyArr));
}

bool isValidPartialPermutation(size_t N)(in size_t[] perm)
{
    int[N] mask;
    return isValidPartialPermutationImpl(perm, mask);
}

private bool isValidPartialPermutationImpl(size_t N)(in size_t[] perm, ref int[N] mask)
{
    if (perm.length == 0)
        return false;
    foreach (j; perm)
    {
        if (j >= N)
            return false;
        if (mask[j]) //duplicate
            return false;
        mask[j] = true;
    }
    return true;
}

enum toSize_t(size_t i) = i;
enum isSize_t(alias i) = is(typeof(i) == size_t);
enum isIndex(I) = is(I : size_t);
enum is_Slice(S) = is(S : _Slice);

alias Repeat(size_t N : 0, T...) = AliasSeq!();

private enum isReference(P) =
    hasIndirections!P
    || isFunctionPointer!P
    || is(P == interface);

enum hasReference(T) = anySatisfy!(isReference, RepresentationTypeTuple!T);

alias ImplicitlyUnqual(T) = Select!(isImplicitlyConvertible!(T, Unqual!T), Unqual!T, T);

size_t lengthsProduct(size_t N)(auto ref in size_t[N] lengths)
{
    size_t length = lengths[0];
    foreach (i; Iota!(1, N))
            length *= lengths[i];
    return length;
}

pure nothrow unittest
{
    const size_t[3] lengths = [3, 4, 5];
    assert(lengthsProduct(lengths) == 60);
    assert(lengthsProduct([3, 4, 5]) == 60);
}

struct _Slice { size_t i, j; }
