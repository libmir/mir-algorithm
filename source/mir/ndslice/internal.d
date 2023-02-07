module mir.ndslice.internal;

import mir.internal.utility : isFloatingPoint, Iota;
import mir.math.common: optmath;
import mir.ndslice.iterator: IotaIterator;
import mir.ndslice.slice;
import mir.primitives;
import std.meta;
import std.traits;

@optmath:

template ConstIfPointer(T)
{
    static if (isPointer!T)
        alias ConstIfPointer = const(PointerTarget!T)*;
    else
        alias ConstIfPointer = T;
}

///
public import mir.utility: _expect;

struct RightOp(string op, T)
{
    T value;

    auto lightConst()() const @property
    {
        import mir.qualifier;
        return RightOp!(op, LightConstOf!T)(value.lightConst);
    }

    auto lightImmutable()() immutable @property
    {
        import mir.qualifier;
        return RightOp!(op, LightImmutableOf!T)(value.lightImmutable);
    }

    this()(ref T v) { value = v; }
    this()(T v) { value = v; }
    auto ref opCall(F)(auto ref F right)
    {
        static if (op == "^^" && isNumeric!T && isFloatingPoint!F)
        {
            import mir.math.common: pow;
            return pow(value, right);
        }
        else
        {
            return mixin("value " ~ op ~ " right");
        }
    }
}

struct LeftOp(string op, T)
{
    T value;

    auto lightConst()() const @property
    {
        import mir.qualifier;
        return LeftOp!(op, LightConstOf!T)(value.lightConst);
    }

    auto lightImmutable()() immutable @property
    {
        import mir.qualifier;
        return LeftOp!(op, LightImmutableOf!T)(value.lightImmutable);
    }

    this()(ref T v) { value = v; }
    this()(T v) { value = v; }
    auto ref opCall(F)(auto ref F left)
    {
        static if (op == "^^" && isFloatingPoint!T && isNumeric!F)
        {
            import mir.math.common: pow;
            return pow(left, value);
        }
        else
        {
            return mixin("left " ~ op ~ " value");
        }
    }
}

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

alias _IteratorOf(T : Slice!(Iterator, N, kind), Iterator, size_t N, SliceKind kind) = Iterator;

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

size_t sum()(size_t[] packs)
{
    size_t s;
    foreach(pack; packs)
        s += pack;
    return s;
}


size_t[] reverse()(size_t[] ar)
{
    foreach(i, e; ar[0..$/2])
    {
        ar[i] = ar[$ - i - 1];
        ar[$ - i - 1] = e;
    }
    return ar;
}

enum indexError(DeepElement, int pos, int N) =
    N.stringof ~ "D slice of " ~ DeepElement.stringof ~ ": bounds check failed at " ~ (pos + 1).stringof ~ " dimension";

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

mixin template DimensionsCountCTError()
{
    static assert(Dimensions.length <= N,
        "Dimensions list length = " ~ Dimensions.length.stringof
        ~ " should be less than or equal to N = " ~ N.stringof
        ~ tailErrorMessage!());
}

enum DimensionsCountRTError = q{
    assert(dimensions.length <= N,
        "Dimensions list length should be less than or equal to N = " ~ N.stringof
        ~ tailErrorMessage!());
};

mixin template DimensionCTError()
{
    static assert(dimension >= 0,
        "dimension = " ~ dimension.stringof ~ " at position "
        ~ i.stringof ~ " should be greater than or equal to 0"
        ~ tailErrorMessage!());
    static assert(dimension < N,
        "dimension = " ~ dimension.stringof ~ " at position "
        ~ i.stringof ~ " should be less than N = " ~ N.stringof
        ~ tailErrorMessage!());
    static assert(dimension < slice.S,
        "dimension = " ~ dimension.stringof ~ " at position "
        ~ i.stringof ~ " should be less than " ~ (slice.S).stringof ~ ". "
        ~ "`universal` and `canonical` from `mir.ndslice.topology` can be used to relax slice kind."
        ~ tailErrorMessage!());
}

enum DimensionRTError = q{
    static if (isSigned!(typeof(dimension)))
    assert(dimension >= 0, "dimension should be greater than or equal to 0"
        ~ tailErrorMessage!());
    assert(dimension < N, "dimension should be less than N = " ~ N.stringof
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

bool isPermutation(size_t N)(auto ref const scope size_t[N] perm)
{
    int[N] mask;
    return isValidPartialPermutationImpl(perm, mask);
}

version(mir_ndslice_test) unittest
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

template ShiftNegativeWith(size_t N)
{
    enum ShiftNegativeWith(sizediff_t i) = i < 0 ? i + N : i;
}

enum toSize_t(size_t i) = i;
enum toSizediff_t(sizediff_t i) = i;
enum isSize_t(alias i) = is(typeof(i) == size_t);
enum isSizediff_t(alias i) = is(typeof(i) == sizediff_t);
enum isIndex(I) = is(I : size_t);
template is_Slice(S)
{
    static if (is(S : Slice!(IotaIterator!I), I))
        enum is_Slice = __traits(isIntegral, I);
    else
        enum is_Slice = false;
}

alias Repeat(size_t N : 0, T...) = AliasSeq!();

private enum isReference(P) =
    hasIndirections!P
    || isFunctionPointer!P
    || is(P == interface);

alias ImplicitlyUnqual(T) = Select!(isImplicitlyConvertible!(T, Unqual!T), Unqual!T, T);
alias ImplicitlyUnqual(T : T*) = T*;

size_t lengthsProduct(size_t N)(auto ref const scope size_t[N] lengths)
{
    size_t length = lengths[0];
    foreach (i; Iota!(1, N))
            length *= lengths[i];
    return length;
}

pure nothrow version(mir_ndslice_test) unittest
{
    const size_t[3] lengths = [3, 4, 5];
    assert(lengthsProduct(lengths) == 60);
    assert(lengthsProduct([3, 4, 5]) == 60);
}

package(mir) template strideOf(args...)
{
    static if (args.length == 0)
        enum strideOf = args;
    else
    {
        @optmath @property auto ref ls()()
        {
            import mir.ndslice.topology: stride;
            return stride(args[0]);
        }
        alias strideOf = AliasSeq!(ls, strideOf!(args[1..$]));
    }
}

package(mir) template frontOf(size_t n)
{
    enum frontOf = () {
        string ret;
        static foreach (i; 0 .. n)
        {
            if (i)
                ret ~= `, `;
            ret ~= "slices[" ~ i.stringof ~ `].front`;
        }
        return ret;
    } ();
}

package(mir) template frontOf2(args...)
{
    static if (args.length == 0)
        enum frontOf2 = args;
    else
    {
        @optmath @property auto frontOf2Mod()()
        {
            return args[0].front;
        }
        alias frontOf2 = AliasSeq!(frontOf2Mod, frontOf2!(args[1..$]));
    }
}

package(mir) template backOf(args...)
{
    static if (args.length == 0)
        enum backOf = args;
    else
    {
        @optmath @property auto ref backOfMod()()
        {
            return args[0].back;
        }
        alias backOf = AliasSeq!(backOfMod, backOf!(args[1..$]));
    }
}

package(mir) template frontOfD(size_t dimension, args...)
{
    static if (args.length == 0)
        enum frontOfD = args;
    else
    {
        @optmath @property auto ref frontOfDMod()()
        {
            return args[0].front!dimension;
        }
        alias frontOfD = AliasSeq!(frontOfDMod, frontOfD!(dimension, args[1..$]));
    }
}

package(mir) template backOfD(size_t dimension, args...)
{
    static if (args.length == 0)
        enum backOfD = args;
    else
    {
        @optmath @property auto ref backOfDMod()()
        {
            return args[0].back!dimension;
        }
        alias backOfD = AliasSeq!(backOfDMod, backOfD!(dimension, args[1..$]));
    }
}

package(mir) template frontOfDim(size_t dim, args...)
{
    static if (args.length == 0)
        enum frontOfDim = args;
    else
    {
        alias arg = args[0];
        @optmath @property auto ref frontOfDimMod()
        {
            return arg.front!dim;
        }
        alias frontOfDim = AliasSeq!(frontOfDimMod, frontOfDim!(dim, args[1..$]));
    }
}

package(mir) template selectFrontOf(alias input, args...)
{
    static if (args.length == 0)
        enum selectFrontOf = args;
    else
    {
        alias arg = args[0];
        @optmath @property auto ref selectFrontOfMod()()
        {
            return arg.lightScope.selectFront!0(input);
        }
        alias selectFrontOf = AliasSeq!(selectFrontOfMod, selectFrontOf!(input, args[1..$]));
    }
}

package(mir) template selectBackOf(alias input, args...)
{
    static if (args.length == 0)
        enum selectBackOf = args;
    else
    {
        alias arg = args[0];
        @optmath @property auto ref selectBackOfMod()()
        {
            return arg.selectBack!0(input);
        }
        alias selectBackOf = AliasSeq!(selectBackOfMod, selectBackOf!(input, args[1..$]));
    }
}

package(mir) template frontSelectFrontOf(alias input, args...)
{
    static if (args.length == 0)
        enum frontSelectFrontOf = args;
    else
    {
        alias arg = args[0];
        @optmath @property auto ref frontSelectFrontOfMod()()
        {
            return arg.lightScope.front.selectFront!0(input);
        }
        alias frontSelectFrontOf = AliasSeq!(frontSelectFrontOfMod, frontSelectFrontOf!(input, args[1..$]));
    }
}

package(mir) template frontSelectBackOf(alias input, args...)
{
    static if (args.length == 0)
        enum frontSelectBackOf = args;
    else
    {
        alias arg = args[0];
        @optmath @property auto ref frontSelectBackOfMod
        ()()
        {
            return arg.lightScope.front.selectBack!0(input);
        }
        alias frontSelectBackOf = AliasSeq!(frontSelectBackOfMod
        , frontSelectBackOf!(input, args[1..$]));
    }
}
