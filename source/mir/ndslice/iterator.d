/++
This is a submodule of $(MREF mir,ndslice).

Iterator is a type with a pointer like behavior.
An ndslice can be created on top of an iterator using $(SUBREF slice, sliced).

$(BOOKTABLE $(H2 Iterators),
$(TR $(TH Iterator Name) $(TH Used By))
$(T2 BytegroupIterator, $(SUBREF topology, bytegroup).)
$(T2 CachedIterator, $(SUBREF topology, cached), $(SUBREF topology, cachedGC).)
$(T2 ChopIterator, $(SUBREF topology, chopped))
$(T2 FieldIterator, $(SUBREF slice, slicedField), $(SUBREF topology, bitwise), $(SUBREF topology, ndiota), and others.)
$(T2 FlattenedIterator, $(SUBREF topology, flattened))
$(T2 IndexIterator, $(SUBREF topology, indexed))
$(T2 IotaIterator, $(SUBREF topology, iota))
$(T2 MapIterator, $(SUBREF topology, map))
$(T2 MemberIterator, $(SUBREF topology, member))
$(T2 NeighboursIterator, $(SUBREF topology, withNeighboursSum))
$(T2 RetroIterator, $(SUBREF topology, retro))
$(T2 SliceIterator, $(SUBREF topology, map) in composition with $(LREF MapIterator) for packed slices.)
$(T2 SlideIterator, $(SUBREF topology, diff), $(SUBREF topology, pairwise), and $(SUBREF topology, slide).)
$(T2 StairsIterator, $(SUBREF topology, stairs))
$(T2 StrideIterator, $(SUBREF topology, stride))
$(T2 SubSliceIterator, $(SUBREF topology, subSlices))
$(T2 TripletIterator, $(SUBREF topology, triplets))
$(T2 ZipIterator, $(SUBREF topology, zip))
)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.iterator;

import mir.internal.utility: Iota;
import mir.math.common: optmath;
import mir.ndslice.field;
import mir.ndslice.internal;
import mir.ndslice.slice: SliceKind, Slice, Universal, Canonical, Contiguous, isSlice;
import mir.qualifier;
import mir.conv;
import std.traits;

private static immutable assumeZeroShiftExceptionMsg = "*.assumeFieldsHaveZeroShift: shift is not zero!";
version(D_Exceptions)
    private static immutable assumeZeroShiftException = new Exception(assumeZeroShiftExceptionMsg);

@optmath:

enum std_ops = q{
    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    { mixin(op ~ "_iterator;"); }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index;"); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return this._iterator - right._iterator; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
};

/++
Step counter.

`IotaIterator` is used by $(SUBREF topology, iota).
+/
struct IotaIterator(I)
    if (isIntegral!I || isPointer!I)
{
@optmath:

    ///
    I _index;

    static if (isPointer!I)
    ///
    auto lightConst()() const @property
    {
        static if (isIntegral!I)
            return IotaIterator!I(_index);
        else
            return IotaIterator!(LightConstOf!I)(_index);
    }

    static if (isPointer!I)
    ///
    auto lightImmutable()() immutable @property
    {
        static if (isIntegral!I)
            return IotaIterator!I(_index);
        else
            return IotaIterator!(LightImmutableOf!I)(_index);
    }

pure:

    I opUnary(string op : "*")()
    { return _index; }

    void opUnary(string op)()
        if (op == "--" || op == "++")
    { mixin(op ~ `_index;`); }

    I opIndex()(ptrdiff_t index) const
    { return cast(I)(_index + index); }

    void opOpAssign(string op)(ptrdiff_t index)
        if (op == `+` || op == `-`)
    { mixin(`_index ` ~ op ~ `= index;`); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(const typeof(this) right) const
    { return cast(ptrdiff_t)(this._index - right._index); }

    bool opEquals()(const typeof(this) right) const
    { return this._index == right._index; }

    auto opCmp()(const typeof(this) right) const
    { return this._index - right._index; }
}

///
@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    IotaIterator!int iota;
    assert(*iota == 0);

    // iteration
    ++iota;
    assert(*iota == 1);
    
    assert(iota[2] == 3);
    assert(iota[-1] == 0);

    --iota;
    assert(*iota == 0);

    // opBinary
    assert(*(iota + 2) == 2);
    assert(*(iota - 3) == -3);
    assert((iota - 3) - iota == -3);

    // construction
    assert(*IotaIterator!int(3) == 3);
    assert(iota - 1 < iota);
}

///
pure nothrow @nogc version(mir_ndslice_test) unittest
{
    int[32] data;
    auto iota = IotaIterator!(int*)(data.ptr);
    assert(*iota == data.ptr);

    // iteration
    ++iota;
    assert(*iota == 1 + data.ptr);
    
    assert(iota[2] == 3 + data.ptr);
    assert(iota[-1] == 0 + data.ptr);

    --iota;
    assert(*iota == 0 + data.ptr);

    // opBinary
    assert(*(iota + 2) == 2 + data.ptr);
    assert(*(iota - 3) == -3 + data.ptr);
    assert((iota - 3) - iota == -3);

    // construction
    assert(*IotaIterator!(int*)(data.ptr) == data.ptr);
    assert(iota - 1 < iota);
}

auto RetroIterator__map(Iterator, alias fun)(ref RetroIterator!Iterator it)
{
    auto iterator = it._iterator._mapIterator!fun;
    return RetroIterator!(typeof(iterator))(iterator);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = iota(9).retro.map!(a => a).slice;
    uint r;
    auto w = iota(9).retro.map!(a => a).map!(a => a * r).slice;
}

/++
Reverse directions for an iterator.

`RetroIterator` is used by $(SUBREF topology, retro).
+/
struct RetroIterator(Iterator)
{
@optmath:
    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return RetroIterator!(LightConstOf!Iterator)(.lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return RetroIterator!(LightImmutableOf!Iterator)(.lightImmutable(_iterator));
    }

    ///
    static alias __map(alias fun) = RetroIterator__map!(Iterator, fun);

    auto ref opUnary(string op : "*")()
    { return *_iterator; }

    void opUnary(string op : "--")()
    { ++_iterator; }

    void opUnary(string op : "++")() pure
    { --_iterator; }

    auto ref opIndex()(ptrdiff_t index)
    { return _iterator[-index]; }

    void opOpAssign(string op : "-")(ptrdiff_t index) scope
    { _iterator += index; }

    void opOpAssign(string op : "+")(ptrdiff_t index) scope
    { _iterator -= index; }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return right._iterator - this._iterator; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return right._iterator == this._iterator; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!Iterator)
            return right._iterator - this._iterator;
        else
            return right._iterator.opCmp(this._iterator);
    }
}

///
@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    IotaIterator!int iota;
    RetroIterator!(IotaIterator!int) retro;

    ++iota;
    --retro;
    assert(*retro == *iota);

    --iota;
    ++retro;
    assert(*retro == *iota);

    assert(retro[-7] == iota[7]);

    iota += 100;
    retro -= 100;
    assert(*retro == *iota);

    iota -= 100;
    retro += 100;
    assert(*retro == *iota);

    assert(*(retro + 10) == *(iota - 10));

    assert(retro - 1 < retro);

    assert((retro - 5) - retro == -5);

    iota = IotaIterator!int(3);
    retro = RetroIterator!(IotaIterator!int)(iota);
    assert(*retro == *iota);
}

auto StrideIterator__map(Iterator, alias fun)(StrideIterator!Iterator it)
{
    auto iterator = it._iterator._mapIterator!fun;
    return StrideIterator!(typeof(iterator))(it._stride, iterator);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = iota([3], 0, 3).map!(a => a).slice;
    uint r;
    auto w = iota([3], 0, 3).map!(a => a).map!(a => a * r).slice;
}

/++
Iterates an iterator with a fixed strides.

`StrideIterator` is used by $(SUBREF topology, stride).
+/
struct StrideIterator(Iterator)
{
@optmath:
    ///
    ptrdiff_t _stride;
    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return StrideIterator!(LightConstOf!Iterator)(_stride, .lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return StrideIterator!(LightImmutableOf!Iterator)(_stride, .lightImmutable(_iterator));
    }

    ///
    static alias __map(alias fun) = StrideIterator__map!(Iterator, fun);

    auto ref opUnary(string op : "*")()
    { return *_iterator; }

    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    { mixin("_iterator " ~ op[0] ~ "= _stride;"); }

    auto ref opIndex()(ptrdiff_t index)
    { return _iterator[index * _stride]; }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index * _stride;"); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return (this._iterator - right._iterator) / _stride; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!Iterator)
            ptrdiff_t ret = this._iterator - right._iterator;
        else
            ptrdiff_t ret = this._iterator.opCmp(right._iterator);
        return _stride >= 0 ? ret : -ret;
    }
}

///
@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    IotaIterator!int iota;
    StrideIterator!(IotaIterator!int) stride;
    stride._stride = -3;

    iota -= stride._stride;
    --stride;
    assert(*stride == *iota);

    iota += stride._stride;
    ++stride;
    assert(*stride == *iota);

    assert(stride[7] == iota[7 * stride._stride]);

    iota -= 100 * stride._stride;
    stride -= 100;
    assert(*stride == *iota);

    iota += 100 * stride._stride;
    stride += 100;
    assert(*stride == *iota);

    assert(*(stride + 10) == *(iota + 10 * stride._stride));

    assert(stride - 1 < stride);

    assert((stride - 5) - stride == -5);

    iota = IotaIterator!int(3);
    stride = StrideIterator!(IotaIterator!int)(3, iota);
    assert(*stride == *iota);
}

auto StrideIterator__map(Iterator, size_t factor, alias fun)(StrideIterator!(Iterator, factor) it)
{
    auto iterator = it._iterator._mapIterator!fun;
    return StrideIterator!(typeof(iterator), factor)(iterator);
}

/++
Iterates an iterator with a fixed strides.

`StrideIterator` is used by $(SUBREF topology, stride).
+/
struct StrideIterator(Iterator, ptrdiff_t factor)
{
@optmath:
    ///
    enum _stride = factor;

    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return StrideIterator!(LightConstOf!Iterator, _stride)(.lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return StrideIterator!(LightImmutableOf!Iterator, _stride)(.lightImmutable(_iterator));
    }

    ///
    static alias __map(alias fun) = StrideIterator__map!(Iterator, _stride, fun);

    auto ref opUnary(string op : "*")()
    { return *_iterator; }

    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    { mixin("_iterator " ~ op[0] ~ "= _stride;"); }

    auto ref opIndex()(ptrdiff_t index)
    { return _iterator[index * _stride]; }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index * _stride;"); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return (this._iterator - right._iterator) / _stride; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!Iterator)
            ptrdiff_t ret = this._iterator - right._iterator;
        else
            ptrdiff_t ret = this._iterator.opCmp(right._iterator);
        return _stride >= 0 ? ret : -ret;
    }
}

///
@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    IotaIterator!int iota;
    StrideIterator!(IotaIterator!int, -3) stride;

    iota -= stride._stride;
    --stride;
    assert(*stride == *iota);

    iota += stride._stride;
    ++stride;
    assert(*stride == *iota);

    assert(stride[7] == iota[7 * stride._stride]);

    iota -= 100 * stride._stride;
    stride -= 100;
    assert(*stride == *iota);

    iota += 100 * stride._stride;
    stride += 100;
    assert(*stride == *iota);

    assert(*(stride + 10) == *(iota + 10 * stride._stride));

    assert(stride - 1 < stride);

    assert((stride - 5) - stride == -5);
}

package template _zip_types(Iterators...)
{
    alias AliasSeq(T...) = T;
    static if (Iterators.length)
    {
        enum i = Iterators.length - 1;
        alias T = typeof(Iterators[i].init[sizediff_t.init]);
        static if (__traits(compiles, &Iterators[i].init[sizediff_t.init]))
        {
            import mir.functional: Ref;
            alias _zip_types = AliasSeq!(_zip_types!(Iterators[0 .. i]), Ref!T);
        }
        else
            alias _zip_types = AliasSeq!(_zip_types!(Iterators[0 .. i]), T);
    }
    else
        alias _zip_types = AliasSeq!();
}

package template _zip_fronts(Iterators...)
{
    static if (Iterators.length)
    {
        enum i = Iterators.length - 1;
        static if (__traits(compiles, &Iterators[i].init[sizediff_t.init]))
            enum _zip_fronts = _zip_fronts!(Iterators[0 .. i]) ~ "_ref(*_iterators[" ~ i.stringof ~ "]), ";
        else
            enum _zip_fronts = _zip_fronts!(Iterators[0 .. i]) ~ "*_iterators[" ~ i.stringof ~ "], ";
    }
    else
        enum _zip_fronts = "";
}

package template _zip_index(Iterators...)
{
    static if (Iterators.length)
    {
        enum i = Iterators.length - 1;
        static if (__traits(compiles, &Iterators[i].init[sizediff_t.init]))
            enum _zip_index = _zip_index!(Iterators[0 .. i]) ~ "_ref(_iterators[" ~ i.stringof ~ "][index]), ";
        else
            enum _zip_index = _zip_index!(Iterators[0 .. i]) ~ "_iterators[" ~ i.stringof ~ "][index], ";
    }
    else
        enum _zip_index = "";
}

/++
Iterates multiple iterators in lockstep.

`ZipIterator` is used by $(SUBREF topology, zip).
+/
struct ZipIterator(Iterators...)
    if (Iterators.length > 1)
{
@optmath:
    import std.traits: ConstOf, ImmutableOf;
    import std.meta: staticMap;
    import mir.functional: RefTuple, Ref, _ref;
    ///
    Iterators _iterators;

    ///
    auto lightConst()() const @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        import std.meta: staticMap;
        alias Ret = ZipIterator!(staticMap!(LightConstOf, Iterators));
        enum ret = "Ret(%(.lightConst(_iterators[%s]),%)]))".format(_iterators.length.iota);
        return mixin(ret);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        import std.meta: staticMap;
        alias Ret = ZipIterator!(staticMap!(LightImmutableOf, Iterators));
        enum ret = "Ret(%(.lightImmutable(_iterators[%s]),%)]))".format(_iterators.length.iota);
        return mixin(ret);
    }

    auto opUnary(string op : "*")()
    { return mixin("RefTuple!(_zip_types!Iterators)(" ~ _zip_fronts!Iterators ~ ")"); }


    auto opUnary(string op : "*")() const
    { return mixin("RefTuple!(_zip_types!Iterators)(" ~ _zip_fronts!Iterators ~ ")"); }

    auto opUnary(string op : "*")() immutable
    { return mixin("RefTuple!(_zip_types!Iterators)(" ~ _zip_fronts!Iterators ~ ")"); }

    void opUnary(string op)() scope
        if (op == "++" || op == "--")
    {
        foreach (ref _iterator; _iterators)
            mixin(op ~ `_iterator;`);
    }

    auto opIndex()(ptrdiff_t index)
    { return mixin("RefTuple!(_zip_types!Iterators)(" ~ _zip_index!Iterators ~ ")"); }

    auto opIndexAssign(Types...)(RefTuple!(Types) value, ptrdiff_t index)
        if (Types.length == Iterators.length)
    {
        foreach(i, ref val; value.expand)
        {
            import mir.functional: unref;
            _iterators[i][index] = unref(val);
        }
        return opIndex(index);
    }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "+" || op == "-")
    {
        foreach (ref _iterator; _iterators)
            mixin(`_iterator ` ~ op ~ `= index;`);
    }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return this._iterators[0] - right._iterators[0]; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterators[0] == right._iterators[0]; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!(Iterators[0]))
            return this._iterators[0] - right._iterators[0];
        else
            return this._iterators[0].opCmp(right._iterators[0]);
    }

    import std.meta: anySatisfy;
    static if (anySatisfy!(hasZeroShiftFieldMember, Iterators))
    /// Defined if at least one of `Iterators` has member `assumeFieldsHaveZeroShift`.
    auto assumeFieldsHaveZeroShift() @property
    {
        import std.meta: staticMap;
        alias _fields = _iterators;
        return mixin("ZipField!(staticMap!(ZeroShiftField, Iterators))(" ~ applyAssumeZeroShift!Iterators ~ ")");
    }
}

///
pure nothrow @nogc version(mir_ndslice_test) unittest
{
    import mir.ndslice.traits: isIterator;

    double[10] data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    alias ItA = IotaIterator!int;
    alias ItB = double*;
    alias ItZ = ZipIterator!(ItA, ItB);
    auto zip = ItZ(ItA(3), data.ptr);
    assert((*zip).a == 3);
    assert((*zip).b == 1);

    // iteration
    ++zip;
    assert((*zip).a == 3 + 1);
    assert((*zip).b == 1 + 1);
    assert(&(*zip).b() == data.ptr + 1);
    
    assert(zip[4].a == 3 + 5);
    assert(zip[4].b == 1 + 5);
    assert(&zip[4].b() == data.ptr + 5);

    --zip;
    assert((*zip).a == 3);
    assert((*zip).b == 1);

    assert((*(zip + 2)).a == 3 + 2);
    assert((*(zip - 3)).a == 3 + -3);
    assert((*(zip + 2)).b == 1 + 2);
    assert((*(zip + 3 - 3)).b == 1);
    assert((zip - 3).opBinary!"-"(zip) == -3);

    assert(zip == zip);
    assert(zip - 1 < zip);

    static assert(isIterator!(ZipIterator!(double*, int*)));
    static assert(isIterator!(ZipIterator!(immutable(double)*, immutable(int)*)));
}

///
struct CachedIterator(Iterator, CacheIterator, FlagIterator)
{
    ///
    Iterator _iterator;
    ///
    CacheIterator _caches;
    ///
    FlagIterator _flags;

@optmath:

    ///
    auto lightScope()() scope @property
    {
        return CachedIterator!(LightScopeOf!Iterator, LightScopeOf!CacheIterator, LightScopeOf!FlagIterator)(
            .lightScope(_iterator),
            .lightScope(_caches),
            .lightScope(_flags),
            );
    }

    ///
    auto lightScope()() scope const @property
    {
        return lightConst.lightScope;
    }

    ///
    auto lightScope()() scope immutable @property
    {
        return lightImmutable.lightScope;
    }

    ///
    auto lightConst()() const @property
    {
        return CachedIterator!(LightConstOf!Iterator, CacheIterator, FlagIterator)(
            .lightConst(_iterator),
            *cast(CacheIterator*)&_caches,
            *cast(FlagIterator*)&_flags,
            );
    }

    ///
    auto lightImmutable()() immutable @property @trusted
    {
        return CachedIterator!(LightImmutableOf!Iterator, CacheIterator, FlagIterator)(
            .lightImmutable(_iterator),
            *cast(CacheIterator*)&_caches,
            *cast(FlagIterator*)&_flags,
            );
    }

    private alias T = typeof(Iterator.init[0]);
    private alias UT = Unqual!T;

    auto opUnary(string op : "*")()
    {
        if (_expect(!*_flags, false))
        {
            _flags[0] = true;
            emplaceRef!T(*cast(UT*)&*_caches, *_iterator);
        }
        return *_caches;
    }

    auto opIndex()(ptrdiff_t index)
    {
        if (_expect(!_flags[index], false))
        {
            _flags[index] = true;
            emplaceRef!T(*cast(UT*)&(_caches[index]), _iterator[index]);
        }
        return _caches[index];
    }

    auto ref opIndexAssign(T)(auto ref T val, ptrdiff_t index)
    {
        _flags[index] = true;
        return _caches[index] = val;
    }

    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    {
        mixin(op ~ "_iterator;");
        mixin(op ~ "_caches;");
        mixin(op ~ "_flags;");
    }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    {
        mixin("_iterator" ~ op ~ "= index;");
        mixin("_caches" ~ op ~ "= index;");
        mixin("_flags" ~ op ~ "= index;");
    }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return this._iterator - right._iterator; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
}

private enum map_primitives = q{

    import mir.functional: RefTuple, autoExpandAndForward;

    auto ref opUnary(string op : "*")()
    {
        static if (is(typeof(*_iterator) : RefTuple!T, T...))
        {
            auto t = *_iterator;
            return _fun(autoExpandAndForward!t);
        }
        else
            return _fun(*_iterator);
    }

    auto ref opIndex(ptrdiff_t index) scope
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = _iterator[index];
            return _fun(autoExpandAndForward!t);
        }
        else
            return _fun(_iterator[index]);
    }

    static if (!__traits(compiles, &opIndex(ptrdiff_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index) scope
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return _fun(autoExpandAndForward!t) = value;
            }
            else
                return _fun(_iterator[index]) = value;
        }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return _fun(autoExpandAndForward!t);
            }
            else
                return mixin(op ~ "_fun(_iterator[index])");
        }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("_fun(autoExpandAndForward!t)" ~ op ~ "= value");
            }
            else
                return mixin("_fun(_iterator[index])" ~ op ~ "= value");
        }
    }
};

/++
`VmapIterator` is used by $(SUBREF topology, map).
+/
struct VmapIterator(Iterator, Fun)
{
@optmath:

    ///
    Iterator _iterator;
    ///
    Fun _fun;

    ///
    auto lightConst()() const @property
    {
        return VmapIterator!(LightConstOf!Iterator, LightConstOf!Fun)(.lightConst(_iterator), .lightConst(_fun));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return VmapIterator!(LightImmutableOf!Iterator, LightImmutableOf!Fun)(.lightImmutable(_iterator), .lightImmutable(_fun));
    }

    import mir.functional: RefTuple, autoExpandAndForward;

    auto ref opUnary(string op : "*")()
    {
        static if (is(typeof(*_iterator) : RefTuple!T, T...))
        {
            auto t = *_iterator;
            return _fun(autoExpandAndForward!t);
        }
        else
            return _fun(*_iterator);
    }

    auto ref opIndex(ptrdiff_t index) scope
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = _iterator[index];
            return _fun(autoExpandAndForward!t);
        }
        else
            return _fun(_iterator[index]);
    }

    static if (!__traits(compiles, &opIndex(ptrdiff_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index) scope
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return _fun(autoExpandAndForward!t) = value;
            }
            else
                return _fun(_iterator[index]) = value;
        }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin(op ~ "_fun(autoExpandAndForward!t)");
            }
            else
                return mixin(op ~ "_fun(_iterator[index])");
        }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("_fun(autoExpandAndForward!t)" ~ op ~ "= value");
            }
            else
                return mixin("_fun(_iterator[index])" ~ op ~ "= value");
        }
    }
    
    mixin(std_ops);

    static if (hasZeroShiftFieldMember!Iterator)
    ///
    auto assumeFieldsHaveZeroShift() @property
    {
        return _vmapField(_iterator.assumeFieldsHaveZeroShift, _fun);
    }
}

auto MapIterator__map(Iterator, alias fun0, alias fun)(ref MapIterator!(Iterator, fun0) it)
{
    return MapIterator!(Iterator, fun)(it._iterator);
}

/++
`MapIterator` is used by $(SUBREF topology, map).
+/
struct MapIterator(Iterator, alias _fun)
{
@optmath:
    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return MapIterator!(LightConstOf!Iterator, _fun)(.lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return MapIterator!(LightImmutableOf!Iterator, _fun)(.lightImmutable(_iterator));
    }

    import mir.functional: pipe, autoExpandAndForward;
    ///
    static alias __map(alias fun1) = MapIterator__map!(Iterator, _fun, pipe!(_fun, fun1));

    import mir.functional: RefTuple, autoExpandAndForward;

    auto ref opUnary(string op : "*")()
    {
        static if (is(typeof(*_iterator) : RefTuple!T, T...))
        {
            auto t = *_iterator;
            return _fun(autoExpandAndForward!t);
        }
        else
            return _fun(*_iterator);
    }

    auto ref opIndex(ptrdiff_t index) scope
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = _iterator[index];
            return _fun(autoExpandAndForward!t);
        }
        else
            return _fun(_iterator[index]);
    }

    static if (!__traits(compiles, &opIndex(ptrdiff_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index) scope
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return _fun(autoExpandAndForward!t) = value;
            }
            else
                return _fun(_iterator[index]) = value;
        }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin(op ~ "_fun(autoExpandAndForward!t)");
            }
            else
                return mixin(op ~ "_fun(_iterator[index])");
        }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("_fun(autoExpandAndForward!t)" ~ op ~ "= value");
            }
            else
                return mixin("_fun(_iterator[index])" ~ op ~ "= value");
        }
    }
    
    mixin(std_ops);

    static if (hasZeroShiftFieldMember!Iterator)
    ///
    auto assumeFieldsHaveZeroShift() @property
    {
        return _mapField!_fun(_iterator.assumeFieldsHaveZeroShift);
    }
}

/+
Creates a mapped iterator. Uses `__map` if possible.
+/
auto _mapIterator(alias fun, Iterator)(Iterator iterator)
{
    import core.lifetime: move;
    static if (__traits(hasMember, Iterator, "__map"))
    {
        static if (is(Iterator : MapIterator!(Iter0, fun0), Iter0, alias fun0)
                && !__traits(compiles, Iterator.__map!fun(iterator)))
        {
            // https://github.com/libmir/mir-algorithm/issues/111
            debug(mir) pragma(msg, __FUNCTION__~" not coalescing chained map calls into a single lambda, possibly because of multiple embedded context pointers");
            return MapIterator!(Iterator, fun)(move(iterator));
        }
        else
            return Iterator.__map!fun(iterator);
    }
    else
       return MapIterator!(Iterator, fun)(move(iterator));
}


/+
Creates a mapped iterator. Uses `__vmap` if possible.
+/
auto _vmapIterator(Iterator, Fun)(Iterator iterator, Fun fun)
{
    static if (__traits(hasMember, Iterator, "__vmap"))
        return Iterator.__vmap(iterator, fun);
    else
       return MapIterator!(Iterator, fun)(iterator);
}

@safe pure nothrow @nogc version(mir_ndslice_test) unittest
{
    // https://github.com/libmir/mir-algorithm/issues/111
    import mir.ndslice.topology : iota, map;
    import mir.functional : pipe;

    static auto foo(T)(T x)
    {
        return x.map!(a => a + 1);
    }

    static auto bar(T)(T x)
    {
        return foo(x).map!(a => a + 2);
    }

    auto data = iota(5);
    auto result = iota([5], 3);

    auto x = data.map!(a => a + 1).map!(a => a + 2);
    assert(x == result);

    auto y = bar(data);
    assert(y == result);
}

/++
`NeighboursIterator` is used by $(SUBREF topology, map).
+/
struct NeighboursIterator(Iterator, size_t N, alias _fun, bool around)
{
    import std.meta: AliasSeq;
@optmath:
    ///
    Iterator _iterator;
    static if (N)
        Iterator[2][N] _neighbours;
    else alias _neighbours = AliasSeq!();

    ///
    auto lightConst()() const @property
    {
        LightConstOf!Iterator[2][N] neighbours;
        foreach (i; 0 .. N)
        {
            neighbours[i][0] = .lightConst(_neighbours[i][0]);
            neighbours[i][1] = .lightConst(_neighbours[i][1]);
        }
        return NeighboursIterator!(LightConstOf!Iterator, N, _fun, around)(.lightConst(_iterator), neighbours);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        LightImmutableOf!Iterator[2][N] neighbours;
        foreach (i; 0 .. N)
        {
            neighbours[i][0] = .lightImmutable(_neighbours[i][0]);
            neighbours[i][1] = .lightImmutable(_neighbours[i][1]);
        }
        return NeighboursIterator!(LightImmutableOf!Iterator, N, _fun, around)(.lightImmutable(_iterator), neighbours);
    }

    import mir.functional: RefTuple, _ref;

    private alias RA = Unqual!(typeof(_fun(_iterator[-1], _iterator[+1])));
    private alias Result = RefTuple!(_zip_types!Iterator, RA);

    auto ref opUnary(string op : "*")()
    {
        return opIndex(0);
    }

    auto ref opIndex(ptrdiff_t index) scope
    {
        static if (around)
            RA result = _fun(_iterator[index - 1], _iterator[index + 1]);

        foreach (i; Iota!N)
        {
            static if (i == 0 && !around)
                RA result = _fun(_neighbours[i][0][index], _neighbours[i][1][index]);
            else
                result = _fun(result, _fun(_neighbours[i][0][index], _neighbours[i][1][index]));
        }
        static if (__traits(compiles, &_iterator[index]))
            return Result(_ref(_iterator[index]), result);
        else
            return Result(_iterator[index], result);
    }
    
    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    {
        mixin(op ~ "_iterator;");
        foreach (i; Iota!N)
        {
            mixin(op ~ "_neighbours[i][0];");
            mixin(op ~ "_neighbours[i][1];");
        }
    }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    {

        mixin("_iterator " ~ op ~ "= index;");
        foreach (i; Iota!N)
        {
            mixin("_neighbours[i][0] " ~ op ~ "= index;");
            mixin("_neighbours[i][1] " ~ op ~ "= index;");
        }
    }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return this._iterator - right._iterator; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
}

/++
`MemberIterator` is used by $(SUBREF topology, member).
+/
struct MemberIterator(Iterator, string member)
{
@optmath:
    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return MemberIterator!(LightConstOf!Iterator, member)(.lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return MemberIterator!(LightImmutableOf!Iterator, member)(.lightImmutable(_iterator));
    }

    auto ref opUnary(string op : "*")()
    {
        return __traits(getMember, *_iterator, member);
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        return __traits(getMember, _iterator[index], member);
    }

    static if (!__traits(compiles, &opIndex(ptrdiff_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index) scope
        {
            return __traits(getMember, _iterator[index], member) = value;
        }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        {
            return mixin(op ~ "__traits(getMember, _iterator[index], member)");
        }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        {
            return mixin("__traits(getMember, _iterator[index], member)" ~ op ~ "= value");
        }
    }

    mixin(std_ops);
}

/++
`BytegroupIterator` is used by $(SUBREF topology, Bytegroup) and $(SUBREF topology, bytegroup).
+/
struct BytegroupIterator(Iterator, size_t count, DestinationType)
    if (count)
{
@optmath:
    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return BytegroupIterator!(LightConstOf!Iterator, count, DestinationType)(.lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return BytegroupIterator!(LightImmutableOf!Iterator, count, DestinationType)(.lightImmutable(_iterator));
    }

    package(mir) alias Byte = Unqual!(typeof(_iterator[0]));

    version(LittleEndian)
        private enum BE = false;
    else
        private enum BE = true;

    private union U
    {
        DestinationType value;
        static if (DestinationType.sizeof > Byte[count].sizeof && BE && isScalarType!DestinationType)
        {
            struct
            {
                ubyte[DestinationType.sizeof - Byte[count].sizeof] shiftPayload;
                Byte[count] bytes;
            }
        }
        else
        {
            Byte[count] bytes;
        }
    }

    DestinationType opUnary(string op : "*")()
    {
        U ret = { value: DestinationType.init };
        foreach (i; Iota!count)
            ret.bytes[i] = _iterator[i];
        return ret.value;
    }

    DestinationType opIndex()(ptrdiff_t index)
    {
        return *(this + index);
    }

    DestinationType opIndexAssign(T)(T val, ptrdiff_t index) scope
    {
        auto it = this + index;
        U ret = { value: val };
        foreach (i; Iota!count)
            it._iterator[i] = ret.bytes[i];
        return ret.value;
    }

    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    { mixin("_iterator " ~ op[0] ~ "= count;"); }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    { mixin("_iterator " ~ op ~ "= index * count;"); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return (this._iterator - right._iterator) / count; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._iterator == right._iterator; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        static if (isPointer!Iterator)
            return this._iterator - right._iterator;
        else
            return this._iterator.opCmp(right._iterator);
    }
}

auto SlideIterator__map(Iterator, size_t params, alias fun0, alias fun)(SlideIterator!(Iterator, params, fun0) it)
{
    return SlideIterator!(Iterator, params, fun)(it._iterator);
}

/++
`SlideIterator` is used by $(SUBREF topology, diff) and $(SUBREF topology, slide).
+/
struct SlideIterator(Iterator, size_t params, alias fun)
    if (params > 1)
{
@optmath:
    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return SlideIterator!(LightConstOf!Iterator, params, fun)(.lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return SlideIterator!(LightImmutableOf!Iterator, params, fun)(.lightImmutable(_iterator));
    }

    import mir.functional: pipe;
    ///
    static alias __map(alias fun1) = SlideIterator__map!(Iterator, params, fun, pipe!(fun, fun1));

    auto ref opUnary(string op : "*")()
    {
        return mixin("fun(" ~ _iotaArgs!(params, "_iterator[", "], ") ~ ")");
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        return mixin("fun(" ~ _iotaArgs!(params, "_iterator[index + ", "], ") ~ ")");
    }

    mixin(std_ops);
}

///
version(mir_ndslice_test) unittest
{
    import mir.functional: naryFun;
    auto data = [1, 3, 8, 18];
    auto diff = SlideIterator!(int*, 2, naryFun!"b - a")(data.ptr);
    assert(*diff == 2);
    assert(diff[1] == 5);
    assert(diff[2] == 10);
}

auto IndexIterator__map(Iterator, Field, alias fun)(ref IndexIterator!(Iterator, Field) it)
{
    auto field = it._field._mapField!fun;
    return IndexIterator!(Iterator, typeof(field))(it._iterator, field);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    import mir.ndslice.slice;
    auto indices = [4, 3, 1, 2, 0, 4].sliced;
    auto v = iota(5).indexed(indices).map!(a => a).slice;
    uint r;
    auto w = iota(5).indexed(indices).map!(a => a).map!(a => a * r).slice;
}

/++
Iterates a field using an iterator.

`IndexIterator` is used by $(SUBREF topology, indexed).
+/
struct IndexIterator(Iterator, Field)
{
    import mir.functional: RefTuple, autoExpandAndForward;

@optmath:
    ///
    Iterator _iterator;
    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        return IndexIterator!(LightConstOf!Iterator, LightConstOf!Field)(.lightConst(_iterator), .lightConst(_field));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return IndexIterator!(LightImmutableOf!Iterator, LightImmutableOf!Field)(.lightImmutable(_iterator), _field.lightImmutable);
    }

    ///
    static alias __map(alias fun) = IndexIterator__map!(Iterator, Field, fun);

    auto ref opUnary(string op : "*")()
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = *_iterator;
            return _field[autoExpandAndForward!t];
        }
        else
            return _field[*_iterator];
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
        {
            auto t = _iterator[index];
            return _field[autoExpandAndForward!t];
        }
        else
            return _field[_iterator[index]];
    }

    static if (!__traits(compiles, &opIndex(ptrdiff_t.init)))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index) scope
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return _field[autoExpandAndForward!t] = value;
            }
            else
                return _field[_iterator[index]] = value;
        }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin(op ~ "_field[autoExpandAndForward!t]");
            }
            else
                return mixin(op ~ "_field[_iterator[index]]");
        }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        {
            static if (is(typeof(_iterator[0]) : RefTuple!T, T...))
            {
                auto t = _iterator[index];
                return mixin("_field[autoExpandAndForward!t]" ~ op ~ "= value");
            }
            else
                return mixin("_field[_iterator[index]]" ~ op ~ "= value");
        }
    }

    mixin(std_ops);
}

/++
Iterates chunks in a sliceable using an iterator composed of indices.

Definition:
----
auto index = iterator[i];
auto elem  = sliceable[index[0] .. index[1]];
----
+/
struct SubSliceIterator(Iterator, Sliceable)
{
@optmath:
    ///
    Iterator _iterator;
    ///
    Sliceable _sliceable;

    ///
    auto lightConst()() const @property
    {
        return SubSliceIterator!(LightConstOf!Iterator, LightConstOf!Sliceable)(.lightConst(_iterator), _sliceable.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return SubSliceIterator!(LightImmutableOf!Iterator, LightImmutableOf!Sliceable)(.lightImmutable(_iterator), _sliceable.lightImmutable);
    }

    auto ref opUnary(string op : "*")()
    {
        auto i = *_iterator;
        return _sliceable[i[0] .. i[1]];
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        auto i = _iterator[index];
        return _sliceable[i[0] .. i[1]];
    }

    mixin(std_ops);
}

/++
Iterates chunks in a sliceable using an iterator composed of indices stored consequently.

Definition:
----
auto elem  = _sliceable[_iterator[index] .. _iterator[index + 1]];
----
+/
struct ChopIterator(Iterator, Sliceable)
{
@optmath:
    ///
    Iterator _iterator;
    ///
    Sliceable _sliceable;

    ///
    auto lightConst()() const @property
    {
        return ChopIterator!(LightConstOf!Iterator, LightConstOf!Sliceable)(.lightConst(_iterator), _sliceable.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return ChopIterator!(LightImmutableOf!Iterator, LightImmutableOf!Sliceable)(.lightImmutable(_iterator), _sliceable.lightImmutable);
    }

    auto ref opUnary(string op : "*")()
    {
        return _sliceable[*_iterator .. _iterator[1]];
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        return _sliceable[_iterator[index] .. _iterator[index + 1]];
    }

    mixin(std_ops);
}

/++
Iterates on top of another iterator and returns a slice
as a multidimensional window at the current position.

`SliceIterator` is used by $(SUBREF topology, map) for packed slices.
+/
struct SliceIterator(Iterator, size_t N = 1, SliceKind kind = Contiguous)
{
@optmath:
    ///
    alias Element = Slice!(Iterator, N, kind);
    ///
    Element._Structure _structure;
    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return SliceIterator!(LightConstOf!Iterator, N, kind)(_structure, .lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return SliceIterator!(LightImmutableOf!Iterator, N, kind)(_structure, .lightImmutable(_iterator));
    }

    auto opUnary(string op : "*")()
    {
        return Element(_structure, _iterator);
    }

    auto opIndex()(ptrdiff_t index)
    {
        return Element(_structure, _iterator + index);
    }

    mixin(std_ops);
}

public auto FieldIterator__map(Field, alias fun)(FieldIterator!(Field) it)
{
    import mir.ndslice.field: _mapField;
    auto field = it._field._mapField!fun;
    return FieldIterator!(typeof(field))(it._index, field);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = ndiota(3, 3).map!(a => a).slice;
    uint r;
    auto w = ndiota(3, 3).map!(a => a).map!(a => a[0] * r).slice;
}

/++
Creates an iterator on top of a field.

`FieldIterator` is used by $(SUBREF slice, slicedField), $(SUBREF topology, bitwise), $(SUBREF topology, ndiota), and others.
+/
struct FieldIterator(Field)
{
@optmath:
    ///
    ptrdiff_t _index;
    ///
    Field _field;

    ///
    auto lightConst()() const @property
    {
        return FieldIterator!(LightConstOf!Field)(_index, .lightConst(_field));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return FieldIterator!(LightImmutableOf!Field)(_index, .lightImmutable(_field));
    }

    ///
    static alias __map(alias fun) = FieldIterator__map!(Field, fun);

    ///
    Slice!(IotaIterator!size_t) opSlice(size_t dimension)(size_t i, size_t j) scope const
    {
        assert(i <= j);
        return typeof(return)(j - i, typeof(return).Iterator(i));
    }

    /++
    Returns:
        `_field[_index + sl.i .. _index + sl.j]`.
    +/
    auto opIndex()(Slice!(IotaIterator!size_t) sl)
    {
        auto idx = _index + sl._iterator._index;
        return _field[idx .. idx + sl.length];
    }

    auto ref opUnary(string op : "*")()
    { return _field[_index]; }

    void opUnary(string op)() scope
        if (op == "++" || op == "--")
    { mixin(op ~ `_index;`); }

    auto ref opIndex()(ptrdiff_t index)
    { return _field[_index + index]; }

    static if (!__traits(compiles, &_field[_index]))
    {
        auto ref opIndexAssign(T)(auto ref T value, ptrdiff_t index)
        { return _field[_index + index] = value; }

        auto ref opIndexUnary(string op)(ptrdiff_t index)
        { mixin (`return ` ~ op ~ `_field[_index + index];`); }

        auto ref opIndexOpAssign(string op, T)(T value, ptrdiff_t index)
        { mixin (`return _field[_index + index] ` ~ op ~ `= value;`); }
    }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "+" || op == "-")
    { mixin(`_index ` ~ op ~ `= index;`); }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    { return this._index - right._index; }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._index == right._index; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    { return this._index - right._index; }

    ///
    auto assumeFieldsHaveZeroShift() @property
    {
        if (_expect(_index != 0, false))
        {
            version (D_Exceptions)
                throw assumeZeroShiftException;
            else
                assert(0, assumeZeroShiftExceptionMsg);
        }
        static if (hasZeroShiftFieldMember!Field)
            return _field.assumeFieldsHaveZeroShift;
        else
            return _field;
    }
}

auto FlattenedIterator__map(Iterator, size_t N, SliceKind kind, alias fun)(FlattenedIterator!(Iterator, N, kind) it)
{
    import mir.ndslice.topology: map;
    auto slice = it._slice.map!fun;
    return FlattenedIterator!(TemplateArgsOf!(typeof(slice)))(it._indices, slice);
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.allocation;
    auto v = iota(3, 3).universal.flattened.map!(a => a).slice;
    uint r;
    auto w = iota(3, 3).universal.flattened.map!(a => a).map!(a => a * r).slice;
}

/++
Creates an iterator on top of all elements in a slice.

`FieldIterator` is used by $(SUBREF topology, bitwise), $(SUBREF topology, ndiota), and others.
+/
struct FlattenedIterator(Iterator, size_t N, SliceKind kind)
    if (N > 1 && (kind == Universal || kind == Canonical))
{
@optmath:
    ///
    ptrdiff_t[N] _indices;
    ///
    Slice!(Iterator, N, kind) _slice;

    ///
    auto lightConst()() const @property
    {
        return FlattenedIterator!(LightConstOf!Iterator, N, kind)(_indices, _slice.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return FlattenedIterator!(LightImmutableOf!Iterator, N, kind)(_indices, _slice.lightImmutable);
    }

    ///
    static alias __map(alias fun) = FlattenedIterator__map!(Iterator, N, kind, fun);

    private ptrdiff_t getShift()(ptrdiff_t n)
    {
        ptrdiff_t _shift;
        n += _indices[$ - 1];
        foreach_reverse (i; Iota!(1, N))
        {
            immutable v = n / ptrdiff_t(_slice._lengths[i]);
            n %= ptrdiff_t(_slice._lengths[i]);
            static if (i == _slice.S)
                _shift += (n - _indices[i]);
            else
                _shift += (n - _indices[i]) * _slice._strides[i];
            n = _indices[i - 1] + v;
        }
        _shift += (n - _indices[0]) * _slice._strides[0];
        return _shift;
    }

    auto ref opUnary(string op : "*")()
    {
        return *_slice._iterator;
    }

    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    {
        foreach_reverse (i; Iota!N)
        {
            static if (i == _slice.S)
                mixin(op ~ `_slice._iterator;`);
            else
                mixin(`_slice._iterator ` ~ op[0] ~ `= _slice._strides[i];`);
            mixin (op ~ `_indices[i];`);
            static if (i)
            {
                static if (op == "++")
                {
                    if (_indices[i] < _slice._lengths[i])
                        return;
                    static if (i == _slice.S)
                        _slice._iterator -= _slice._lengths[i];
                    else
                        _slice._iterator -= _slice._lengths[i] * _slice._strides[i];
                    _indices[i] = 0;
                }
                else
                {
                    if (_indices[i] >= 0)
                        return;
                    static if (i == _slice.S)
                        _slice._iterator += _slice._lengths[i];
                    else
                        _slice._iterator += _slice._lengths[i] * _slice._strides[i];
                    _indices[i] = _slice._lengths[i] - 1;
                }
            }
        }
    }

    auto ref opIndex()(ptrdiff_t index)
    {
        return _slice._iterator[getShift(index)];
    }

    static if (isMutable!(_slice.DeepElement) && !_slice.hasAccessByRef)
    ///
    auto ref opIndexAssign(E)(scope ref E elem, size_t index) return scope
    {
        return _slice._iterator[getShift(index)] = elem;
    }

    void opOpAssign(string op : "+")(ptrdiff_t n) scope
    {
        ptrdiff_t _shift;
        n += _indices[$ - 1];
        foreach_reverse (i; Iota!(1, N))
        {
            immutable v = n / ptrdiff_t(_slice._lengths[i]);
            n %= ptrdiff_t(_slice._lengths[i]);
            static if (i == _slice.S)
                _shift += (n - _indices[i]);
            else
                _shift += (n - _indices[i]) * _slice._strides[i];
            _indices[i] = n;
            n = _indices[i - 1] + v;
        }
        _shift += (n - _indices[0]) * _slice._strides[0];
        _indices[0] = n;
        foreach_reverse (i; Iota!(1, N))
        {
            if (_indices[i] >= 0)
                break;
            _indices[i] += _slice._lengths[i];
            _indices[i - 1]--;
        }
        _slice._iterator += _shift;
    }

    void opOpAssign(string op : "-")(ptrdiff_t n) scope
    { this += -n; }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    {
        ptrdiff_t ret = this._indices[0] - right._indices[0];
        foreach (i; Iota!(1, N))
        {
            ret *= _slice._lengths[i];
            ret += this._indices[i] - right._indices[i];
        }
        return ret;
    }

    bool opEquals()(scope ref const typeof(this) right) scope const
    {
        foreach_reverse (i; Iota!N)
            if (this._indices[i] != right._indices[i])
                return false;
        return true;
    }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    {
        foreach (i; Iota!(N - 1))
            if (auto ret = this._indices[i] - right._indices[i])
                return ret;
        return this._indices[$ - 1] - right._indices[$ - 1];
    }
}

version(mir_ndslice_test) unittest
{
    import mir.ndslice.topology;
    import mir.ndslice.slice;

    auto it0 = iota(3, 4).universal.flattened._iterator;
    auto it1 = it0;
    assert(it0 == it1);
    it0 += 5;
    assert(it0 > it1);
    it0 -= 5;
    assert(*it0 == *it1);
    assert(it0 == it1);
    it0 += 5;
    it0 += 7;
    it0 -= 9;
    assert(it0 > it1);
    it1 += 3;
    assert(*it0 == *it1);
    assert(it0 == it1);
    assert(it0 <= it1);
    assert(it0 >= it1);

    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;
    ++it0;

    assert(it0 - it1 == 9);
    assert(it1 - it0 == -9);

    ++it0;

    assert(it0 - it1 == 10);
    assert(it1 - it0 == -10);

    --it0;

    assert(it0 - it1 == 9);
    assert(it1 - it0 == -9);
    assert(it0[-9] == *it1);
    assert(*it0 == it1[9]);

    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    --it0;
    assert(*it0 == *it1);
    assert(it0 == it1);
    assert(it0 <= it1);
    assert(it0 >= it1);
}

/++
`StairsIterator` is used by $(SUBREF topology, stairs).
+/
struct StairsIterator(Iterator, string direction)
    if (direction == "+" || direction == "-")
{
    ///
    size_t _length;

    ///
    Iterator _iterator;

    ///
    auto lightConst()() const @property
    {
        return StairsIterator!(LightConstOf!Iterator, direction)(_length, .lightConst(_iterator));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return StairsIterator!(LightImmutableOf!Iterator, direction)(_length, .lightImmutable(_iterator));
    }

@optmath:

    ///
    Slice!Iterator opUnary(string op : "*")()
    {
        import mir.ndslice.slice: sliced;
        return _iterator.sliced(_length);
    }

    ///
    Slice!Iterator opIndex()(ptrdiff_t index)
    {
        import mir.ndslice.slice: sliced;
        static if (direction == "+")
        {
            auto newLength = _length + index;
            auto shift = ptrdiff_t(_length + newLength - 1) * index / 2;
        }
        else
        {
            auto newLength = _length - index;
            auto shift = ptrdiff_t(_length + newLength + 1) * index / 2;
        }
        assert(ptrdiff_t(newLength) >= 0);
        return (_iterator + shift).sliced(newLength);
    }

    void opUnary(string op)() scope
        if (op == "--" || op == "++")
    {
        static if (op == "++")
        {
            _iterator += _length;
            static if (direction == "+")
                ++_length;
            else
                --_length;
        }
        else
        {
            assert(_length);
            static if (direction == "+")
                --_length;
            else
                ++_length;
            _iterator -= _length;
        }
    }

    void opOpAssign(string op)(ptrdiff_t index) scope
        if (op == "-" || op == "+")
    {
        static if (op == direction)
            auto newLength = _length + index;
        else
            auto newLength = _length - index;
        static if (direction == "+")
            auto shift = ptrdiff_t(_length + newLength - 1) * index / 2;
        else
            auto shift = ptrdiff_t(_length + newLength + 1) * index / 2;
        assert(ptrdiff_t(newLength) >= 0);
        _length = newLength;
        static if (op == "+")
            _iterator += shift;
        else
            _iterator -= shift;
    }

    auto opBinary(string op)(ptrdiff_t index)
        if (op == "+" || op == "-")
    {
        auto ret = this;
        mixin(`ret ` ~ op ~ `= index;`);
        return ret;
    }

    ptrdiff_t opBinary(string op : "-")(scope ref const typeof(this) right) scope const
    {
        static if (direction == "+")
            return this._length - right._length;
        else
            return right._length - this._length;
    }

    bool opEquals()(scope ref const typeof(this) right) scope const
    { return this._length == right._length; }

    ptrdiff_t opCmp()(scope ref const typeof(this) right) scope const
    { return this - right; }
}

///
version(mir_ndslice_test) unittest
{
    // 0
    // 1 2
    // 3 4 5
    // 6 7 8 9
    // 10 11 12 13 14
    auto it = StairsIterator!(IotaIterator!size_t, "+")(1, IotaIterator!size_t());
    assert(*it == [0]);
    assert(it[4] == [10, 11, 12, 13, 14]);
    assert(*(it + 4) == [10, 11, 12, 13, 14]);
    ++it;
    assert(*it == [1, 2]);
    it += 3;
    assert(*it == [10, 11, 12, 13, 14]);
    assert(it[-3] == [1, 2]);
    assert(*(it - 3) == [1, 2]);
    assert(it + 1 > it);
    assert(it + 1 - 1 == it);
    assert(it - 3 - it == -3);
    --it;
    assert(*it == [6, 7, 8, 9]);
}

///
version(mir_ndslice_test) unittest
{
    // [0, 1, 2, 3, 4],
    //    [5, 6, 7, 8],
    //     [9, 10, 11],
    //        [12, 13],
    //            [14]]);

    auto it = StairsIterator!(IotaIterator!size_t, "-")(5, IotaIterator!size_t());
    assert(*it == [0, 1, 2, 3, 4]);
    assert(it[4] == [14]);
    assert(*(it + 4) == [14]);
    ++it;
    assert(*it == [5, 6, 7, 8]);
    it += 3;
    assert(*it == [14]);
    assert(it[-3] == [5, 6, 7, 8]);
    assert(*(it - 3) == [5, 6, 7, 8]);
    assert(it + 1 > it);
    assert(it + 1 - 1 == it);
    assert(it - 3 - it == -3);
    --it;
    assert(*it == [12, 13]);
}

/++
Element type of $(LREF TripletIterator).
+/
struct Triplet(Iterator, SliceKind kind = Contiguous)
{
@optmath:
    ///
    size_t _iterator;
    ///
    Slice!(Iterator, 1, kind) _slice;

    ///
    auto lightConst()() const @property
    {
        return Triplet!(LightConstOf!Iterator, kind)(_iterator, slice.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return Triplet!(LightImmutableOf!Iterator, kind)(_iterator, slice.lightImmutable);
    }

    @property
    {
        ///
        auto ref center()
        {
            assert(_iterator < _slice.length);
            return _slice[_iterator];
        }

        ///
        Slice!(Iterator, 1, kind) left()
        {
            assert(_iterator < _slice.length);
            return _slice[0 .. _iterator];
        }

        ///
        Slice!(Iterator, 1, kind) right()
        {
            assert(_iterator < _slice.length);
            return _slice[_iterator + 1 .. $];
        }
    }
}

/++
Iterates triplets position in a slice. 

`TripletIterator` is used by $(SUBREF topology, triplets).
+/
struct TripletIterator(Iterator, SliceKind kind = Contiguous)
{
@optmath:

    ///
    size_t _iterator;
    ///
    Slice!(Iterator, 1, kind) _slice;

    ///
    auto lightConst()() const @property
    {
        return TripletIterator!(LightConstOf!Iterator, kind)(_iterator, _slice.lightConst);
    }

    ///
    auto lightImmutable()() immutable @property
    {
        return TripletIterator!(LightImmutableOf!Iterator, kind)(_iterator, _slice.lightImmutable);
    }

    ///
    Triplet!(Iterator, kind) opUnary(string op : "*")()
    {
        return typeof(return)(_iterator, _slice);
    }

    ///
    Triplet!(Iterator, kind) opIndex()(ptrdiff_t index)
    {
        return typeof(return)(_iterator + index, _slice);
    }

    mixin(std_ops);
}
