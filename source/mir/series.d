/++
$(H1 Index-series)

The module contains $(LREF Series) data structure with special iteration and indexing methods.
It is aimed to construct index or time-series using Mir and Phobos algorithms.

Public_imports: $(MREF mir,ndslice,slice).

Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
NDSLICE = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.series;

public import mir.ndslice.slice;
public import mir.ndslice.sorting: sort;
import mir.ndslice.iterator: IotaIterator;
import mir.ndslice.sorting: transitionIndex;
import mir.qualifier;
import std.traits;

/++
See_also: $(LREF unionSeries), $(LREF troykaSeries), $(LREF troykaGalop).
+/
@safe version(mir_test) unittest
{
    import mir.ndslice;
    import mir.series;

    import mir.array.allocation: array;
    import mir.algorithm.setops: multiwayUnion;

    import std.datetime: Date;
    static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
    import std.exception: collectExceptionMsg;

    //////////////////////////////////////
    // Constructs two time-series.
    //////////////////////////////////////
    auto index0 = [
        Date(2017, 01, 01),
        Date(2017, 03, 01),
        Date(2017, 04, 01)];

    auto data0 = [1.0, 3, 4];
    auto series0 = index0.series(data0);

    auto index1 = [
        Date(2017, 01, 01),
        Date(2017, 02, 01),
        Date(2017, 05, 01)];

    auto data1 = [10.0, 20, 50];
    auto series1 = index1.series(data1);    

    //////////////////////////////////////
    // asSlice method
    //////////////////////////////////////
    assert(series0
        .asSlice
        // ref qualifier is optional
        .map!((ref key, ref value) => key.month == value)
        .all);

    //////////////////////////////////////
    // get* methods
    //////////////////////////////////////

    auto refDate = Date(2017, 03, 01);
    auto missingDate = Date(2016, 03, 01);

    // default value
    double defaultValue = 100;
    assert(series0.get(refDate, defaultValue) == 3);
    assert(series0.get(missingDate, defaultValue) == defaultValue);

    // Exceptions handlers
    assert(series0.get(refDate) == 3);
    assert(series0.get(refDate, new Exception("My exception msg")) == 3);
    assert(series0.getVerbose(refDate) == 3);    
    assert(series0.getExtraVerbose(refDate, "My exception msg") == 3);    

    assert(collectExceptionMsg!Exception(
            series0.get(missingDate)
        ) == "Series double[Date]: Missing required key");
    
    assert(collectExceptionMsg!Exception(
            series0.get(missingDate, new Exception("My exception msg"))
        ) == "My exception msg");
    
    assert(collectExceptionMsg!Exception(
            series0.getVerbose(missingDate)
        ) == "Series double[Date]: Missing 2016-Mar-01 key");
    
    assert(collectExceptionMsg!Exception(
            series0.getExtraVerbose(missingDate, "My exception msg")
        ) == "My exception msg. Series double[Date]: Missing 2016-Mar-01 key");

    // assign with get*
    series0.get(refDate) = 100; 
    assert(series0.get(refDate) == 100); 
    series0.get(refDate) = 3; 

    // tryGet
    double val;
    assert(series0.tryGet(refDate, val));
    assert(val == 3);
    assert(!series0.tryGet(missingDate, val));
    assert(val == 3); // val was not changed

    //////////////////////////////////////
    // Merges multiple series into one.
    // Allocates using GC. M
    // Makes exactly two allocations per merge:
    // one for index/time and one for data.
    //////////////////////////////////////
    auto m0 = unionSeries(series0, series1);
    auto m1 = unionSeries(series1, series0); // order is matter

    assert(m0.index == [
        Date(2017, 01, 01),
        Date(2017, 02, 01),
        Date(2017, 03, 01),
        Date(2017, 04, 01),
        Date(2017, 05, 01)]);

    assert(m0.index == m1.index);
    assert(m0.data == [ 1, 20,  3,  4, 50]);
    assert(m1.data == [10, 20,  3,  4, 50]);

    //////////////////////////////////////
    // Joins two time-series into a one with two columns.
    //////////////////////////////////////
    auto u = [index0, index1].multiwayUnion;
    auto index = u.move.array;
    auto data = slice!double([index.length, 2], 0); // initialized to 0 value
    auto series = index.series(data);

    series[0 .. $, 0][].opIndexAssign(series0); // fill first column
    series[0 .. $, 1][] = series1; // fill second column

    assert(data == [
        [1, 10],
        [0, 20],
        [3,  0],
        [4,  0],
        [0, 50]]);
}

///
unittest{

    import mir.series;

    double[int] map;
    map[1] = 4.0;
    map[2] = 5.0;
    map[4] = 6.0;
    map[5] = 10.0;
    map[10] = 11.0;

    const s = series(map);

    double value;
    int key;
    assert(s.tryGet(2, value) && value == 5.0);
    assert(!s.tryGet(8, value));

    assert(s.tryGetNext(2, value) && value == 5.0);
    assert(s.tryGetPrev(2, value) && value == 5.0);
    assert(s.tryGetNext(8, value) && value == 11.0);
    assert(s.tryGetPrev(8, value) && value == 10.0);
    assert(!s.tryGetFirst(8, 9, value));
    assert(s.tryGetFirst(2, 10, value) && value == 5.0);
    assert(s.tryGetLast(2, 10, value) && value == 11.0);
    assert(s.tryGetLast(2, 8, value) && value == 10.0);

    key = 2; assert(s.tryGetNextUpdateKey(key, value) && key == 2 && value == 5.0);
    key = 2; assert(s.tryGetPrevUpdateKey(key, value) && key == 2 && value == 5.0);
    key = 8; assert(s.tryGetNextUpdateKey(key, value) && key == 10 && value == 11.0);
    key = 8; assert(s.tryGetPrevUpdateKey(key, value) && key == 5 && value == 10.0);
    key = 2; assert(s.tryGetFirstUpdateLower(key, 10, value) && key == 2 && value == 5.0);
    key = 10; assert(s.tryGetLastUpdateKey(2, key, value) && key == 10 && value == 11.0);
    key = 8; assert(s.tryGetLastUpdateKey(2, key, value) && key == 5 && value == 10.0);
}

import mir.ndslice.slice;
import mir.ndslice.internal: is_Slice, isIndex;
import mir.math.common: optmath;

import std.meta;

@optmath:

/++
Plain index/time observation data structure.
Observation are used as return tuple for for indexing $(LREF Series).
+/
struct mir_observation(Index, Data)
{
    /// Date, date-time, time, or index.
    Index index;
    /// An alias for time-series index.
    alias time = index;
    /// An alias for key-value representation.
    alias key = index;
    /// Value or ndslice.
    Data data;
    /// An alias for key-value representation.
    alias value = data;
}

/// ditto
alias Observation = mir_observation;

/// Convenient function for $(LREF Observation) construction.
auto observation(Index, Data)(Index index, Data data)
{
    return mir_observation!(Index, Data)(index, data);
}

/++
Convinient alias for 1D Contiguous $(LREF Series).
+/
alias SeriesMap(K, V) = mir_series!(K*, V*);

///
version(mir_test) unittest
{
    import std.traits;
    import mir.series;

    static assert (is(SeriesMap!(string, double) == Series!(string*, double*)));

    /// LHS, RHS
    static assert (isAssignable!(SeriesMap!(string, double), SeriesMap!(string, double)));
    static assert (isAssignable!(SeriesMap!(string, double), typeof(null)));

    static assert (isAssignable!(SeriesMap!(const string, double), SeriesMap!(string, double)));
    static assert (isAssignable!(SeriesMap!(string, const double), SeriesMap!(string, double)));
    static assert (isAssignable!(SeriesMap!(const string, const double), SeriesMap!(string, double)));

    static assert (isAssignable!(SeriesMap!(immutable string, double), SeriesMap!(immutable string, double)));
    static assert (isAssignable!(SeriesMap!(immutable string, const double), SeriesMap!(immutable string, double)));
    static assert (isAssignable!(SeriesMap!(const string, const double), SeriesMap!(immutable string, double)));
    static assert (isAssignable!(SeriesMap!(string, immutable double), SeriesMap!(string, immutable double)));
    static assert (isAssignable!(SeriesMap!(const string, immutable double), SeriesMap!(string, immutable double)));
    static assert (isAssignable!(SeriesMap!(const string, const double), SeriesMap!(string, immutable double)));
    // etc
}

/++
Plain index series data structure.

`*.index[i]`/`*.key[i]`/`*.time` corresponds to `*.data[i]`/`*.value`.

Index is assumed to be sorted.
$(LREF sort) can be used to normalise a series.
+/
struct mir_series(IndexIterator_, Iterator_, size_t N_ = 1, SliceKind kind_ = Contiguous)
{
    private enum doUnittest = is(typeof(this) == Series!(int*, double*));

    ///
    alias IndexIterator = IndexIterator_;

    ///
    alias Iterator = Iterator_;

    ///
    enum size_t N = N_;

    ///
    enum SliceKind kind = kind_;

    ///
    Slice!(Iterator, N, kind) _data;

    ///
    IndexIterator _index;

    /// Index / Key / Time type aliases
    alias Index = typeof(this.front.index);
    /// ditto
    alias Key = Index;
    /// ditto
    alias Time = Index;
    /// Data / Value type aliases
    alias Data = typeof(this.front.data);
    /// ditto
    alias Value = Data;

    /// An alias for time-series index.
    alias time = index;
    /// An alias for key-value representation.
    alias key = index;
    /// An alias for key-value representation.
    alias value = data;

    private enum defaultMsg() = "Series " ~ Unqual!(this.Data).stringof ~ "[" ~ Unqual!(this.Index).stringof ~ "]: Missing";
    private static immutable defaultExc() = new Exception(defaultMsg!() ~ " required key");

@optmath:

    ///
    this()(Slice!IndexIterator index, Slice!(Iterator, N, kind) data)
    {
        assert(index.length == data.length, "Series constructor: index and data lengths must be equal.");
        _data = data;
        _index = index._iterator;
    }


    /// Construct from null
    this(typeof(null))
    {
        _data = _data.init;
        _index = _index.init;
    }

    ///
    bool opEquals(RIndexIterator, RIterator, size_t RN, SliceKind rkind, )(Series!(RIndexIterator, RIterator, RN, rkind) rhs) const
    {
        return this.lightScopeIndex == rhs.lightScopeIndex && this._data.lightScope == rhs._data.lightScope;
    }

    /++
    Index series is assumed to be sorted.

    `IndexIterator` is an iterator on top of date, date-time, time, or numbers or user defined types with defined `opCmp`.
    For example, `Date*`, `DateTime*`, `immutable(long)*`, `mir.ndslice.iterator.IotaIterator`.
    +/
    auto index()() @property @trusted
    {
        return _index.sliced(_data._lengths[0]);
    }

    /// ditto
    auto index()() @property @trusted const
    {
        return _index.lightConst.sliced(_data._lengths[0]);
    }

    /// ditto
    auto index()() @property @trusted immutable
    {
        return _index.lightImmutable.sliced(_data._lengths[0]);
    }

    private auto lightScopeIndex()() @property @trusted
    {
        return .lightScope(_index).sliced(_data._lengths[0]);
    }

    private auto lightScopeIndex()() @property @trusted const
    {
        return .lightScope(_index).sliced(_data._lengths[0]);
    }

    private auto lightScopeIndex()() @property @trusted immutable
    {
        return .lightScope(_index).sliced(_data._lengths[0]);
    }

    /++
    Data is any ndslice with only one constraints, 
    `data` and `index` lengths should be equal.
    +/
    auto data()() @property @trusted
    {
        return _data;
    }

    /// ditto
    auto data()() @property @trusted const
    {
        return _data[];
    }

    /// ditto
    auto data()() @property @trusted immutable
    {
        return _data[];
    }

    ///
    typeof(this) opBinary(string op : "~")(typeof(this) rhs)
    {
        return unionSeries(this.lightScope, rhs.lightScope);
    }

    /// ditto
    auto opBinary(string op : "~")(const typeof(this) rhs) const
    {
        return unionSeries(this.lightScope, rhs.lightScope);
    }

    static if (doUnittest)
    ///
    @safe pure nothrow version(mir_test) unittest
    {
        import std.datetime: Date;

        //////////////////////////////////////
        // Constructs two time-series.
        //////////////////////////////////////
        auto index0 = [1,3,4];
        auto data0 = [1.0, 3, 4];
        auto series0 = index0.series(data0);

        auto index1 = [1,2,5];
        auto data1 = [10.0, 20, 50];
        auto series1 = index1.series(data1);

        //////////////////////////////////////
        // Merges multiple series into one.
        //////////////////////////////////////
        // Order is matter.
        // The first slice has higher priority.
        auto m0 = series0 ~ series1;
        auto m1 = series1 ~ series0;

        assert(m0.index == m1.index);
        assert(m0.data == [ 1, 20,  3,  4, 50]);
        assert(m1.data == [10, 20,  3,  4, 50]);
    }

    static if (doUnittest)
    @safe pure nothrow version(mir_test) unittest
    {
        import std.datetime: Date;

        //////////////////////////////////////
        // Constructs two time-series.
        //////////////////////////////////////
        auto index0 = [1,3,4];
        auto data0 = [1.0, 3, 4];
        auto series0 = index0.series(data0);

        auto index1 = [1,2,5];
        auto data1 = [10.0, 20, 50];
        const series1 = index1.series(data1);

        //////////////////////////////////////
        // Merges multiple series into one.
        //////////////////////////////////////
        // Order is matter.
        // The first slice has higher priority.
        auto m0 = series0 ~ series1;
        auto m1 = series1 ~ series0;

        assert(m0.index == m1.index);
        assert(m0.data == [ 1, 20,  3,  4, 50]);
        assert(m1.data == [10, 20,  3,  4, 50]);
    }

    /++
    Special `[] =` index-assign operator for index-series.
    Assigns data from `r` with index intersection.
    If a index index in `r` is not in the index index for this series, then no op-assign will take place.
    This and r series are assumed to be sorted.

    Params:
        r = rvalue index-series
    +/
    void opIndexAssign(IndexIterator_, Iterator_, size_t N_, SliceKind kind_)
        (Series!(IndexIterator_, Iterator_, N_, kind_) r)
    {
        opIndexOpAssign!("", IndexIterator_, Iterator_, N_, kind_)(r);
    }

    static if (doUnittest)
    ///
    version(mir_test) unittest
    {
        auto index = [1, 2, 3, 4];
        auto data = [10.0, 10, 10, 10];
        auto series = index.series(data);

        auto rindex = [0, 2, 4, 5];
        auto rdata = [1.0, 2, 3, 4];
        auto rseries = rindex.series(rdata);

        // series[] = rseries;
        series[] = rseries;
        assert(series.data == [10, 2, 10, 3]);
    }

    /++
    Special `[] op=` index-op-assign operator for index-series.
    Op-assigns data from `r` with index intersection.
    If a index index in `r` is not in the index index for this series, then no op-assign will take place.
    This and r series are assumed to be sorted.

    Params:
        rSeries = rvalue index-series
    +/
    void opIndexOpAssign(string op, IndexIterator_, Iterator_, size_t N_, SliceKind kind_)
        (auto ref Series!(IndexIterator_, Iterator_, N_, kind_) rSeries)
    {
        auto l = this.lightScope;
        auto r = rSeries.lightScope;
        if (r.empty)
            return;
        if (l.empty)
            return;
        Unqual!(typeof(*r._index)) rf = *r._index;
        Unqual!(typeof(*l._index)) lf = *l._index;
        goto Begin;
    R:
        r.popFront;
        if (r.empty)
            goto End;
        rf = *r._index;
    Begin:
        if (lf > rf)
            goto R;
        if (lf < rf)
            goto L;
    E:
        static if (N != 1)
            mixin("l.data.front[] " ~ op ~ "= r.data.front;");
        else
            mixin("l.data.front   " ~ op ~ "= r.data.front;");

        r.popFront;
        if (r.empty)
            goto End;
        rf = *r._index;
    L:
        l.popFront;
        if (l.empty)
            goto End;
        lf = *l._index;

        if (lf < rf)
            goto L;
        if (lf == rf)
            goto E;
        goto R;
    End:
    }

    static if (doUnittest)
    ///
    version(mir_test) unittest
    {
        auto index = [1, 2, 3, 4];
        auto data = [10.0, 10, 10, 10];
        auto series = index.series(data);

        auto rindex = [0, 2, 4, 5];
        auto rdata = [1.0, 2, 3, 4];
        auto rseries = rindex.series(rdata);

        series[] += rseries;
        assert(series.data == [10, 12, 10, 13]);
    }

    /++
    This function uses a search with policy sp to find the largest left subrange on which 
    `t < key` is true for all `t`.
    The search schedule and its complexity are documented in `std.range.SearchPolicy`.
    +/
    auto lowerBound(Index)(auto ref scope const Index key)
    {
        return opIndex(opSlice(0, lightScopeIndex.transitionIndex(key)));
    }

    /// ditto
    auto lowerBound(Index)(auto ref scope const Index key) const
    {
        return opIndex(opSlice(0, lightScopeIndex.transitionIndex(key)));
    }


    /++
    This function uses a search with policy sp to find the largest left subrange on which 
    `t > key` is true for all `t`.
    The search schedule and its complexity are documented in `std.range.SearchPolicy`.
    +/
    auto upperBound(Index)(auto ref scope const Index key)
    {
        return opIndex(opSlice(lightScopeIndex.transitionIndex!"a <= b"(key), length));
    }

    /// ditto
    auto upperBound(Index)(auto ref scope const Index key) const
    {
        return opIndex(opSlice(lightScopeIndex.transitionIndex!"a <= b"(key), length));
    }

    /**
    Gets data for the index.
    Params:
        key = index
        _default = default value is returned if the series does not contains the index.
    Returns:
        data that corresponds to the index or default value.
    */
    ref get(Index, Value)(auto ref scope const Index key, return ref Value _default) @trusted
        if (!is(Value : const(Exception)))
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        return idx < _data._lengths[0] && _index[idx] == key ? _data[idx] : _default;
    }

    /// ditto
    ref get(Index, Value)(auto ref scope const Index key, return ref Value _default) const
        if (!is(Value : const(Exception)))
    {
        return this.lightScope.get(key, _default);
    }

    /// ditto
    ref get(Index, Value)(auto ref scope const Index key, return ref Value _default) immutable
        if (!is(Value : const(Exception)))
    {
        return this.lightScope.get(key, _default);
    }

    auto get(Index, Value)(auto ref scope const Index key, Value _default) @trusted
        if (!is(Value : const(Exception)))
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        return idx < _data._lengths[0] && _index[idx] == key ? _data[idx] : _default;
    }

    /// ditto
    auto get(Index, Value)(auto ref scope const Index key, Value _default) const
        if (!is(Value : const(Exception)))
    {
        import mir.functional: forward;
        return this.lightScope.get(key, forward!_default);
    }

    /// ditto
    auto get(Index, Value)(auto ref scope const Index key, Value _default) immutable
        if (!is(Value : const(Exception)))
    {
        import mir.functional: forward;
        return this.lightScope.get(key, forward!_default);
    }

    /**
    Gets data for the index.
    Params:
        key = index
        exc = (lazy, optional) exception to throw if the series does not contains the index.
    Returns: data that corresponds to the index.
    Throws:
        Exception if the series does not contains the index.
    See_also: $(LREF Series.getVerbose), $(LREF Series.tryGet)
    */
    auto ref get(Index)(auto ref scope const Index key) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        if (idx < _data._lengths[0] && _index[idx] == key)
        {
            return _data[idx];
        }
        throw defaultExc!();
    }

    /// ditto
    auto ref get(Index)(auto ref scope const Index key, lazy const Exception exc) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        if (idx < _data._lengths[0] && _index[idx] == key)
        {
            return _data[idx];
        }
        throw exc;
    }

    /// ditto
    auto ref get(Index)(auto ref scope const Index key) const
    {
        return this.lightScope.get(key);
    }

    /// ditto
    auto ref get(Index)(auto ref scope const Index key, lazy const Exception exc) const
    {
        return this.lightScope.get(key, exc);
    }


    /// ditto
    auto ref get(Index)(auto ref scope const Index key) immutable
    {
        return this.lightScope.get(key);
    }

    /// ditto
    auto ref get(Index)(auto ref scope const Index key, lazy const Exception exc) immutable
    {
        return this.lightScope.get(key, exc);
    }

    /**
    Gets data for the index (verbose exception).
    Params:
        key = index
    Returns: data that corresponds to the index.
    Throws:
        Detailed exception if the series does not contains the index.
    See_also: $(LREF Series.get), $(LREF Series.tryGet)
    */
    auto ref getVerbose(Index)(auto ref scope const Index key, string file = __FILE__, int line = __LINE__)
    {
        import std.format: format;
        return this.get(key, new Exception(format("%s %s key", defaultMsg!(), key), file, line));
    }

    /// ditto
    auto ref getVerbose(Index)(auto ref scope const Index key, string file = __FILE__, int line = __LINE__) const
    {
        return this.lightScope.getVerbose(key, file, line);
    }

    /// ditto
    auto ref getVerbose(Index)(auto ref scope const Index key, string file = __FILE__, int line = __LINE__) immutable
    {
        return this.lightScope.getVerbose(key, file, line);
    }

    /**
    Gets data for the index (extra verbose exception).
    Params:
        key = index
    Returns: data that corresponds to the index.
    Throws:
        Detailed exception if the series does not contains the index.
    See_also: $(LREF Series.get), $(LREF Series.tryGet)
    */
    auto ref getExtraVerbose(Index)(auto ref scope const Index key, string exceptionInto, string file = __FILE__, int line = __LINE__)
    {
        import std.format: format;
        return this.get(key, new Exception(format("%s. %s %s key", exceptionInto, defaultMsg!(), key), file, line));
    }

    /// ditto
    auto ref getExtraVerbose(Index)(auto ref scope const Index key, string exceptionInto, string file = __FILE__, int line = __LINE__) const
    {
        return this.lightScope.getExtraVerbose(key, exceptionInto, file, line);
    }

    /// ditto
    auto ref getExtraVerbose(Index)(auto ref scope const Index key, string exceptionInto, string file = __FILE__, int line = __LINE__) immutable
    {
        return this.lightScope.getExtraVerbose(key, exceptionInto, file, line);
    }

    ///
    bool contains(Index)(auto ref scope const Index key) const @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        return idx < _data._lengths[0] && _index[idx] == key;
    }

    ///
    auto opBinaryRight(string op : "in", Index)(auto ref scope const Index key) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        bool cond = idx < _data._lengths[0] && _index[idx] == key;
        static if (__traits(compiles, &_data[size_t.init]))
        {
            if (cond)
                return &_data[idx];
            return null; 
        }
        else
        {
            return bool(cond);
        }
    }

    /// ditto
    auto opBinaryRight(string op : "in", Index)(auto ref scope const Index key) const
    {
        return key in this.lightScope;
    }

    /// ditto
    auto opBinaryRight(string op : "in", Index)(auto ref scope const Index key) immutable
    {
        return key in this.lightScope;
    }

    /++
    Tries to get the first value, such that `key_i == key`.

    Returns: `true` on success.
    +/
    bool tryGet(Index, Value)(Index key, scope ref Value val) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        auto cond = idx < _data._lengths[0] && _index[idx] == key;
        if (cond)
            val = _data[idx];
        return cond;
    }

    /// ditto
    bool tryGet(Index, Value)(Index key, scope ref Value val) const
    {
        return this.lightScope.tryGet(key, val);
    }

    /// ditto
    bool tryGet(Index, Value)(Index key, scope ref Value val) immutable
    {
        return this.lightScope.tryGet(key, val);
    }

    /++
    Tries to get the first value, such that `key_i >= key`.

    Returns: `true` on success.
    +/
    bool tryGetNext(Index, Value)(auto ref scope const Index key, scope ref Value val)
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        auto cond = idx < _data._lengths[0];
        if (cond)
            val = _data[idx];
        return cond;
    }

    /// ditto
    bool tryGetNext(Index, Value)(auto ref scope const Index key, scope ref Value val) const
    {
        return this.lightScope.tryGetNext(key, val);
    }

    /// ditto
    bool tryGetNext(Index, Value)(auto ref scope const Index key, scope ref Value val) immutable
    {
        return this.lightScope.tryGetNext(key, val);
    }

    /++
    Tries to get the first value, such that `key_i >= key`.
    Updates `key` with `key_i`.

    Returns: `true` on success.
    +/
    bool tryGetNextUpdateKey(Index, Value)(scope ref Index key, scope ref Value val) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(key);
        auto cond = idx < _data._lengths[0];
        if (cond)
        {
            key = _index[idx];
            val = _data[idx];
        }
        return cond;
    }

    /// ditto
    bool tryGetNextUpdateKey(Index, Value)(scope ref Index key, scope ref Value val) const
    {
        return this.lightScope.tryGetNextUpdateKey(key, val);
    }

    /// ditto
    bool tryGetNextUpdateKey(Index, Value)(scope ref Index key, scope ref Value val) immutable
    {
        return this.lightScope.tryGetNextUpdateKey(key, val);
    }

    /++
    Tries to get the last value, such that `key_i <= key`.

    Returns: `true` on success.
    +/
    bool tryGetPrev(Index, Value)(auto ref scope const Index key, scope ref Value val)
    {
        size_t idx = lightScopeIndex.transitionIndex!"a <= b"(key) - 1;
        auto cond = 0 <= sizediff_t(idx);
        if (cond)
            val = _data[idx];
        return cond;
    }

    /// ditto
    bool tryGetPrev(Index, Value)(auto ref scope const Index key, scope ref Value val) const
    {
        return this.lightScope.tryGetPrev(key, val);
    }

    /// ditto
    bool tryGetPrev(Index, Value)(auto ref scope const Index key, scope ref Value val) immutable
    {
        return this.lightScope.tryGetPrev(key, val);
    }

    /++
    Tries to get the last value, such that `key_i <= key`.
    Updates `key` with `key_i`.

    Returns: `true` on success.
    +/
    bool tryGetPrevUpdateKey(Index, Value)(scope ref Index key, scope ref Value val) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex!"a <= b"(key) - 1;
        auto cond = 0 <= sizediff_t(idx);
        if (cond)
        {
            key = _index[idx];
            val = _data[idx];
        }
        return cond;
    }

    /// ditto
    bool tryGetPrevUpdateKey(Index, Value)(scope ref Index key, scope ref Value val) const
    {
        return this.lightScope.tryGetPrevUpdateKey(key, val);
    }

    /// ditto
    bool tryGetPrevUpdateKey(Index, Value)(scope ref Index key, scope ref Value val) immutable
    {
        return this.lightScope.tryGetPrevUpdateKey(key, val);
    }

    /++
    Tries to get the first value, such that `lowerBound <= key_i <= upperBound`.

    Returns: `true` on success.
    +/
    bool tryGetFirst(Index, Value)(auto ref scope const Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(lowerBound);
        auto cond = idx < _data._lengths[0] && _index[idx] <= upperBound;
        if (cond)
            val = _data[idx];
        return cond;
    }

    /// ditto
    bool tryGetFirst(Index, Value)(Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) const
    {
        return this.lightScope.tryGetFirst(lowerBound, upperBound, val);
    }

    /// ditto
    bool tryGetFirst(Index, Value)(Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) immutable
    {
        return this.lightScope.tryGetFirst(lowerBound, upperBound, val);
    }

    /++
    Tries to get the first value, such that `lowerBound <= key_i <= upperBound`.
    Updates `lowerBound` with `key_i`.

    Returns: `true` on success.
    +/
    bool tryGetFirstUpdateLower(Index, Value)(ref Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex(lowerBound);
        auto cond = idx < _data._lengths[0] && _index[idx] <= upperBound;
        if (cond)
        {
            lowerBound = _index[idx];
            val = _data[idx];
        }
        return cond;
    }

    /// ditto
    bool tryGetFirstUpdateLower(Index, Value)(ref Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) const
    {
        return this.lightScope.tryGetFirstUpdateLower(lowerBound, upperBound, val);
    }

    /// ditto
    bool tryGetFirstUpdateLower(Index, Value)(ref Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) immutable
    {
        return this.lightScope.tryGetFirstUpdateLower(lowerBound, upperBound, val);
    }

    /++
    Tries to get the last value, such that `lowerBound <= key_i <= upperBound`.

    Returns: `true` on success.
    +/
    bool tryGetLast(Index, Value)(Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex!"a <= b"(upperBound) - 1;
        auto cond = 0 <= sizediff_t(idx) && _index[idx] >= lowerBound;
        if (cond)
            val = _data[idx];
        return cond;
    }

    /// ditto
    bool tryGetLast(Index, Value)(Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) const
    {
        return this.lightScope.tryGetLast(lowerBound, upperBound, val);
    }

    /// ditto
    bool tryGetLast(Index, Value)(Index lowerBound, auto ref scope const Index upperBound, scope ref Value val) immutable
    {
        return this.lightScope.tryGetLast(lowerBound, upperBound, val);
    }

    /++
    Tries to get the last value, such that `lowerBound <= key_i <= upperBound`.
    Updates `upperBound` with `key_i`.

    Returns: `true` on success.
    +/
    bool tryGetLastUpdateKey(Index, Value)(Index lowerBound, ref Index upperBound, scope ref Value val) @trusted
    {
        size_t idx = lightScopeIndex.transitionIndex!"a <= b"(upperBound) - 1;
        auto cond = 0 <= sizediff_t(idx) && _index[idx] >= lowerBound;
        if (cond)
        {
            upperBound = _index[idx];
            val = _data[idx];
        }
        return cond;
    }

    /// ditto
    bool tryGetLastUpdateKey(Index, Value)(Index lowerBound, ref Index upperBound, scope ref Value val) const
    {
        return this.lightScope.tryGetLastUpdateKey(lowerBound, upperBound, val);
    }

    /// ditto
    bool tryGetLastUpdateKey(Index, Value)(Index lowerBound, ref Index upperBound, scope ref Value val) immutable
    {
        return this.lightScope.tryGetLastUpdateKey(lowerBound, upperBound, val);
    }

    /++
    Returns:
        1D Slice with creared with $(NDSLICE topology, zip) ([0] - key, [1] - value).
    See_also:
        $(NDSLICE topology, map) uses multiargument lambdas to handle zipped slices.
    +/
    auto asSlice()() @property
    {
        import mir.ndslice.topology: zip, map, ipack;
        static if (N == 1)
            return index.zip(data);
        else
            return index.zip(data.ipack!1.map!"a");
    }

    /// ditto
    auto asSlice()() const @property
    {
        return opIndex.asSlice;
    }

    /// ditto
    auto asSlice()() immutable @property
    {
        return opIndex.asSlice;
    }

    /// ndslice-like primitives
    bool empty(size_t dimension = 0)() const @property
        if (dimension < N)
    {
        return !length!dimension;
    }

    /// ditto
    size_t length(size_t dimension = 0)() const @property
        if (dimension < N)
    {
        return _data.length!dimension;
    }

    /// ditto
    auto front(size_t dimension = 0)() @property
        if (dimension < N)
    {
        assert(!empty!dimension);
        static if (dimension)
        {
            return index.series(data.front!dimension);
        }
        else
        {
            return index.front.observation(data.front);
        }
    }

    /// ditto
    auto back(size_t dimension = 0)() @property
        if (dimension < N)
    {
        assert(!empty!dimension);
        static if (dimension)
        {
            return index.series(_data.back!dimension);
        }
        else
        {
            return index.back.observation(_data.back);
        }
    }

    /// ditto
    void popFront(size_t dimension = 0)() @trusted
        if (dimension < N)
    {
        assert(!empty!dimension);
        static if (dimension == 0)
            _index++;
        _data.popFront!dimension;
    }

    /// ditto
    void popBack(size_t dimension = 0)()
        if (dimension < N)
    {
        assert(!empty!dimension);
        _data.popBack!dimension;
    }

    /// ditto
    void popFrontExactly(size_t dimension = 0)(size_t n) @trusted
        if (dimension < N)
    {
        assert(length!dimension >= n);
        static if (dimension == 0)
            _index += n;
        _data.popFrontExactly!dimension(n);
    }

    /// ditto
    void popBackExactly(size_t dimension = 0)(size_t n)
        if (dimension < N)
    {
        assert(length!dimension >= n);
        _data.popBackExactly!dimension(n);
    }

    /// ditto
    void popFrontN(size_t dimension = 0)(size_t n)
        if (dimension < N)
    {
        auto len = length!dimension;
        n = n <= len ? n : len;
        popFrontExactly!dimension(n);
    }

    /// ditto
    void popBackN(size_t dimension = 0)(size_t n)
        if (dimension < N)
    {
        auto len = length!dimension;
        n = n <= len ? n : len;
        popBackExactly!dimension(n);
    }

    /// ditto
    Slice!(IotaIterator!size_t) opSlice(size_t dimension = 0)(size_t i, size_t j) const
        if (dimension < N)
    in
    {
        assert(i <= j,
            "Series.opSlice!" ~ dimension.stringof ~ ": the left opSlice boundary must be less than or equal to the right bound.");
        enum errorMsg = ": difference between the right and the left bounds"
                        ~ " must be less than or equal to the length of the given dimension.";
        assert(j - i <= _data._lengths[dimension],
              "Series.opSlice!" ~ dimension.stringof ~ errorMsg);
    }
    body
    {
        return typeof(return)(j - i, typeof(return).Iterator(i));
    }

    /// ditto
    size_t opDollar(size_t dimension = 0)() const
    {
        return _data.opDollar!dimension;
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices)
        if (allSatisfy!(templateOr!(is_Slice, isIndex), Slices))
    {
        static if (Slices.length == 0)
        {
            return this;
        }
        else
        static if (is_Slice!(Slices[0]))
        {
            return index[slices[0]].series(data[slices]);
        }
        else
        {
            return index[slices[0]].observation(data[slices]);
        }
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices) const
        if (allSatisfy!(templateOr!(is_Slice, isIndex), Slices))
    {
        return lightConst.opIndex(slices);
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices) immutable
        if (allSatisfy!(templateOr!(is_Slice, isIndex), Slices))
    {
        return lightImmutable.opIndex(slices);
    }

    ///
    ref opAssign(typeof(this) rvalue) return @trusted
    {
        import mir.utility: swap;
        this._data._structure = rvalue._data._structure;
        swap(this._data._iterator, rvalue._data._iterator);
        swap(this._index, rvalue._index);
        return this;
    }

    /// ditto
    ref opAssign(RIndexIterator, RIterator)(Series!(RIndexIterator, RIterator, N, kind) rvalue) return
        if (isAssignable!(IndexIterator, RIndexIterator) && isAssignable!(Iterator, RIterator))
    {
        static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
        this._data._structure = rvalue._data._structure;
        this._data._iterator = rvalue._data._iterator.move;
        this._index = rvalue._index.move;
        return this;
    }

    /// ditto
    ref opAssign(RIndexIterator, RIterator)(auto ref const Series!(RIndexIterator, RIterator, N, kind) rvalue) return
        if (isAssignable!(IndexIterator, LightConstOf!RIndexIterator) && isAssignable!(Iterator, LightConstOf!RIterator))
    {
        return this = rvalue.opIndex;
    }

    /// ditto
    ref opAssign(RIndexIterator, RIterator)(auto ref immutable Series!(RIndexIterator, RIterator, N, kind) rvalue) return
        if (isAssignable!(IndexIterator, LightImmutableOf!RIndexIterator) && isAssignable!(Iterator, LightImmutableOf!RIterator))
    {
        return this = rvalue.opIndex;
    }

    /// ditto
    ref opAssign(typeof(null)) return
    {
        return this = this.init;
    }

    /// ditto
    auto save()() @property
    {
        return this;
    }

    ///
    Series!(LightScopeOf!IndexIterator, LightScopeOf!Iterator, N, kind) lightScope()() @trusted scope return @property
    {
        return typeof(return)(lightScopeIndex, _data.lightScope);
    }

    /// ditto
    Series!(LightConstOf!(LightScopeOf!IndexIterator), LightConstOf!(LightScopeOf!Iterator), N, kind) lightScope()() @trusted scope return const @property
    {
        return typeof(return)(lightScopeIndex, _data.lightScope);
    }

    /// ditto
    Series!(LightConstOf!(LightScopeOf!IndexIterator), LightConstOf!(LightScopeOf!Iterator), N, kind) lightScope()() @trusted scope return immutable @property
    {
        return typeof(return)(lightScopeIndex, _data.lightScope);
    }

    ///
    Series!(LightConstOf!IndexIterator, LightConstOf!Iterator, N, kind) lightConst()() scope return const @property @trusted
    {
        return index.series(data);
    }

    ///
    Series!(LightImmutableOf!IndexIterator, LightImmutableOf!Iterator, N, kind) lightImmutable()() scope return immutable @property @trusted
    {
        return index.series(data);
    }

    ///
    auto toConst()() const @property
    {
        return index.toConst.series(data.toConst);
    }

    ///
    void toString(Writer, Spec)(auto ref Writer w, const ref Spec f) const
    {
        import std.format: formatValue, formatElement;
        import std.range: put;

        if (f.spec != 's' && f.spec != '(')
            throw new Exception("incompatible format character for Mir Series argument: %" ~ f.spec);

        enum defSpec = "%s" ~ f.keySeparator ~ "%s" ~ f.seqSeparator;
        auto fmtSpec = f.spec == '(' ? f.nested : defSpec;

        if (f.spec == 's')
            put(w, f.seqBefore);
        if (length) for (size_t i = 0;;)
        {
            auto fmt = Spec(fmtSpec);
            fmt.writeUpToNextSpec(w);
            if (f.flDash)
            {
                formatValue(w, index[i], fmt);
                fmt.writeUpToNextSpec(w);
                formatValue(w, data[i], fmt);
            }
            else
            {
                formatElement(w, index[i], fmt);
                fmt.writeUpToNextSpec(w);
                formatElement(w, data[i], fmt);
            }
            if (f.sep !is null)
            {
                fmt.writeUpToNextSpec(w);
                if (++i != length)
                    put(w, f.sep);
                else
                    break;
            }
            else
            {
                if (++i != length)
                    fmt.writeUpToNextSpec(w);
                else
                    break;
            }
        }
        if (f.spec == 's')
            put(w, f.seqAfter);
    }

    version(mir_test)
    ///
    unittest
    {
        import mir.series: series, sort;
        auto s = ["b", "a"].series([9, 8]).sort;

        import std.conv : to;
        assert(s.to!string == `["a":8, "b":9]`);

        import std.format : format;
        assert("%s".format(s) == `["a":8, "b":9]`);
        assert("%(%s %s | %)".format(s) == `"a" 8 | "b" 9`);
        assert("%-(%s,%s\n%)\n".format(s) == "a,8\nb,9\n");
    }
}

/// ditto
alias Series = mir_series;

/// 1-dimensional data
@safe pure version(mir_test) unittest
{
    auto index = [1, 2, 3, 4];
    auto data = [2.1, 3.4, 5.6, 7.8];
    auto series = index.series(data);
    const cseries = series;

    assert(series.contains(2));
    assert( ()@trusted{ return (2 in series) is &data[1]; }() );

    assert(!series.contains(5));
    assert( ()@trusted{ return (5 in series) is null; }() );

    assert(series.lowerBound(2) == series[0 .. 1]);
    assert(series.upperBound(2) == series[2 .. $]);

    assert(cseries.lowerBound(2) == cseries[0 .. 1]);
    assert(cseries.upperBound(2) == cseries[2 .. $]);

    // slicing type deduction for const / immutable series
    static assert(is(typeof(series[]) == 
        Series!(int*, double*)));
    static assert(is(typeof(cseries[]) == 
        Series!(const(int)*, const(double)*)));
    static assert(is(typeof((cast(immutable) series)[]) == 
        Series!(immutable(int)*, immutable(double)*)));

    /// slicing
    auto seriesSlice  = series[1 .. $ - 1];
    assert(seriesSlice.index == index[1 .. $ - 1]);
    assert(seriesSlice.data == data[1 .. $ - 1]);
    static assert(is(typeof(series) == typeof(seriesSlice)));

    /// indexing
    assert(series[1] == observation(2, 3.4));

    /// range primitives
    assert(series.length == 4);
    assert(series.front == observation(1, 2.1));

    series.popFront;
    assert(series.front == observation(2, 3.4));

    series.popBackN(10);
    assert(series.empty);
}

/// 2-dimensional data
@safe pure version(mir_test) unittest
{
    import std.datetime: Date;
    import mir.ndslice.topology: canonical, iota;

    size_t row_length = 5;

    auto index = [
        Date(2017, 01, 01),
        Date(2017, 02, 01),
        Date(2017, 03, 01),
        Date(2017, 04, 01)];

    //  1,  2,  3,  4,  5
    //  6,  7,  8,  9, 10
    // 11, 12, 13, 14, 15
    // 16, 17, 18, 19, 20
    auto data = iota!int([index.length, row_length], 1);

    // canonical and universal ndslices are more flexible then contiguous
    auto series = index.series(data.canonical);

    /// slicing
    auto seriesSlice  = series[1 .. $ - 1, 2 .. 4];
    assert(seriesSlice.index == index[1 .. $ - 1]);
    assert(seriesSlice.data == data[1 .. $ - 1, 2 .. 4]);

    static if (kindOf!(typeof(series.data)) != Contiguous)
        static assert(is(typeof(series) == typeof(seriesSlice)));

    /// indexing
    assert(series[1, 4] == observation(Date(2017, 02, 01), 10));
    assert(series[2] == observation(Date(2017, 03, 01), iota!int([row_length], 11)));

    /// range primitives
    assert(series.length == 4);
    assert(series.length!1 == 5);

    series.popFront!1;
    assert(series.length!1 == 4);
}

/// Construct from null
@safe pure nothrow @nogc version(mir_test) unittest
{
    import mir.series;
    alias Map = Series!(string*, double*);
    Map a = null;
    auto b = Map(null);
    assert(a.empty);
    assert(b.empty);

    auto fun(Map a = null)
    {
        
    }
}

/++
Convenient function for $(LREF Series) construction.
See_also: $(LREF assocArray)
Attention:
    This overloads do not sort the data.
    User should call $(LREF directly) if index was not sorted.
+/
auto series(IndexIterator, Iterator, size_t N, SliceKind kind)
    (
        Slice!IndexIterator index,
        Slice!(Iterator, N, kind) data,
    )
{
    assert(index.length == data.length);
    return Series!(IndexIterator, Iterator, N, kind)(index, data);
}

/// ditto
auto series(Index, Data)(Index[] index, Data[] data)
{
    assert(index.length == data.length);
    return .series(index.sliced, data.sliced);
}

/// ditto
auto series(IndexIterator, Data)(Slice!IndexIterator index, Data[] data)
{
    assert(index.length == data.length);
    return .series(index, data.sliced);
}

/// ditto
auto series(Index, Iterator, size_t N, SliceKind kind)(Index[] index, Slice!(Iterator, N, kind) data)
{
    assert(index.length == data.length);
    return .series(index.sliced, data);
}

/**
Constructs a GC-allocated series from an associative array.
Performs exactly two allocations.

Params:
    aa = associative array or a pointer to associative array
Returns:
    sorted GC-allocated series.
See_also: $(LREF assocArray)
*/
Series!(K*, V*) series(RK, RV, K = RK, V = RV)(RV[RK] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    import mir.conv: to;
    const size_t length = aa.length;
    alias R = typeof(return);
    if (__ctfe)
    {
        K[] keys;
        V[] values;
        foreach(ref kv; aa.byKeyValue)
        {
            keys ~= kv.key.to!K;
            values ~= kv.value.to!V;
        }
        auto ret = series(keys, values);
        .sort((()@trusted=>cast(Series!(Unqual!K*, Unqual!V*))ret)());
        static if (is(typeof(ret) == typeof(return)))
            return ret;
        else
            return ()@trusted{ return *cast(R*) &ret; }();
    }
    import mir.ndslice.allocation: uninitSlice;
    Series!(Unqual!K*, Unqual!V*) ret = series(length.uninitSlice!(Unqual!K), length.uninitSlice!(Unqual!V));
    auto it = ret;
    foreach(ref kv; aa.byKeyValue)
    {
        import mir.conv: emplaceRef;
        emplaceRef!K(it.index.front, kv.key.to!K);
        emplaceRef!V(it._data.front, kv.value.to!V);
        it.popFront;
    }
    .sort(ret);
    static if (is(typeof(ret) == typeof(return)))
        return ret;
    else
        return ()@trusted{ return *cast(R*) &ret; }();
}

/// ditto
Series!(RK*, RV*) series(K, V, RK = const K, RV = const V)(const V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return .series!(K, V, RK, RV)((()@trusted => cast(V[K]) aa)());
}

/// ditto
Series!(RK*, RV*)  series( K, V, RK = immutable K, RV = immutable V)(immutable V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return .series!(K, V, RK, RV)((()@trusted => cast(V[K]) aa)());
}

/// ditto
auto series(K, V)(V[K]* aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return series(*a);
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto s = [1: 1.5, 3: 3.3, 2: 20.9].series;
    assert(s.index == [1, 2, 3]);
    assert(s.data == [1.5, 20.9, 3.3]);
    assert(s.data[s.findIndex(2)] == 20.9);
}

pure nothrow version(mir_test) unittest
{
    immutable aa = [1: 1.5, 3: 3.3, 2: 2.9];
    auto s = aa.series;
    s = cast() s;
    s = cast(const) s;
    s = cast(immutable) s;
    s = s;
    assert(s.index == [1, 2, 3]);
    assert(s.data == [1.5, 2.9, 3.3]);
    assert(s.data[s.findIndex(2)] == 2.9);
}


/**
Constructs a RC-allocated series from an associative array.
Performs exactly two allocations.

Params:
    aa = associative array or a pointer to associative array
Returns:
    sorted RC-allocated series.
See_also: $(LREF assocArray)
*/
auto rcseries(RK, RV, K = RK, V = RV)(RV[RK] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    import mir.rc.array;
    import mir.conv: to;
    alias R = Series!(RCI!K, RCI!V);
    const size_t length = aa.length;
    auto ret = series(length.mininitRcarray!(Unqual!K).asSlice, length.mininitRcarray!(Unqual!V).asSlice);
    auto it = ret.lightScope;
    foreach(ref kv; aa.byKeyValue)
    {
        import mir.conv: emplaceRef;
        emplaceRef!K(it.lightScopeIndex.front, kv.key.to!K);
        emplaceRef!V(it._data.front, kv.value.to!V);
        it.popFront;
    }
    static if (__VERSION__ >= 2085) import core.lifetime: move; else import std.algorithm.mutation: move; 
    .sort(ret.lightScope);
    static if (is(typeof(ret) == R))
        return ret;
    else
        return ()@trusted{ return (*cast(R*) &ret); }();
}

/// ditto
auto rcseries(K, V, RK = const K, RV = const V)(const V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return .rcseries!(K, V, RK, RV)((()@trusted => cast(V[K]) aa)());
}

/// ditto
auto  rcseries( K, V, RK = immutable K, RV = immutable V)(immutable V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init)))
{
    return .rcseries!(K, V, RK, RV)((()@trusted => cast(V[K]) aa)());
}

/// ditto
auto rcseries(K, V)(V[K]* aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return rcseries(*a);
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto s = [1: 1.5, 3: 3.3, 2: 20.9].rcseries;
    assert(s.index == [1, 2, 3]);
    assert(s.data == [1.5, 20.9, 3.3]);
    assert(s.data[s.findIndex(2)] == 20.9);
}

// pure nothrow
version(mir_test) unittest
{
    import mir.rc.array;
    immutable aa = [1: 1.5, 3: 3.3, 2: 2.9];
    auto s = aa.rcseries;
    Series!(RCI!(const int), RCI!(const double)) c;
    s = cast() s;
    c = s;
    s = cast(const) s;
    s = cast(immutable) s;
    s = s;
    assert(s.index == [1, 2, 3]);
    assert(s.data == [1.5, 2.9, 3.3]);
    assert(s.data[s.findIndex(2)] == 2.9);
}

/++
Constructs a manually allocated series from an associative array.
Performs exactly two allocations.

Params:
    aa == associative array or a pointer to associative array
Returns:
    sorted manually allocated series.
+/
Series!(K*, V*) makeSeries(Allocator, K, V)(auto ref Allocator allocator, V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init)))
{
    import mir.ndslice.allocation: makeUninitSlice;
    import mir.conv: emplaceRef;

    immutable size_t length = aa.length;

    auto ret = series(
        allocator.makeUninitSlice!(Unqual!K)(length),
        allocator.makeUninitSlice!(Unqual!V)(length));

    auto it = ret;
    foreach(ref kv; aa.byKeyValue)
    {
        it.index.front.emplaceRef!K(kv.key);
        it.data.front.emplaceRef!V(kv.value);
        it.popFront;
    }

    ret.sort;
    static if (is(typeof(ret) == typeof(return)))
        return ret;
    else
        return ()@trusted{ return cast(typeof(return)) ret; }();
}

/// ditto
Series!(K*, V*) makeSeries(Allocator, K, V)(auto ref Allocator allocator, V[K]* aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return makeSeries(allocator, *a);
}

///
pure nothrow version(mir_test) unittest
{
    import std.experimental.allocator;
    import std.experimental.allocator.building_blocks.region;

    InSituRegion!(1024) allocator;
    auto aa = [1: 1.5, 3: 3.3, 2: 2.9];

    auto s = (double[int] aa) @nogc @trusted pure nothrow {
        return allocator.makeSeries(aa);
    }(aa);

    auto indexArray = s.index.field;
    auto dataArray = s.data.field;
    
    assert(s.index == [1, 2, 3]);
    assert(s.data == [1.5, 2.9, 3.3]);
    assert(s.data[s.findIndex(2)] == 2.9);

    allocator.dispose(indexArray);
    allocator.dispose(dataArray);
}

/++
Returns a newly allocated associative array from a range of key/value tuples.

Params:
    series = index / time $(LREF Series), may not be sorted

Returns: A newly allocated associative array out of elements of the input
_series. Returns a null associative
array reference when given an empty _series.

Duplicates: Associative arrays have unique keys. If r contains duplicate keys,
then the result will contain the value of the last pair for that key in r.
+/
auto assocArray(IndexIterator, Iterator, size_t N, SliceKind kind)
    (Series!(IndexIterator, Iterator, N, kind) series)
{
    alias SK = series.Key;
    alias SV = series.Value;
    alias UK = Unqual!SK;
    alias UV = Unqual!SV;
    static if (isImplicitlyConvertible!(SK, UK))
        alias K = UK;
    else
        alias K = SK;
    static if (isImplicitlyConvertible!(SV, UV))
        alias V = UV;
    else
        alias V = SV;
    static assert(isMutable!V, "mir.series.assocArray: value type ( " ~ V.stringof ~ " ) must be mutable");

    V[K] aa;
    aa.insertOrAssign = series;
    return aa;
}

///
@safe pure version(mir_test) unittest
{
    import mir.ndslice; //iota and etc
    import mir.series;

    auto s = ["c", "a", "b"].series(3.iota!int);
    assert(s.assocArray == [
        "c": 0,
        "a": 1,
        "b": 2,
    ]);
}

/// Returns: true if `U` is a $(LREF Series);
enum isSeries(U) = is(U : Series!(IndexIterator, Iterator, N, kind), IndexIterator, Iterator, size_t N, SliceKind kind);

/++
Finds an index such that `series.index[index] == key`.

Params:
    series = series
    key = index to find in the series
Returns:
    `size_t.max` if the series does not contain the key and appropriate index otherwise.
+/
size_t findIndex(IndexIterator, Iterator, size_t N, SliceKind kind, Index)(Series!(IndexIterator, Iterator, N, kind) series, auto ref scope const Index key)
{
    auto idx = series.lightScopeIndex.transitionIndex(key);
    if (idx < series._data._lengths[0] && series.index[idx] == key)
    {
        return idx;
    }
    return size_t.max;
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto index = [1, 2, 3, 4].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = index.series(data);

    assert(series.data[series.findIndex(3)] == 5.6);
    assert(series.findIndex(0) == size_t.max);
}

/++
Finds a backward index such that `series.index[$ - backward_index] == key`.

Params:
    series = series
    key = index key to find in the series
Returns:
    `0` if the series does not contain the key and appropriate backward index otherwise.
+/
size_t find(IndexIterator, Iterator, size_t N, SliceKind kind, Index)(Series!(IndexIterator, Iterator, N, kind) series, auto ref scope const Index key)
{
    auto idx = series.lightScopeIndex.transitionIndex(key);
    auto bidx = series._data._lengths[0] - idx;
    if (bidx && series.index[idx] == key)
    {
        return bidx;
    }
    return 0;
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto index = [1, 2, 3, 4].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = index.series(data);

    if (auto bi = series.find(3))
    {
        assert(series.data[$ - bi] == 5.6);
    }
    else
    {
        assert(0);
    }

    assert(series.find(0) == 0);
}

/++
Iterates union using three functions to handle each intersection case separately.
Params:
    lfun = binary function that accepts left side key (and left side value)
    cfun = trinary function that accepts left side key, (left side value,) and right side value
    rfun = binary function that accepts right side key (and right side value)
+/
template troykaGalop(alias lfun, alias cfun, alias rfun)
{
    import std.range.primitives: isInputRange;

    /++
    Params:
        lhs = left hand series
        rhs = right hand series
    +/
    pragma(inline, false)
    void troykaGalop(
        IndexIterL, IterL, size_t LN, SliceKind lkind,
        IndexIterR, IterR, size_t RN, SliceKind rkind,
    )(
        Series!(IndexIterL, IterL, LN, lkind) lhs,
        Series!(IndexIterR, IterR, RN, rkind) rhs,
    )
    {
        if (lhs.empty)
            goto R0;
        if (rhs.empty)
            goto L1;
        for(;;)
        {
            if (lhs.index.front < rhs.index.front)
            {
                lfun(lhs.index.front, lhs.data.front);
                lhs.popFront;
                if (lhs.empty)
                    goto R1;
                continue;
            }
            else
            if (lhs.index.front > rhs.index.front)
            {
                rfun(rhs.index.front, rhs.data.front);
                rhs.popFront;
                if (rhs.empty)
                    goto L1;
                continue;
            }
            else
            {
                cfun(lhs.index.front, lhs.data.front, rhs.data.front);
                lhs.popFront;
                rhs.popFront;
                if (rhs.empty)
                    goto L0;
                if (lhs.empty)
                    goto R1;
                continue;
            }
        }

    L0:
        if (lhs.empty)
            return;
    L1:
        do
        {
            lfun(lhs.index.front, lhs.data.front);
            lhs.popFront;
        } while(!lhs.empty);
        return;

    R0:
        if (rhs.empty)
            return;
    R1:
        do
        {
            rfun(rhs.index.front, rhs.data.front);
            rhs.popFront;
        } while(!rhs.empty);
        return;
    }

    /++
    Params:
        lhs = left hand input range
        rhs = right hand input range
    +/
    pragma(inline, false)
    void troykaGalop (LeftRange, RightRange)(LeftRange lhs, RightRange rhs)
        if (isInputRange!LeftRange && isInputRange!RightRange && !isSeries!LeftRange && !isSeries!RightRange)
    {
        if (lhs.empty)
            goto R0;
        if (rhs.empty)
            goto L1;
        for(;;)
        {
            if (lhs.front < rhs.front)
            {
                lfun(lhs.front);
                lhs.popFront;
                if (lhs.empty)
                    goto R1;
                continue;
            }
            else
            if (lhs.front > rhs.front)
            {
                rfun(rhs.front);
                rhs.popFront;
                if (rhs.empty)
                    goto L1;
                continue;
            }
            else
            {
                cfun(lhs.front, rhs.front);
                lhs.popFront;
                rhs.popFront;
                if (rhs.empty)
                    goto L0;
                if (lhs.empty)
                    goto R1;
                continue;
            }
        }

    L0:
        if (lhs.empty)
            return;
    L1:
        do
        {
            lfun(lhs.front);
            lhs.popFront;
        } while(!lhs.empty);
        return;

    R0:
        if (rhs.empty)
            return;
    R1:
        do
        {
            rfun(rhs.front);
            rhs.popFront;
        } while(!rhs.empty);
        return;
    }
}

/++
Constructs union using three functions to handle each intersection case separately.
Params:
    lfun = binary function that accepts left side key and left side value
    cfun = trinary function that accepts left side key, left side value, and right side value
    rfun = binary function that accepts right side key and right side value
+/
template troykaSeries(alias lfun, alias cfun, alias rfun)
{
    /++
    Params:
        lhs = left hand series
        rhs = right hand series
    Returns:
        GC-allocated union series with length equal to $(LREF troykaLength)
    +/
    auto troykaSeries
    (
        IndexIterL, IterL, size_t LN, SliceKind lkind,
        IndexIterR, IterR, size_t RN, SliceKind rkind,
    )(
        Series!(IndexIterL, IterL, LN, lkind) lhs,
        Series!(IndexIterR, IterR, RN, rkind) rhs,
    )
    {
        alias I = CommonType!(typeof(lhs.index.front), typeof(rhs.index.front));
        alias E = CommonType!(
            typeof(lfun(lhs.index.front, lhs.data.front)),
            typeof(cfun(lhs.index.front, lhs.data.front, rhs.data.front)),
            typeof(rfun(rhs.index.front, rhs.data.front)),
        );
        alias R = Series!(I*, E*);
        alias UI = Unqual!I;
        alias UE = Unqual!E;
        const length = troykaLength(lhs.index, rhs.index);
        import mir.ndslice.allocation: uninitSlice;
        auto index = length.uninitSlice!UI;
        auto data = length.uninitSlice!UE;
        auto ret = index.series(data);
        alias algo = troykaSeriesImpl!(lfun, cfun, rfun);
        algo!(I, E)(lhs.lightScope, rhs.lightScope, ret);
        return (()@trusted => cast(R) ret)();
    }
}

///
version(mir_test) unittest
{
    import mir.ndslice;
    auto a = [1, 2, 3, 9].sliced.series(iota!int([4], 1));
    auto b = [0, 2, 4, 9].sliced.series(iota!int([4], 1) * 10.0);
    alias unionAlgorithm = troykaSeries!(
        (key, left) => left,
        (key, left, right) => left + right,
        (key, right) => -right,
    );
    auto c = unionAlgorithm(a, b);
    assert(c.index == [0, 1, 2, 3, 4, 9]);
    assert(c.data == [-10, 1, 22, 3, -30, 44]);
}

/++
Constructs union using three functions to handle each intersection case separately.
Params:
    lfun = binary function that accepts left side key and left side value
    cfun = trinary function that accepts left side key, left side value, and right side value
    rfun = binary function that accepts right side key and right side value
+/
template rcTroykaSeries(alias lfun, alias cfun, alias rfun)
{
    /++
    Params:
        lhs = left hand series
        rhs = right hand series
    Returns:
        RC-allocated union series with length equal to $(LREF troykaLength)
    +/
    auto rcTroykaSeries
    (
        IndexIterL, IterL, size_t LN, SliceKind lkind,
        IndexIterR, IterR, size_t RN, SliceKind rkind,
    )(
        auto ref Series!(IndexIterL, IterL, LN, lkind) lhs,
        auto ref Series!(IndexIterR, IterR, RN, rkind) rhs,
    )
    {
        import mir.rc.array;
        alias I = CommonType!(typeof(lhs.index.front), typeof(rhs.index.front));
        alias E = CommonType!(
            typeof(lfun(lhs.index.front, lhs.data.front)),
            typeof(cfun(lhs.index.front, lhs.data.front, rhs.data.front)),
            typeof(rfun(rhs.index.front, rhs.data.front)),
        );
        alias R = Series!(RCI!I, RCI!E);
        alias UI = Unqual!I;
        alias UE = Unqual!E;
        const length = troykaLength(lhs.index, rhs.index);
        import mir.ndslice.allocation: uninitSlice;
        auto ret = length.mininitRcarray!UI.asSlice.series(length.mininitRcarray!UE.asSlice);
        alias algo = troykaSeriesImpl!(lfun, cfun, rfun);
        algo!(I, E)(lhs.lightScope, rhs.lightScope, ret.lightScope);
        return (()@trusted => *cast(R*) &ret)();
    }
}

///
version(mir_test) unittest
{
    import mir.ndslice;
    auto a = [1, 2, 3, 9].sliced.series(iota!int([4], 1));
    auto b = [0, 2, 4, 9].sliced.series(iota!int([4], 1) * 10.0);
    alias unionAlgorithm = rcTroykaSeries!(
        (key, left) => left,
        (key, left, right) => left + right,
        (key, right) => -right,
    );
    auto c = unionAlgorithm(a, b);
    assert(c.index == [0, 1, 2, 3, 4, 9]);
    assert(c.data == [-10, 1, 22, 3, -30, 44]);
}


/++
Length for Troyka union handlers.
Params:
    lhs = left hand side series/range
    rhs = right hand side series/range
Returns: Total count of lambda function calls in $(LREF troykaGalop) union handler.
+/
size_t troykaLength(
    IndexIterL, IterL, size_t LN, SliceKind lkind,
    IndexIterR, IterR, size_t RN, SliceKind rkind,
)(
    Series!(IndexIterL, IterL, LN, lkind) lhs,
    Series!(IndexIterR, IterR, RN, rkind) rhs,
)
{
    return troykaLength(lhs.index, rhs.index);
}

/// ditto
size_t troykaLength(LeftRange, RightRange)(LeftRange lhs, RightRange rhs)
    if (!isSeries!LeftRange && !isSeries!RightRange)
{
    size_t length;
    alias counter = (scope auto ref _) => ++length;
    alias ccounter = (scope auto ref _l, scope auto ref _r) => ++length;
    troykaGalop!(counter, ccounter, counter)(lhs, rhs);
    return length;
}

///
template troykaSeriesImpl(alias lfun, alias cfun, alias rfun)
{
    ///
    void troykaSeriesImpl
    (
        I, E,
        IndexIterL, IterL, size_t LN, SliceKind lkind,
        IndexIterR, IterR, size_t RN, SliceKind rkind,
        UI, UE,
    )(
        Series!(IndexIterL, IterL, LN, lkind) lhs,
        Series!(IndexIterR, IterR, RN, rkind) rhs,
        Series!(UI*, UE*) uninitSlice,
    )
    {
        import mir.conv: emplaceRef;
        troykaGalop!(
            (auto ref key, auto ref value) {
                uninitSlice.index.front.emplaceRef!I(key);
                uninitSlice.data.front.emplaceRef!E(lfun(key, value));
                uninitSlice.popFront;
            },
            (auto ref key, auto ref lvalue, auto ref rvalue) {
                uninitSlice.index.front.emplaceRef!I(key);
                uninitSlice.data.front.emplaceRef!E(cfun(key, lvalue, rvalue));
                uninitSlice.popFront;
            },
            (auto ref key, auto ref value) {
                uninitSlice.index.front.emplaceRef!I(key);
                uninitSlice.data.front.emplaceRef!E(rfun(key, value));
                uninitSlice.popFront;
            },
            )(lhs, rhs);
        assert(uninitSlice.length == 0);
    }
}

/**
Merges multiple (time) series into one.
Makes exactly one memory allocation for two series union
and two memory allocation for three and more series union.

Params: 
    seriesTuple = variadic static array of composed of series, each series must be sorted.
Returns: sorted GC-allocated series.
See_also $(LREF Series.opBinary) $(LREF makeUnionSeries)
*/
auto unionSeries(IndexIterator, Iterator, size_t N, SliceKind kind, size_t C)(Series!(IndexIterator, Iterator, N, kind)[C] seriesTuple...)
    if (C > 1)
{
    return unionSeriesImplPrivate!false(seriesTuple);
}

///
@safe pure nothrow version(mir_test) unittest
{
    import std.datetime: Date;

    //////////////////////////////////////
    // Constructs two time-series.
    //////////////////////////////////////
    auto index0 = [1,3,4];
    auto data0 = [1.0, 3, 4];
    auto series0 = index0.series(data0);

    auto index1 = [1,2,5];
    auto data1 = [10.0, 20, 50];
    auto series1 = index1.series(data1);

    //////////////////////////////////////
    // Merges multiple series into one.
    //////////////////////////////////////
    // Order is matter.
    // The first slice has higher priority.
    auto m0 = unionSeries(series0, series1);
    auto m1 = unionSeries(series1, series0);

    assert(m0.index == m1.index);
    assert(m0.data == [ 1, 20,  3,  4, 50]);
    assert(m1.data == [10, 20,  3,  4, 50]);
}

///
@safe pure nothrow version(mir_test) unittest
{
    import std.datetime: Date;

    //////////////////////////////////////
    // Constructs three time-series.
    //////////////////////////////////////
    auto index0 = [1,3,4];
    auto data0 = [1.0, 3, 4];
    auto series0 = index0.series(data0);

    auto index1 = [1,2,5];
    auto data1 = [10.0, 20, 50];
    auto series1 = index1.series(data1);

    auto index2 = [1, 6];
    auto data2 = [100.0, 600];
    auto series2 = index2.series(data2);

    //////////////////////////////////////
    // Merges multiple series into one.
    //////////////////////////////////////
    // Order is matter.
    // The first slice has higher priority.
    auto m0 = unionSeries(series0, series1, series2);
    auto m1 = unionSeries(series1, series0, series2);
    auto m2 = unionSeries(series2, series0, series1);

    assert(m0.index == m1.index);
    assert(m0.index == m2.index);
    assert(m0.data == [  1, 20,  3,  4, 50, 600]);
    assert(m1.data == [ 10, 20,  3,  4, 50, 600]);
    assert(m2.data == [100, 20,  3,  4, 50, 600]);
}

/**
Merges multiple (time) series into one.

Params:
    allocator = memory allocator
    seriesTuple = variadic static array of composed of series.
Returns: sorted manually allocated series.
See_also $(LREF unionSeries)
*/
auto makeUnionSeries(IndexIterator, Iterator, size_t N, SliceKind kind, size_t C, Allocator)(auto ref Allocator allocator, Series!(IndexIterator, Iterator, N, kind)[C] seriesTuple...)
    if (C > 1)
{
    return unionSeriesImplPrivate!false(seriesTuple, allocator);
}

///
@system pure nothrow version(mir_test) unittest
{
    import std.experimental.allocator;
    import std.experimental.allocator.building_blocks.region;

    //////////////////////////////////////
    // Constructs two time-series.
    //////////////////////////////////////
    auto index0 = [1,3,4];

    auto data0 = [1.0, 3, 4];
    auto series0 = index0.series(data0);

    auto index1 = [1,2,5];

    auto data1 = [10.0, 20, 50];
    auto series1 = index1.series(data1);

    //////////////////////////////////////
    // Merges multiple series into one.
    //////////////////////////////////////

    InSituRegion!(1024) allocator;

    auto m0 = allocator.makeUnionSeries(series0, series1);
    auto m1 = allocator.makeUnionSeries(series1, series0); // order is matter

    assert(m0.index == m1.index);
    assert(m0.data == [ 1, 20,  3,  4, 50]);
    assert(m1.data == [10, 20,  3,  4, 50]);

    /// series should have the same sizes as after allocation
    allocator.dispose(m0.index.field);
    allocator.dispose(m0.data.field);
    allocator.dispose(m1.index.field);
    allocator.dispose(m1.data.field);
}

/**
Merges multiple (time) series into one.

Params:
    seriesTuple = variadic static array of composed of series.
Returns: sorted manually allocated series.
See_also $(LREF unionSeries)
*/
auto rcUnionSeries(IndexIterator, Iterator, size_t N, SliceKind kind, size_t C)(Series!(IndexIterator, Iterator, N, kind)[C] seriesTuple...)
    if (C > 1)
{
    return unionSeriesImplPrivate!true(seriesTuple);
}

///
@safe pure nothrow version(mir_test) unittest
{
    import mir.rc.array;

    //////////////////////////////////////
    // Constructs two time-series.
    //////////////////////////////////////
    auto index0 = [1,3,4];

    auto data0 = [1.0, 3, 4];
    auto series0 = index0.series(data0);

    auto index1 = [1,2,5];

    auto data1 = [10.0, 20, 50];
    auto series1 = index1.series(data1);

    //////////////////////////////////////
    // Merges multiple series into one.
    //////////////////////////////////////

    Series!(RCI!int, RCI!double) m0 = rcUnionSeries(series0, series1);
    Series!(RCI!int, RCI!double) m1 = rcUnionSeries(series1, series0); // order is matter

    assert(m0.index == m1.index);
    assert(m0.data == [ 1, 20,  3,  4, 50]);
    assert(m1.data == [10, 20,  3,  4, 50]);
}

/**
Initialize preallocated series using union of multiple (time) series.
Doesn't make any allocations.

Params: 
    seriesTuple = dynamic array composed of series.
    uninitSeries = uninitialized series with exactly required length.
*/
pragma(inline, false)
auto unionSeriesImpl(I, E,
    IndexIterator, Iterator, size_t N, SliceKind kind, UI, UE)(
    Series!(IndexIterator, Iterator, N, kind)[] seriesTuple,
    Series!(UI*, UE*, N) uninitSeries,
    )
{
    import mir.conv: emplaceRef;
    import mir.algorithm.setops: multiwayUnion;

    enum N = N;
    alias I = DeepElementType!(typeof(seriesTuple[0].index));
    alias E = DeepElementType!(typeof(seriesTuple[0]._data));

    if(uninitSeries.length)
    {
        auto u = seriesTuple.multiwayUnion!"a.index < b.index";
        do
        {
            auto obs = u.front;
            emplaceRef!I(uninitSeries.index.front, obs.index);
            static if (N == 1)
                emplaceRef!E(uninitSeries._data.front, obs.data);
            else
                each!(emplaceRef!E)(uninitSeries._data.front, obs.data);
            u.popFront;
            uninitSeries.popFront;
        }
        while(uninitSeries.length);
    }
}

private auto unionSeriesImplPrivate(bool rc, IndexIterator, Iterator, size_t N, SliceKind kind, size_t C, Allocator...)(ref Series!(IndexIterator, Iterator, N, kind)[C] seriesTuple, ref Allocator allocator)
    if (C > 1 && Allocator.length <= 1)
{
    import mir.algorithm.setops: unionLength;
    import mir.ndslice.topology: iota;
    import mir.internal.utility: Iota;
    import mir.ndslice.allocation: uninitSlice, makeUninitSlice;
    static if (rc)
        import mir.rc.array;

    Slice!IndexIterator[C] indeces;
    foreach (i; Iota!C)
        indeces[i] = seriesTuple[i].index;

    immutable len = indeces[].unionLength; 

    alias I = typeof(seriesTuple[0].index.front);
    alias E = typeof(seriesTuple[0].data.front);
    static if (rc)
        alias R = Series!(RCI!I, RCI!E, N);
    else
        alias R = Series!(I*, E*, N);
    alias UI = Unqual!I;
    alias UE = Unqual!E;

    static if (N > 1)
    {
        auto shape = seriesTuple[0]._data._lengths;
        shape[0] = len;

        foreach (ref sl; seriesTuple[1 .. $])
            foreach (i; Iota!(1, N))
                if (seriesTuple._data[0]._lengths[i] != sl._data._lengths[i])
                    assert(0, "shapes mismatch");
    }
    else
    {
        alias shape = len;
    }

    static if (rc == false)
    {
        static if (Allocator.length)
            auto ret = (()@trusted => allocator[0].makeUninitSlice!UI(len).series(allocator[0].makeUninitSlice!UE(shape)))();
        else
            auto ret = (()@trusted => len.uninitSlice!UI.series(shape.uninitSlice!UE))();
    }
    else
    {
        static if (Allocator.length)
            static assert(0, "rcUnionSeries with allocators is not implemented.");
        else
            auto ret = (()@trusted =>
                len
                .mininitRcarray!UI
                .asSlice
                .series(
                    shape
                    .iota
                    .elementCount
                    .mininitRcarray!UE
                    .asSlice
                    .sliced(shape)))();
    }

    static if (C == 2) // fast path
    {
        alias algo = troykaSeriesImpl!(
            ref (scope ref key, scope return ref left) => left,
            ref (scope ref key, scope return ref left, scope return ref right) => left,
            ref (scope ref key, scope return ref right) => right,
        );
        algo!(I, E)(seriesTuple[0], seriesTuple[1], ret.lightScope);
    }
    else
    {
        unionSeriesImpl!(I, E)(seriesTuple, ret.lightScope);
    }

    return () @trusted {return *cast(R*) &ret; }();
}

/**
Inserts or assigns a series to the associative array `aa`.
Params:
    aa = associative array
    series = series
Returns:
    associative array 
*/
ref V[K] insertOrAssign(V, K, IndexIterator, Iterator, size_t N, SliceKind kind)(return ref V[K] aa, auto ref Series!(IndexIterator, Iterator, N, kind) series) @property
{
    auto s = series.lightScope;
    foreach (i; 0 .. s.length)
    {
        aa[s.index[i]] = s.data[i];
    }
    return aa;
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto a = [1: 3.0, 4: 2.0];
    auto s = series([1, 2, 3], [10, 20, 30]);
    a.insertOrAssign = s;
    assert(a.series == series([1, 2, 3, 4], [10.0, 20, 30, 2]));
}

/**
Inserts a series to the associative array `aa`.
Params:
    aa = associative array
    series = series
Returns:
    associative array 
*/
ref V[K] insert(V, K, IndexIterator, Iterator, size_t N, SliceKind kind)(return ref V[K] aa, auto ref Series!(IndexIterator, Iterator, N, kind) series) @property
{
    auto s = series.lightScope;
    foreach (i; 0 .. s.length)
    {
        if (s.index[i] in aa)
            continue;
        aa[s.index[i]] = s.data[i];
    }
    return aa;
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto a = [1: 3.0, 4: 2.0];
    auto s = series([1, 2, 3], [10, 20, 30]);
    a.insert = s;
    assert(a.series == series([1, 2, 3, 4], [3.0, 20, 30, 2]));
}


static if (__VERSION__ < 2078)
//////////////////// OBJECT.d
{

private:

extern (C)
{
    // from druntime/src/rt/aaA.d

    // size_t _aaLen(in void* p) pure nothrow @nogc;
    private void* _aaGetY(void** paa, const TypeInfo_AssociativeArray ti, in size_t valuesize, in void* pkey) pure nothrow;
    // inout(void)* _aaGetRvalueX(inout void* p, in TypeInfo keyti, in size_t valuesize, in void* pkey);
    inout(void)[] _aaValues(inout void* p, in size_t keysize, in size_t valuesize, const TypeInfo tiValArray) pure nothrow;
    inout(void)[] _aaKeys(inout void* p, in size_t keysize, const TypeInfo tiKeyArray) pure nothrow;
    void* _aaRehash(void** pp, in TypeInfo keyti) pure nothrow;
    void _aaClear(void* p) pure nothrow;

    // alias _dg_t = extern(D) int delegate(void*);
    // int _aaApply(void* aa, size_t keysize, _dg_t dg);

    // alias _dg2_t = extern(D) int delegate(void*, void*);
    // int _aaApply2(void* aa, size_t keysize, _dg2_t dg);

    // private struct AARange { void* impl; size_t idx; }
    alias AARange = ReturnType!(object._aaRange);
    AARange _aaRange(void* aa) pure nothrow @nogc @safe;
    bool _aaRangeEmpty(AARange r) pure nothrow @nogc @safe;
    void* _aaRangeFrontKey(AARange r) pure nothrow @nogc @safe;
    void* _aaRangeFrontValue(AARange r) pure nothrow @nogc @safe;
    void _aaRangePopFront(ref AARange r) pure nothrow @nogc @safe;

}

auto byKeyValue(T : V[K], K, V)(T aa) pure nothrow @nogc @safe
{
    import core.internal.traits : substInout;

    static struct Result
    {
        AARange r;

    pure nothrow @nogc:
        @property bool empty() @safe { return _aaRangeEmpty(r); }
        @property auto front()
        {
            static struct Pair
            {
                // We save the pointers here so that the Pair we return
                // won't mutate when Result.popFront is called afterwards.
                private void* keyp;
                private void* valp;

                @property ref key() inout
                {
                    auto p = (() @trusted => cast(substInout!K*) keyp) ();
                    return *p;
                };
                @property ref value() inout
                {
                    auto p = (() @trusted => cast(substInout!V*) valp) ();
                    return *p;
                };
            }
            return Pair(_aaRangeFrontKey(r),
                        _aaRangeFrontValue(r));
        }
        void popFront() @safe { return _aaRangePopFront(r); }
        @property Result save() { return this; }
    }

    return Result(_aaToRange(aa));
}

auto byKeyValue(T : V[K], K, V)(T* aa) pure nothrow @nogc
{
    return (*aa).byKeyValue();
}

// this should never be made public.
private AARange _aaToRange(T: V[K], K, V)(ref T aa) pure nothrow @nogc @safe
{
    // ensure we are dealing with a genuine AA.
    static if (is(const(V[K]) == const(T)))
        alias realAA = aa;
    else
        const(V[K]) realAA = aa;
    return _aaRange(() @trusted { return cast(void*)realAA; } ());
}

}
