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
import mir.qualifier;
import std.traits;

/++
See_also: $(LREF sort), $(LREF unionSeries), $(LREF troykaSeries), $(LREF troykaGalop).
+/
@safe version(mir_test) unittest
{
    import mir.ndslice;
    import mir.series;

    import mir.array.allocation: array;
    import mir.algorithm.setops: multiwayUnion;

    import std.datetime: Date;
    import std.algorithm.mutation: move;
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

    series[0 .. $, 0][] = series0; // fill first column
    series[0 .. $, 1][] = series1; // fill second column

    assert(data == [
        [1, 10],
        [0, 20],
        [3,  0],
        [4,  0],
        [0, 50]]);
}

import mir.ndslice.slice;
import mir.ndslice.internal: _Slice, is_Slice, isIndex;
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
    return Observation!(Index, Data)(index, data);
}

/++
Convinient alias for 1D Contiguous $(LREF Series).
+/
alias SeriesMap(K, V) = Series!(K*, V*);

///
version(mir_test) unittest
{
    import std.traits;
    import mir.series;

    static assert (is(SeriesMap!(string, double) == Series!(string*, double*)));

    /// LHS, RHS
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
struct mir_series(IndexIterator, Iterator, size_t N = 1, SliceKind kind = Contiguous)
{
    import std.range: SearchPolicy, assumeSorted;

    private enum doUnittest = is(typeof(this) == Series!(int*, double*));

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
    this()(typeof(null))
    {
        _data = _data.init;
        _index = _index.init;
    }

    ///
    bool opEquals(RIndexIterator, RIterator, size_t RN, SliceKind rkind, )(Series!(RIndexIterator, RIterator, RN, rkind) rhs) const
    {
        return this.index == rhs.index && this.data == rhs.data;
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
        return unionSeries(this, rhs);
    }

    /// ditto
    auto opBinary(string op : "~")(const typeof(this) rhs) const
    {
        return unionSeries(this[], rhs[]);
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
        r = rvalue index-series
    +/
    void opIndexOpAssign(string op, IndexIterator_, Iterator_, size_t N_, SliceKind kind_)
        (Series!(IndexIterator_, Iterator_, N_, kind_) r)
    {
        auto l = this;
        if (r.empty)
            return;
        if (l.empty)
            return;
        Unqual!(typeof(r.index.front)) rf = r.index.front;
        Unqual!(typeof(l.index.front)) lf = l.index.front;
        goto Begin;
    R:
        r.popFront;
        if (r.empty)
            goto End;
        rf = r.index.front;
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
        rf = r.index.front;
    L:
        l.popFront;
        if (l.empty)
            goto End;
        lf = l.index.front;

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
    `t < moment` is true for all `t`.
    The search schedule and its complexity are documented in `std.range.SearchPolicy`.
    +/
    auto lowerBound(SearchPolicy sp = SearchPolicy.binarySearch, Index)(Index moment)
    {
        return this[0 .. index.assumeSorted.lowerBound!sp(moment).length];
    }

    /// ditto
    auto lowerBound(SearchPolicy sp = SearchPolicy.binarySearch, Index)(Index moment) const
    {
        return this[0 .. index.assumeSorted.lowerBound!sp(moment).length];
    }


    /++
    This function uses a search with policy sp to find the largest left subrange on which 
    `t > moment` is true for all `t`.
    The search schedule and its complexity are documented in `std.range.SearchPolicy`.
    +/
    auto upperBound(SearchPolicy sp = SearchPolicy.binarySearch, Index)(Index moment)
    {
        return this[$ - index.assumeSorted.upperBound!sp(moment).length .. $];
    }

    /// ditto
    auto upperBound(SearchPolicy sp = SearchPolicy.binarySearch, Index)(Index moment) const
    {
        return this[$ - index.assumeSorted.upperBound!sp(moment).length .. $];
    }

    /**
    Gets data for the index.
    Params:
        moment = index
        _default = default value is returned if the series does not contains the index.
    Returns:
        data that corresponds to the index or default value.
    */
    ref get(Index, Value)(Index moment, return ref Value _default)
        if (!is(Value : const(Exception)))
    {
        size_t idx = index.assumeSorted.lowerBound(moment).length;
        return idx < _data._lengths[0] && index[idx] == moment ? data[idx] : _default;
    }

    /// ditto
    ref get(Index, Value)(Index moment, return ref Value _default) const
        if (!is(Value : const(Exception)))
    {
        return this[].get(moment, _default);
    }

    /// ditto
    ref get(Index, Value)(Index moment, return ref Value _default) immutable
        if (!is(Value : const(Exception)))
    {
        return this[].get(moment, _default);
    }

    auto get(Index, Value)(Index moment, Value _default)
        if (!is(Value : const(Exception)))
    {
        size_t idx = index.assumeSorted.lowerBound(moment).length;
        return idx < _data._lengths[0] && index[idx] == moment ? data[idx] : _default;
    }

    /// ditto
    auto get(Index, Value)(Index moment, Value _default) const
        if (!is(Value : const(Exception)))
    {
        import mir.functional: forward;
        return this[].get(moment, forward!_default);
    }

    /// ditto
    auto get(Index, Value)(Index moment, Value _default) immutable
        if (!is(Value : const(Exception)))
    {
        import mir.functional: forward;
        return this[].get(moment, forward!_default);
    }

    /**
    Gets data for the index.
    Params:
        moment = index
        exc = (lazy, optional) exception to throw if the series does not contains the index.
    Returns: data that corresponds to the index.
    Throws:
        Exception if the series does not contains the index.
    See_also: $(LREF Series.getVerbose), $(LREF Series.tryGet)
    */
    auto ref get(Index)(Index moment)
    {
        return this.get(moment, defaultExc!());
    }

    /// ditto
    auto ref get(Index)(Index moment, lazy const Exception exc)
    {
        size_t idx = index.assumeSorted.lowerBound(moment).length;
        if (idx < _data._lengths[0] && index[idx] == moment)
        {
            return data[idx];
        }
        throw exc;
    }

    /// ditto
    auto ref get(Index)(Index moment) const
    {
        return this[].get(moment);
    }

    /// ditto
    auto ref get(Index)(Index moment, lazy const Exception exc) const
    {
        return this[].get(moment, exc);
    }


    /// ditto
    auto ref get(Index)(Index moment) immutable
    {
        return this[].get(moment);
    }

    /// ditto
    auto ref get(Index)(Index moment, lazy const Exception exc) immutable
    {
        return this[].get(moment, exc);
    }

    /**
    Gets data for the index (verbose exception).
    Params:
        moment = index
    Returns: data that corresponds to the index.
    Throws:
        Detailed exception if the series does not contains the index.
    See_also: $(LREF Series.get), $(LREF Series.tryGet)
    */
    auto ref getVerbose(Index)(Index moment, string file = __FILE__, int line = __LINE__)
    {
        import std.format: format;
        return this.get(moment, new Exception(format("%s %s key", defaultMsg!(), moment), file, line));
    }

    /// ditto
    auto ref getVerbose(Index)(Index moment, string file = __FILE__, int line = __LINE__) const
    {
        return this[].getVerbose(moment, file, line);
    }

    /// ditto
    auto ref getVerbose(Index)(Index moment, string file = __FILE__, int line = __LINE__) immutable
    {
        return this[].getVerbose(moment, file, line);
    }

    /**
    Gets data for the index (extra verbose exception).
    Params:
        moment = index
    Returns: data that corresponds to the index.
    Throws:
        Detailed exception if the series does not contains the index.
    See_also: $(LREF Series.get), $(LREF Series.tryGet)
    */
    auto ref getExtraVerbose(Index)(Index moment, string exceptionInto, string file = __FILE__, int line = __LINE__)
    {
        import std.format: format;
        return this.get(moment, new Exception(format("%s. %s %s key", exceptionInto, defaultMsg!(), moment), file, line));
    }

    /// ditto
    auto ref getExtraVerbose(Index)(Index moment, string exceptionInto, string file = __FILE__, int line = __LINE__) const
    {
        return this[].getExtraVerbose(moment, exceptionInto, file, line);
    }

    /// ditto
    auto ref getExtraVerbose(Index)(Index moment, string exceptionInto, string file = __FILE__, int line = __LINE__) immutable
    {
        return this[].getExtraVerbose(moment, exceptionInto, file, line);
    }

    ///
    bool contains(Index)(Index moment) const
    {
        size_t idx = index.assumeSorted.lowerBound(moment).length;
        return idx < _data._lengths[0] && index[idx] == moment;
    }

    ///
    auto opBinaryRight(string op : "in", Index)(Index moment)
    {
        size_t idx = index.assumeSorted.lowerBound(moment).length;
        bool cond = idx < _data._lengths[0] && index[idx] == moment;
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
    auto opBinaryRight(string op : "in", Index)(Index moment) const
    {
        return moment in this[];
    }

    /// ditto
    auto opBinaryRight(string op : "in", Index)(Index moment) immutable
    {
        return moment in this[];
    }

    ///
    bool tryGet(Index, Value)(Index moment, ref Value val)
    {
        size_t idx = index.assumeSorted.lowerBound(moment).length;
        auto cond = idx < _data._lengths[0] && index[idx] == moment;
        if (cond)
            val = data[idx];
        return cond;
    }

    /// ditto
    bool tryGet(Index, Value)(Index moment, ref Value val) const
    {
        return this[].tryGet(moment, val);
    }

    /// ditto
    bool tryGet(Index, Value)(Index moment, ref Value val) immutable
    {
        return this[].tryGet(moment, val);
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
        return this[].asSlice;
    }

    /// ditto
    auto asSlice()() immutable @property
    {
        return this[].asSlice;
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
    _Slice!() opSlice(size_t dimension)(size_t i, size_t j) const
        if (dimension < N)
    in
    {
        assert(i <= j,
            "Series.opSlice!" ~ dimension.stringof ~ ": the left bound must be less than or equal to the right bound.");
        enum errorMsg = ": difference between the right and the left bounds"
                        ~ " must be less than or equal to the length of the given dimension.";
        assert(j - i <= _data._lengths[dimension],
              "Series.opSlice!" ~ dimension.stringof ~ errorMsg);
    }
    body
    {
        return typeof(return)(i, j);
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
        return lightConst[slices];
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices) immutable
        if (allSatisfy!(templateOr!(is_Slice, isIndex), Slices))
    {
        return lightImmutable[slices];
    }

    /// ditto
    ref opAssign(RIndexIterator, RIterator)(auto ref Series!(RIndexIterator, RIterator, N, kind) rvalue)
        if (isAssignable!(IndexIterator, RIndexIterator) && isAssignable!(Iterator, RIterator))
    {
        this._data._lengths = rvalue._data._lengths;
        static if (this._data._strides.length)
            this._data._strides = rvalue._data._strides;
        this._data._iterator = rvalue._data._iterator;
        this._index = rvalue._index;
    }

    /// ditto
    ref opAssign(RIndexIterator, RIterator)(auto ref const Series!(RIndexIterator, RIterator, N, kind) rvalue)
        if (isAssignable!(IndexIterator, LightConstOf!RIndexIterator) && isAssignable!(Iterator, LightConstOf!RIterator))
    {
        return this = rvalue[];
    }

    /// ditto
    ref opAssign(RIndexIterator, RIterator)(auto ref immutable Series!(RIndexIterator, RIterator, N, kind) rvalue)
        if (isAssignable!(IndexIterator, LightImmutableOf!RIndexIterator) && isAssignable!(Iterator, LightImmutableOf!RIterator))
    {
        return this = rvalue[];
    }

    /// ditto
    ref opAssign(typeof(null))
    {
        this = typeof(this)(null);
    }

    /// ditto
    auto save()() @property
    {
        return this;
    }

    ///
    auto lightConst()() const @property
    {
        return index.series(data);
    }

    /// ditto
    auto lightImmutable()() immutable @property
    {
        return index.series(data);
    }

    /// ditto
    auto trustedImmutable()() const @property @trusted
    {
        return (cast(immutable) this)[];
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
Series!(K*, V*) series(K, V)(V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    immutable size_t length = aa.length;
    alias R = typeof(return);
    auto ret = ()
    {
        if (__ctfe)
        {
            K[] keys;
            V[] values;
            foreach(kv; aa.byKeyValue)
            {
                keys ~= kv.key;
                values ~= kv.value;
            }
            return (()=>.series(cast(Unqual!K[])keys, cast(Unqual!V[])values))();
        }
        else
        {
            import mir.ndslice.allocation: uninitSlice;

            auto ret = series(length.uninitSlice!(Unqual!K), length.uninitSlice!(Unqual!V));
            auto it = ret;
            foreach(kv; aa.byKeyValue)
            {
                import std.backdoor: emplaceRef;
                emplaceRef!K(it.index.front, kv.key);
                emplaceRef!V(it._data.front, kv.value);
                it.popFront;
            }
            return ret;
        }
    }();

    ret.sort;
    static if (is(typeof(ret) == typeof(return)))
        return ret;
    else
        return ()@trusted{ return cast(R) ret; }();
}

/// ditto
Series!(const(K)*, const(V)*) series(K, V)(const V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return .series(cast(const(V)[const K]) aa);
}

/// ditto
Series!(immutable(K)*, immutable(V)*) series(K, V)(immutable V[K] aa)
    if (is(typeof(K.init < K.init)) && is(typeof(Unqual!K.init < Unqual!K.init))) 
{
    return .series(cast(immutable(V)[immutable K]) aa);
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
    auto s = [1: 1.5, 3: 3.3, 2: 2.9].series;
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
    import std.backdoor: emplaceRef;

    immutable size_t length = aa.length;

    auto ret = series(
        allocator.makeUninitSlice!(Unqual!K)(length),
        allocator.makeUninitSlice!(Unqual!V)(length));

    auto it = ret;
    foreach(kv; aa.byKeyValue)
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
Finds an index such that `series.index[index] == moment`.

Params:
    series = series
    moment = index to find in the series
Returns:
    `size_t.max` if the series does not contain the moment and appropriate index otherwise.
+/
size_t findIndex(IndexIterator, Iterator, size_t N, SliceKind kind, Index)(Series!(IndexIterator, Iterator, N, kind) series, Index moment)
{
    import std.range: assumeSorted;

    auto idx = series.index.assumeSorted.lowerBound(moment).length;
    if (idx < series._data._lengths[0] && series.index[idx] == moment)
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
Finds a backward index such that `series.index[$ - backward_index] == moment`.

Params:
    series = series
    moment = index moment to find in the series
Returns:
    `0` if the series does not contain the moment and appropriate backward index otherwise.
+/
size_t find(IndexIterator, Iterator, size_t N, SliceKind kind, Index)(Series!(IndexIterator, Iterator, N, kind) series, Index moment)
{
    import std.range: assumeSorted;

    auto idx = series.index.assumeSorted.lowerBound(moment).length;
    auto bidx = series._data._lengths[0] - idx;
    if (bidx && series.index[idx] == moment)
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
Sorts index-series according to the `less` predicate applied to index observations.

The function works only for 1-dimensional index-series data.
+/
template sort(alias less = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    {
    @optmath:

        /++
        One dimensional case.
        +/
        Series!(IndexIterator, Iterator, N, kind)
            sort(IndexIterator, Iterator, size_t N, SliceKind kind)
            (Series!(IndexIterator, Iterator, N, kind) series)
        if (N == 1)
        {
            import mir.ndslice.sorting: sort;
            import mir.ndslice.topology: zip;
            with(series)
                index.zip(data).sort!((a, b) => less(a.a, b.a));
            return series;
        }

        /++
        N-dimensional case. Requires index and data buffers.
        +/
        Series!(IndexIterator, Iterator, N, kind)
            sort(
                IndexIterator,
                Iterator,
                size_t N,
                SliceKind kind,
                SortIndexIterator,
                DataIterator,
                )
            (
                Series!(IndexIterator, Iterator, N, kind) series,
                Slice!SortIndexIterator indexBuffer,
                Slice!DataIterator dataBuffer,
            )
        {
            import mir.algorithm.iteration: each;
            import mir.ndslice.sorting: sort;
            import mir.ndslice.topology: iota, zip, ipack, evertPack;

            assert(indexBuffer.length == series.length);
            assert(dataBuffer.length == series.length);
            indexBuffer[] = indexBuffer.length.iota!(typeof(indexBuffer.front));
            series.index.zip(indexBuffer).sort!((a, b) => less(a.a, b.a));
            series.data.ipack!1.evertPack.each!((sl){
            {
                assert(sl.shape == dataBuffer.shape);
                dataBuffer[] = sl[indexBuffer];
                sl[] = dataBuffer;
            }});
            return series;
        }
    }
    else
        alias sort = .sort!(naryFun!less);
}

/// 1D data
pure version(mir_test) unittest
{
    auto index = [1, 2, 4, 3].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = index.series(data);
    series.sort;
    assert(series.index == [1, 2, 3, 4]);
    assert(series.data == [2.1, 3.4, 7.8, 5.6]);
    /// initial index and data are the same
    assert(index.iterator is series.index.iterator);
    assert(data.iterator is series.data.iterator);

    foreach(obs; series)
    {
        static assert(is(typeof(obs) == Observation!(int, double)));
    }
}

/// 2D data
pure version(mir_test) unittest
{
    import mir.series;
    import mir.ndslice.allocation: uninitSlice;

    auto index = [4, 2, 3, 1].sliced;
    auto data =
        [2.1, 3.4, 
         5.6, 7.8,
         3.9, 9.0,
         4.0, 2.0].sliced(4, 2);
    auto series = index.series(data);

    series.sort(
        uninitSlice!size_t(series.length), // index buffer
        uninitSlice!double(series.length), // data buffer
        );

    assert(series.index == [1, 2, 3, 4]);
    assert(series.data ==
        [[4.0, 2.0],
         [5.6, 7.8],
         [3.9, 9.0],
         [2.1, 3.4]]);
    /// initial index and data are the same
    assert(index.iterator is series.index.iterator);
    assert(data.iterator is series.data.iterator);
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
        algo!(I, E)(lhs, rhs, ret);
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
        import std.backdoor: emplaceRef;
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
    return unionSeriesImplPrivate(seriesTuple);
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
Makes exactly one memory allocation for two series union
and exactly two memory allocation for three and more series union.

Params:
    allocator = memory allocator
    seriesTuple = variadic static array of composed of series.
Returns: sorted manually allocated series.
See_also $(LREF unionSeries)
*/
auto makeUnionSeries(IndexIterator, Iterator, size_t N, SliceKind kind, size_t C, Allocator)(auto ref Allocator allocator, Series!(IndexIterator, Iterator, N, kind)[C] seriesTuple...)
    if (C > 1)
{
    return unionSeriesImplPrivate(seriesTuple, allocator);
}

///
@system pure nothrow version(mir_test) unittest
{
    import std.datetime: Date;
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
    import std.backdoor: emplaceRef;
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

private auto unionSeriesImplPrivate(IndexIterator, Iterator, size_t N, SliceKind kind, size_t C, Allocator...)(ref Series!(IndexIterator, Iterator, N, kind)[C] seriesTuple, ref Allocator allocator)
    if (C > 1 && Allocator.length <= 1)
{
    import mir.algorithm.setops: unionLength;
    import mir.internal.utility: Iota;
    import mir.ndslice.allocation: uninitSlice, makeUninitSlice;

    Slice!IndexIterator[C] indeces;
    foreach (i; Iota!C)
        indeces[i] = seriesTuple[i].index;

    immutable len = indeces[].unionLength; 

    alias I = typeof(seriesTuple[0].index.front);
    alias E = typeof(seriesTuple[0].data.front);
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

    static if (Allocator.length)
        auto ret = (()@trusted => allocator[0].makeUninitSlice!UI(len).series(allocator[0].makeUninitSlice!UE(shape)))();
    else
        auto ret = (()@trusted => len.uninitSlice!UI.series(shape.uninitSlice!UE))();

    static if (N == 2) // fast path
    {
        alias algo = troykaSeriesImpl!(
            (auto ref key, auto ref left) => left,
            (auto ref key, auto ref left, auto ref right) => left,
            (auto ref key, auto ref right) => right,
        );
        algo!(I, E)(seriesTuple[0], seriesTuple[1], ret);
    }
    else
    {
        unionSeriesImpl!(I, E)(seriesTuple, ret);
    }

    return () @trusted {return cast(R) ret; }();
}

/**
Inserts or assigns a series to the associative array `aa`.
Params:
    aa = associative array
    series = series
Returns:
    associative array 
*/
ref V[K] insertOrAssign(V, K, IndexIterator, Iterator, size_t N, SliceKind kind)(return ref V[K] aa, Series!(IndexIterator, Iterator, N, kind) series) @property
{
    foreach (i; 0 .. series.length)
    {
        aa[series.index[i]] = series.data[i];
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
ref V[K] insert(V, K, IndexIterator, Iterator, size_t N, SliceKind kind)(return ref V[K] aa, Series!(IndexIterator, Iterator, N, kind) series) @property
{
    foreach (i; 0 .. series.length)
    {
        if (series.index[i] in aa)
            continue;
        aa[series.index[i]] = series.data[i];
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
