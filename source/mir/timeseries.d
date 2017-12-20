/++
$(H1 Time-series)

The module contains $(LREF Series) data structure with special iteration and indexing methods.
It is aimed to construct time-series using Mir and Phobos algorithms.

Public_imports: $(MREF mir,ndslice,slice).

Copyright: Copyright © 2017, Kaleidic Associates Advisory Limited
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolate, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.timeseries;

public import mir.ndslice.slice;
import std.traits;

///
version(mir_test) unittest
{
    import std.datetime: Date;
    import std.algorithm.setops: nWayUnion;
    import std.algorithm.iteration: uniq;
    import std.array: array;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.allocation: slice;

    auto time0 = [
        Date(2017, 01, 01),
        Date(2017, 03, 01),
        Date(2017, 04, 01)].sliced;

    auto data0 = [1.0, 3, 4].sliced;
    auto series0 = time0.series(data0);

    auto time1 = [
        Date(2017, 01, 01),
        Date(2017, 02, 01),
        Date(2017, 05, 01)].sliced;

    auto data1 = [10.0, 20, 50].sliced;
    auto series1 = time1.series(data1);

    auto time = [time0, time1].nWayUnion.uniq.array.sliced;
    auto data = slice!double([time.length, 2], 0); // initialized to 0 value
    auto series = time.series(data);

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
Plain time observation data structure.
Observation are used as return tuple for for indexing $(LREF Series).
+/
struct Observation(Time, Data)
{
    /// Date, date-time, time, or integer.
    Time time;
    /// Value or ndslice.
    Data data;
}

/// Convenient function for $(LREF Observation) construction.
auto observation(Time, Data)(Time time, Data data)
{
    return Observation!(Time, Data)(time, data);
}

/++
Plain time series data structure.

`*.time[i]` corresponds to `*.data[i]`.
+/
struct Series(TimeIterator, SliceKind kind, size_t[] packs, Iterator)
{
    import std.range: SearchPolicy, assumeSorted;

@optmath:

    ///
    Slice!(kind, packs, Iterator) _data;

    ///
    TimeIterator _time;

    ///
    this()(Slice!(Contiguous, [1], TimeIterator) time, Slice!(kind, packs, Iterator) data)
    {
        assert(time.length == data.length, "Series constructor: time and data lengths must be equal.");
        _data = data;
        _time = time._iterator;

    }

    ///
    bool opEquals()(const typeof(this) rhs) const
    {
        return this.time == rhs.time && this.data == rhs.data;
    }

    /++
    Time series is assumed to be sorted.

    `TimeIterator` is an iterator on top of date, date-time, time, or integer types.
    For example, `Date*`, `DateTime*`, `immutable(long)*`, `mir.ndslice.iterator.IotaIterator`.
    +/
    auto time()() @property @trusted
    {
        return _time.sliced(_data._lengths[0]);
    }

    /// ditto
    auto time()() @property @trusted const
    {
        return _time.sliced(_data._lengths[0]);
    }

    /// ditto
    auto time()() @property @trusted immutable
    {
        return _time.sliced(_data._lengths[0]);
    }

    /++
    Data is any ndslice with only one constraints, 
    `data` and `time` lengths should be equal.
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

    /++
    Special `[] =` index-assign operator for time-series.
    Assigns data from `r` with time intersection.
    If a time index in `r` is not in the time index for this series, then no op-assign will take place.
    This and r series are assumed to be sorted.

    Params:
        r = rvalue time-series
    +/
    void opIndexAssign(TimeIterator_, SliceKind kind_, size_t[] packs_, Iterator_)
        (Series!(TimeIterator_, kind_, packs_, Iterator_) r)
    {
        opIndexOpAssign!("", TimeIterator_, kind_, packs_, Iterator_)(r);
    }

    ///
    version(mir_test) unittest
    {
        auto time = [1, 2, 3, 4].sliced;
        auto data = [10.0, 10, 10, 10].sliced;
        auto series = time.series(data);

        auto rtime = [0, 2, 4, 5].sliced;
        auto rdata = [1.0, 2, 3, 4].sliced;
        auto rseries = rtime.series(rdata);

        // series[] = rseries;
        series.opIndexAssign(rseries);
        assert(series.data == [10, 2, 10, 3]);
    }

    /++
    Special `[] op=` index-op-assign operator for time-series.
    Op-assigns data from `r` with time intersection.
    If a time index in `r` is not in the time index for this series, then no op-assign will take place.
    This and r series are assumed to be sorted.

    Params:
        r = rvalue time-series
    +/
    void opIndexOpAssign(string op, TimeIterator_, SliceKind kind_, size_t[] packs_, Iterator_)
        (Series!(TimeIterator_, kind_, packs_, Iterator_) r)
    {
        import std.traits: Unqual;
        auto l = this;
        if (r.empty)
            return;
        if (l.empty)
            return;
        Unqual!(typeof(r.time.front)) rf = r.time.front;
        Unqual!(typeof(l.time.front)) lf = l.time.front;
        if (lf > rf)
            goto R;
        if (lf < rf)
            goto L;
        goto E;
        F: for(;;)
        {
            R: do
            {
                r.popFront;
                if (r.empty)
                    break F;
                rf = r.time.front;
            }
            while(lf > rf);
            if (lf == rf)
            {
            E:
                static if (packs != [1])
                    mixin("l.data.front[] " ~ op ~ "= r.data.front;");
                else
                    mixin("l.data.front   " ~ op ~ "= r.data.front;");

                r.popFront;
                if (r.empty)
                    break F;
                rf = r.time.front;
            }
            L: do
            {
                l.popFront;
                if (l.empty)
                    break F;
                lf = l.time.front;
            }
            while(lf < rf);
            if (lf == rf)
                goto E;
        }
    }

    ///
    version(mir_test) unittest
    {
        auto time = [1, 2, 3, 4].sliced;
        auto data = [10.0, 10, 10, 10].sliced;
        auto series = time.series(data);

        auto rtime = [0, 2, 4, 5].sliced;
        auto rdata = [1.0, 2, 3, 4].sliced;
        auto rseries = rtime.series(rdata);

        series[] += rseries;
        assert(series.data == [10, 12, 10, 13]);
    }

    /++
    This function uses a search with policy sp to find the largest left subrange on which 
    `t < moment` is true for all `t`.
    The search schedule and its complexity are documented in `std.range.SearchPolicy`.
    +/
    auto lowerBound(SearchPolicy sp = SearchPolicy.binarySearch, Time)(Time moment)
    {
        return this[0 .. time.assumeSorted.lowerBound!sp(moment).length];
    }

    /// ditto
    auto lowerBound(SearchPolicy sp = SearchPolicy.binarySearch, Time)(Time moment) const
    {
        return this[0 .. time.assumeSorted.lowerBound!sp(moment).length];
    }


    /++
    This function uses a search with policy sp to find the largest left subrange on which 
    `t > moment` is true for all `t`.
    The search schedule and its complexity are documented in `std.range.SearchPolicy`.
    +/
    auto upperBound(SearchPolicy sp = SearchPolicy.binarySearch, Time)(Time moment)
    {
        return this[$ - time.assumeSorted.upperBound!sp(moment).length .. $];
    }

    /// ditto
    auto upperBound(SearchPolicy sp = SearchPolicy.binarySearch, Time)(Time moment) const
    {
        return this[$ - time.assumeSorted.upperBound!sp(moment).length .. $];
    }

    ///
    bool contains(Time)(Time moment)
    {
        size_t idx = time.assumeSorted.lowerBound(moment).length;
        return idx < _data._lengths[0] && time[idx] == moment;
    }

    ///
    auto opBinaryRight(string op : "in", Time)(Time moment)
    {
        size_t idx = time.assumeSorted.lowerBound(moment).length;
        bool cond = idx < _data._lengths[0] && time[idx] == moment;
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

    /// ndslice-like primitives
    bool empty(size_t dimension = 0)() const @property
        if (dimension < packs[0])
    {
        return !length!dimension;
    }

    /// ditto
    size_t length(size_t dimension = 0)() const @property
        if (dimension < packs[0])
    {
        return _data.length!dimension;
    }

    /// ditto
    auto front(size_t dimension = 0)() @property
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (dimension)
        {
            return time.series(data.front!dimension);
        }
        else
        {
            return time.front.observation(data.front);
        }
    }

    /// ditto
    auto back(size_t dimension = 0)() @property
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (dimension)
        {
            return time.series(_data.back!dimension);
        }
        else
        {
            return time.back.observation(_data.back);
        }
    }

    /// ditto
    void popFront(size_t dimension = 0)() @trusted
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (dimension == 0)
            _time++;
        _data.popFront!dimension;
    }

    /// ditto
    void popBack(size_t dimension = 0)()
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        _data.popBack!dimension;
    }

    /// ditto
    void popFrontExactly(size_t dimension = 0)(size_t n) @trusted
        if (dimension < packs[0])
    {
        assert(length!dimension >= n);
        static if (dimension == 0)
            _time += n;
        _data.popFrontExactly!dimension(n);
    }

    /// ditto
    void popBackExactly(size_t dimension = 0)(size_t n)
        if (dimension < packs[0])
    {
        assert(length!dimension >= n);
        _data.popBackExactly!dimension(n);
    }

    /// ditto
    void popFrontN(size_t dimension = 0)(size_t n)
        if (dimension < packs[0])
    {
        auto len = length!dimension;
        n = n <= len ? n : len;
        popFrontExactly!dimension(n);
    }

    /// ditto
    void popBackN(size_t dimension = 0)(size_t n)
        if (dimension < packs[0])
    {
        auto len = length!dimension;
        n = n <= len ? n : len;
        popBackExactly!dimension(n);
    }

    /// ditto
    _Slice!() opSlice(size_t dimension)(size_t i, size_t j) const
        if (dimension < packs[0])
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
            return time[slices[0]].series(data[slices]);
        }
        else
        {
            return time[slices[0]].observation(data[slices]);
        }
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices) const
        if (allSatisfy!(templateOr!(is_Slice, isIndex), Slices))
    {
        static if (Slices.length == 0)
        {
            return time.series(_data[]);
        }
        else
        static if (is_Slice!(Slices[0]))
        {
            return time[slices[0]].series(data[slices]);
        }
        else
        {
            return time[slices[0]].observation(data[slices]);
        }
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices) immutable
        if (allSatisfy!(templateOr!(is_Slice, isIndex), Slices))
    {
        static if (Slices.length == 0)
        {
            return time.series(_data[]);
        }
        else
        static if (is_Slice!(Slices[0]))
        {
            return time[slices[0]].series(data[slices]);
        }
        else
        {
            return time[slices[0]].observation(data[slices]);
        }
    }

    /// ditto
    auto save()() @property
    {
        return this;
    }
}

/// 1-dimensional data
@safe pure version(mir_test) unittest
{
    auto time = [1, 2, 3, 4].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = time.series(data);
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
        Series!(int*, cast(SliceKind)2, [1LU], double*)));
    static assert(is(typeof(cseries[]) == 
        Series!(const(int)*, cast(SliceKind)2, [1LU], const(double)*)));
    static assert(is(typeof((cast(immutable) series)[]) == 
        Series!(immutable(int)*, cast(SliceKind)2, [1LU], immutable(double)*)));

    /// slicing
    auto seriesSlice  = series[1 .. $ - 1];
    assert(seriesSlice.time == time[1 .. $ - 1]);
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

    auto time = [
        Date(2017, 01, 01),
        Date(2017, 02, 01),
        Date(2017, 03, 01),
        Date(2017, 04, 01)].sliced;

    //  1,  2,  3,  4,  5
    //  6,  7,  8,  9, 10
    // 11, 12, 13, 14, 15
    // 16, 17, 18, 19, 20
    auto data = iota([time.length, row_length], 1);

    // canonical and universal ndslices are more flexible then contiguous
    auto series = time.series(data.canonical);

    /// slicing
    auto seriesSlice  = series[1 .. $ - 1, 2 .. 4];
    assert(seriesSlice.time == time[1 .. $ - 1]);
    assert(seriesSlice.data == data[1 .. $ - 1, 2 .. 4]);

    static if (kindOf!(typeof(series.data)) != Contiguous)
        static assert(is(typeof(series) == typeof(seriesSlice)));

    /// indexing
    assert(series[1, 4] == observation(Date(2017, 02, 01), 10));
    assert(series[2] == observation(Date(2017, 03, 01), iota([row_length], 11)));

    /// range primitives
    assert(series.length == 4);
    assert(series.length!1 == 5);

    series.popFront!1;
    assert(series.length!1 == 4);
}

/// Convenient function for $(LREF Series) construction.
auto series(TimeIterator, SliceKind kind, size_t[] packs, Iterator)
    (
        Slice!(Contiguous, [1], TimeIterator) time,
        Slice!(kind, packs, Iterator) data,
    )
{
    assert(time.length == data.length);
    return Series!(TimeIterator, kind, packs, Iterator)(time, data);
}

/// Returns: packs if `U` is a $(LREF Series) type or null otherwise;
enum isSeries(U : Series!(TimeIterator, kind, packs, Iterator), TimeIterator, SliceKind kind, size_t[] packs, Iterator) = packs;

/// ditto
enum isSeries(U) = (size_t[]).init;


/++
Finds an index such that `series.time[index] == moment`.

Params:
    series = timeseries
    moment = time moment to find in the series
Returns:
    `size_t.max` if the series does not contain the moment and appropriate index otherwise.
+/
size_t findIndex(TimeIterator, SliceKind kind, size_t[] packs, Iterator, Time)(Series!(TimeIterator, kind, packs, Iterator) series, Time moment)
{
    import std.range: assumeSorted;

    auto idx = series.time.assumeSorted.lowerBound(moment).length;
    if (idx < series._data._lengths[0] && series.time[idx] == moment)
    {
        return idx;
    }
    return size_t.max;
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto time = [1, 2, 3, 4].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = time.series(data);

    assert(series.data[series.findIndex(3)] == 5.6);
    assert(series.findIndex(0) == size_t.max);
}

/++
Finds a backward index such that `series.time[$ - backward_index] == moment`.

Params:
    series = timeseries
    moment = time moment to find in the series
Returns:
    `0` if the series does not contain the moment and appropriate backward index otherwise.
+/
size_t find(TimeIterator, SliceKind kind, size_t[] packs, Iterator, Time)(Series!(TimeIterator, kind, packs, Iterator) series, Time moment)
{
    import std.range: assumeSorted;

    auto idx = series.time.assumeSorted.lowerBound(moment).length;
    auto bidx = series._data._lengths[0] - idx;
    if (bidx && series.time[idx] == moment)
    {
        return bidx;
    }
    return 0;
}

///
@safe pure nothrow version(mir_test) unittest
{
    auto time = [1, 2, 3, 4].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = time.series(data);

    assert(series.data[$ - series.find(3)] == 5.6);
    assert(series.find(0) == 0);
}

/++
Sorts time-series according to the `less` predicate applied to time observations.

The function works only for 1-dimensional time-series data.
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
        Series!(TimeIterator, kind, packs, Iterator)
            sort(TimeIterator, SliceKind kind, size_t[] packs, Iterator)
            (Series!(TimeIterator, kind, packs, Iterator) series)
        if (packs == [1])
        {
            import mir.ndslice.sorting: sort;
            import mir.ndslice.topology: zip;
            with(series)
                time.zip(data).sort!((a, b) => less(a.a, b.a));
            return series;
        }

        /++
        N-dimensional case. Requires index and data buffers.
        +/
        Series!(TimeIterator, kind, packs, Iterator)
            sort(
                TimeIterator,
                SliceKind kind,
                size_t[] packs,
                Iterator,
                SliceKind indexKind,
                IndexIterator,
                SliceKind dataKind,
                DataIterator,
                )
            (
                Series!(TimeIterator, kind, packs, Iterator) series,
                Slice!(indexKind, [1], IndexIterator) indexBuffer,
                Slice!(dataKind, [1], DataIterator) dataBuffer,
            )
            if (packs.length == 1)
        {
            import mir.ndslice.algorithm: each;
            import mir.ndslice.sorting: sort;
            import mir.ndslice.topology: iota, zip, ipack, evertPack;

            assert(indexBuffer.length == series.length);
            assert(dataBuffer.length == series.length);
            indexBuffer[] = indexBuffer.length.iota!(typeof(indexBuffer.front));
            series.time.zip(indexBuffer).sort!((a, b) => less(a.a, b.a));
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
    auto time = [1, 2, 4, 3].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = time.series(data);
    series.sort;
    assert(series.time == [1, 2, 3, 4]);
    assert(series.data == [2.1, 3.4, 7.8, 5.6]);
    /// initial time and data are the same
    assert(time.iterator is series.time.iterator);
    assert(data.iterator is series.data.iterator);
}

/// 2D data
pure version(mir_test) unittest
{
    import mir.timeseries;
    import mir.ndslice.allocation: uninitSlice;

    auto time = [4, 2, 3, 1].sliced;
    auto data =
        [2.1, 3.4, 
         5.6, 7.8,
         3.9, 9.0,
         4.0, 2.0].sliced(4, 2);
    auto series = time.series(data);

    series.sort(
        uninitSlice!size_t(series.length), // index buffer
        uninitSlice!double(series.length), // data buffer
        );

    assert(series.time == [1, 2, 3, 4]);
    assert(series.data ==
        [[4.0, 2.0],
         [5.6, 7.8],
         [3.9, 9.0],
         [2.1, 3.4]]);
    /// initial time and data are the same
    assert(time.iterator is series.time.iterator);
    assert(data.iterator is series.data.iterator);
}
