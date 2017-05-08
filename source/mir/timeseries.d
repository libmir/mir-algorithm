/++
$(H1 Time-series)

The module contains $(LREF Series) data structure with special iteration and indexing methods.
It is aimed to construct time-series using Mir and Phobos algorithms.

Public_imports: $(MREF mir,ndslice,slice).

Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, interpolation, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.timeseries;

public import mir.ndslice.slice;

///
unittest
{
    import std.datetime: Date;
    import std.algorithm.setops: nWayUnion;
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

    auto time = [time0, time1].nWayUnion.array.sliced;
    auto data = slice!double([time.length, 2], 0); // initialized to 0 value
    auto series = time.series(data);

    series[0 .. $, 0][] = series0; // fill first column
    series[0 .. $, 1][] = series1; // fill second column

    assert(data == [
        [1, 10],
        [0,  0],
        [0, 20],
        [3,  0],
        [4,  0],
        [0, 50]]);
}

import mir.ndslice.slice;
import mir.ndslice.internal: _Slice, is_Slice, isIndex;
import mir.internal.utility: fastmath;

import std.meta;

@fastmath:

/++
Plain time moment data structure.
Moment are used as return tuple for for indexing $(LREF Series).
+/
struct Moment(Time, Data)
{
    /// Date, date-time, time, or integer.
    Time time;
    /// Value or ndslice.
    Data data;
}

/// Convenient function for $(LREF Moment) construction.
auto moment(Time, Data)(Time time, Data data)
{
    return Moment!(Time, Data)(time, data);
}

/++
Plain time series data structure.

`*.time[i]` corresponds to `*.data[i]`.
+/
struct Series(TimeIterator, SliceKind kind, size_t[] packs, Iterator)
{
    /++
    Time series is assumed to be sorted.

    `TimeIterator` is an iterator on top of date, date-time, time, or integer types.
    For example, `Date*`, `DateTime*`, `immutable(long)*`, `mir.ndslice.iterator.IotaIterator`.
    +/
    Slice!(Contiguous, [1], TimeIterator) time;

    /++
    Data is any ndslice with only one constraints, 
    `data` and `time` lengths should be equal.
    +/
    Slice!(kind, packs, Iterator) data;

@fastmath:

    /++
    Special `[] = ` index-assign operator for time-series.
    Assigns data from `r` for time intersection.
    This and `r` series are assumed to be sorted.
    Params:
        r = rvalue time-series
    +/
    void opIndexAssign(TimeIterator_, SliceKind kind_, size_t[] packs_, Iterator_)
        (Series!(TimeIterator_, kind_, packs_, Iterator_) r)
    {
        opIndexOpAssign!("", TimeIterator_, kind_, packs_, Iterator_)(r);
    }

    ///
    unittest
    {
        auto time = [1, 2, 3, 4].sliced;
        auto data = [10.0, 10, 10, 10].sliced;
        auto series = time.series(data);

        auto rtime = [0, 2, 4, 5].sliced;
        auto rdata = [1.0, 2, 3, 4].sliced;
        auto rseries = rtime.series(rdata);

        series[] = rseries;
        assert(series.data == [10, 2, 10, 3]);
    }

    /++
    Special `[] op= ` index-op-assign operator for time-series.
    Op-assigns data from `r` for time intersection.
    This and `r` series are assumed to be sorted.
    Params:
        r = rvalue time-series
    +/
    void opIndexOpAssign(string op, TimeIterator_, SliceKind kind_, size_t[] packs_, Iterator_)
        (Series!(TimeIterator_, kind_, packs_, Iterator_) r)
    {
        auto l = this;
        assert(r.data.length == r.time.length);
        assert(l.data.length == l.time.length);
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
                static if (isSlice!(typeof(l.data.front)))
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
    unittest
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

    /// ndslice-like primitives
    bool empty(size_t dimension = 0)() const @property
        if (dimension < packs[0])
    {
        static if (!dimension)
            assert(data.length == time.length);
        return !length!dimension;
    }

    /// ditto
    size_t length(size_t dimension = 0)() const @property
        if (dimension < packs[0])
    {
        static if (!dimension)
            assert(data.length == time.length);
        return data.length!dimension;
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
            return time.front.moment(data.front);
        }
    }

    /// ditto
    auto back(size_t dimension = 0)() @property
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (dimension)
        {
            return time.series(data.back!dimension);
        }
        else
        {
            return time.back.moment(data.back);
        }
    }

    /// ditto
    void popFront(size_t dimension = 0)()
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (!dimension)
            time.popFront;
        data.popFront!dimension;
    }

    /// ditto
    void popBack(size_t dimension = 0)()
        if (dimension < packs[0])
    {
        assert(!empty!dimension);
        static if (!dimension)
            time.popBack;
        data.popBack!dimension;
    }

    /// ditto
    void popFrontExactly(size_t dimension = 0)(size_t n)
        if (dimension < packs[0])
    {
        assert(length!dimension >= n);
        static if (!dimension)
            time.popFrontExactly(n);
        data.popFrontExactly!dimension(n);
    }

    /// ditto
    void popBackExactly(size_t dimension = 0)(size_t n)
        if (dimension < packs[0])
    {
        assert(length!dimension >= n);
        static if (!dimension)
            time.popBackExactly(n);
        data.popBackExactly!dimension(n);
    }

    /// ditto
    void popFrontN(size_t dimension = 0)(size_t n)
        if (dimension < packs[0])
    {
        n = n <= length ? n : length;
        popFrontExactly!dimension(n);
    }

    /// ditto
    void popBackN(size_t dimension = 0)(size_t n)
        if (dimension < packs[0])
    {
        n = n <= length ? n : length;
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
        assert(j - i <= data._lengths[dimension],
              "Series.opSlice!" ~ dimension.stringof ~ errorMsg);
    }
    body
    {
        return typeof(return)(i, j);
    }

    /// ditto
    size_t opDollar(size_t dimension = 0)() const
    {
        return data.opDollar!dimension;
    }

    /// ditto
    auto opIndex(Slices...)(Slices slices)
        if (allSatisfy!(templateOr!(is_Slice, isIndex), Slices))
    {
        static if (is_Slice!(Slices[0]))
        {
            return time[slices[0]].series(data[slices]);
        }
        else
        {
            return time[slices[0]].moment(data[slices]);
        }
    }

    /// ditto
    auto save()() @property
    {
        return this;
    }
}

/// 1-dimensional data
unittest
{
    auto time = [1, 2, 3, 4].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = time.series(data);

    /// slicing
    auto seriesSlice  = series[1 .. $ - 1];
    assert(seriesSlice.time == time[1 .. $ - 1]);
    assert(seriesSlice.data == data[1 .. $ - 1]);
    static assert(is(typeof(series) == typeof(seriesSlice)));

    /// indexing
    assert(series[1] == moment(2, 3.4));

    /// range primitives
    assert(series.length == 4);
    assert(series.front == moment(1, 2.1));

    series.popFront;
    assert(series.front == moment(2, 3.4));

    series.popBackN(10);
    assert(series.empty);
}

/// 2-dimensional data
unittest
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
    assert(series[1, 4] == moment(Date(2017, 02, 01), 10));
    assert(series[2] == moment(Date(2017, 03, 01), iota([row_length], 11)));

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
Sorts time-series according to the `less` predicate applied to time moments.

The function works only for 1-dimensional time-series data.
+/
template sort(alias less = "a < b")
{
    import mir.functional: naryFun;
    static if (__traits(isSame, naryFun!less, less))
    ///
    @fastmath
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
    else
        alias sort = .sort!(naryFun!less);
}

/// 1-dimensional data
unittest
{
    auto time = [1, 2, 4, 3].sliced;
    auto data = [2.1, 3.4, 5.6, 7.8].sliced;
    auto series = time.series(data);
    series.sort;
    assert(series.time == [1, 2, 3, 4]);
    assert(series.data == [2.1, 3.4, 7.8, 5.6]);
    /// initial time and data are the same
    assert(time == [1, 2, 3, 4]);
    assert(data == [2.1, 3.4, 7.8, 5.6]);
}
