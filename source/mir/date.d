/++
Fast BetterC Date type with Boost ABI and mangling compatability.

$(SCRIPT inhibitQuickIndex = 1;)
$(DIVC quickindex,
$(BOOKTABLE,
$(TR $(TH Category) $(TH Functions))
$(TR $(TD Main date types) $(TD
    $(LREF Date)
))
$(TR $(TD Other date types) $(TD
    $(LREF Month)
    $(LREF DayOfWeek)
))
$(TR $(TD Date checking) $(TD
    $(LREF valid)
    $(LREF yearIsLeapYear)
))
$(TR $(TD Date conversion) $(TD
    $(LREF daysToDayOfWeek)
))
$(TR $(TD Other) $(TD
    $(LREF AllowDayOverflow)
    $(LREF DateTimeException)
))
))
    License:   $(HTTP www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
    Authors:   $(HTTP jmdavisprog.com, Jonathan M Davis), Ilya Yaroshenko (boost-like and BetterC rework)
+/
module mir.date;

import std.range.primitives : isOutputRange;
import std.traits : isSomeChar, Unqual;

version(D_Exceptions)
version(unittest) import std.exception : assertThrown;

version(test_with_asdf)
unittest
{
    import asdf.serialization;

    assert(Date(2020, 3, 19).serializeToJson == `"2020-03-19"`);
    assert(`"2020-03-19"`.deserialize!Date == Date(2020, 3, 19));
    assert(`"20200319"`.deserialize!Date == Date(2020, 3, 19));
    assert(`"2020-Mar-19"`.deserialize!Date == Date(2020, 3, 19));
}

/++
Returns whether the given value is valid for the given unit type when in a
time point. Naturally, a duration is not held to a particular range, but
the values in a time point are (e.g. a month must be in the range of
1 - 12 inclusive).
Params:
    units = The units of time to validate.
    value = The number to validate.
+/
bool valid(string units)(int value) @safe pure nothrow @nogc
if (units == "months" ||
    units == "hours" ||
    units == "minutes" ||
    units == "seconds")
{
    static if (units == "months")
        return value >= Month.jan && value <= Month.dec;
    else static if (units == "hours")
        return value >= 0 && value <= 23;
    else static if (units == "minutes")
        return value >= 0 && value <= 59;
    else static if (units == "seconds")
        return value >= 0 && value <= 59;
}

///
@safe unittest
{
    assert(valid!"hours"(12));
    assert(!valid!"hours"(32));
    assert(valid!"months"(12));
    assert(!valid!"months"(13));
}

/++
Returns whether the given day is valid for the given year and month.
Params:
    units = The units of time to validate.
    year  = The year of the day to validate.
    month = The month of the day to validate (January is 1).
    day   = The day to validate.
+/
bool valid(string units)(int year, int month, int day) @safe pure nothrow @nogc
    if (units == "days")
{
    return day > 0 && day <= maxDay(year, month);
}

///
@safe pure nothrow @nogc unittest
{
    assert(valid!"days"(2016, 2, 29));
    assert(!valid!"days"(2016, 2, 30));
    assert(valid!"days"(2017, 2, 20));
    assert(!valid!"days"(2017, 2, 29));
}

///
enum AllowDayOverflow : bool
{
    ///
    no,
    ///
    yes
}

/++
Whether the given Gregorian Year is a leap year.
Params:
    year = The year to to be tested.
 +/
bool yearIsLeapYear(int year) @safe pure nothrow @nogc
{
    if (year % 400 == 0)
        return true;
    if (year % 100 == 0)
        return false;
    return year % 4 == 0;
}

///
@safe unittest
{
    foreach (year; [1, 2, 100, 2001, 2002, 2003, 2005, 2006, 2007, 2009, 2010])
    {
        assert(!yearIsLeapYear(year));
        assert(!yearIsLeapYear(-year));
    }

    foreach (year; [0, 4, 8, 400, 800, 1600, 1996, 2000, 2004, 2008, 2012])
    {
        assert(yearIsLeapYear(year));
        assert(yearIsLeapYear(-year));
    }
}

@safe unittest
{
    import std.format : format;
    foreach (year; [1, 2, 3, 5, 6, 7, 100, 200, 300, 500, 600, 700, 1998, 1999,
                    2001, 2002, 2003, 2005, 2006, 2007, 2009, 2010, 2011])
    {
        assert(!yearIsLeapYear(year), format("year: %s.", year));
        assert(!yearIsLeapYear(-year), format("year: %s.", year));
    }

    foreach (year; [0, 4, 8, 400, 800, 1600, 1996, 2000, 2004, 2008, 2012])
    {
        assert(yearIsLeapYear(year), format("year: %s.", year));
        assert(yearIsLeapYear(-year), format("year: %s.", year));
    }
}

///
enum Month : short
{
    ///
    jan = 1,
    ///
    feb,
    ///
    mar,
    ///
    apr,
    ///
    may,
    ///
    jun,
    ///
    jul,
    ///
    aug,
    ///
    sep,
    ///
    oct,
    ///
    nov,
    ///
    dec,
}

version(D_Exceptions)
///
class DateTimeException : Exception
{
    ///
    @nogc @safe pure nothrow this(string msg, string file = __FILE__, size_t line = __LINE__, Throwable nextInChain = null)
    {
        super(msg, file, line, nextInChain);
    }

    /// ditto
    @nogc @safe pure nothrow this(string msg, Throwable nextInChain, string file = __FILE__, size_t line = __LINE__)
    {
        super(msg, file, line, nextInChain);
    }
}

version(D_Exceptions)
{
    private static immutable InvalidMonth = new DateTimeException("Invalid Month");
    private static immutable InvalidDay = new DateTimeException("Invalid Day");
    private static immutable InvalidISOString = new DateTimeException("Invalid ISO String");
    private static immutable InvalidISOExtendedString = new DateTimeException("Invalid ISO Extended String");
    private static immutable InvalidSimpleString = new DateTimeException("Invalid Simple String");
    private static immutable InvalidString = new DateTimeException("Invalid String");
}

@safe unittest
{
    initializeTests();
}

/++
    Represents the 7 days of the Gregorian week (Monday is 0).
  +/
extern(C++, "mir")
enum DayOfWeek
{
    mon = 0, ///
    tue,     ///
    wed,     ///
    thu,     ///
    fri,     ///
    sat,     ///
    sun,     ///
}

///
struct YearMonthDay
{
    short year  = 1;
    Month month = Month.jan;
    ubyte day   = 1;

    // Shares documentation with "years" version.
    @safe pure nothrow @nogc
    ref YearMonthDay add(string units)(long months, AllowDayOverflow allowOverflow = AllowDayOverflow.yes)
        if (units == "months")
    {
        auto years = months / 12;
        months %= 12;
        auto newMonth = month + months;

        if (months < 0)
        {
            if (newMonth < 1)
            {
                newMonth += 12;
                --years;
            }
        }
        else if (newMonth > 12)
        {
            newMonth -= 12;
            ++years;
        }

        year += years;
        month = cast(Month) newMonth;

        immutable currMaxDay = maxDay(year, month);
        immutable overflow = day - currMaxDay;

        if (overflow > 0)
        {
            if (allowOverflow == AllowDayOverflow.yes)
            {
                ++month;
                day = cast(ubyte) overflow;
            }
            else
                day = cast(ubyte) currMaxDay;
        }

        return this;
    }

    // Shares documentation with "years" version.
    @safe pure nothrow @nogc
    ref YearMonthDay add(string units)(long years, AllowDayOverflow allowOverflow = AllowDayOverflow.yes)
        if (units == "years")
    {
        year += years;

        immutable currMaxDay = maxDay(year, month);
        immutable overflow = day - currMaxDay;

        if (overflow > 0)
        {
            if (allowOverflow == AllowDayOverflow.yes)
            {
                ++month;
                day = cast(ubyte) overflow;
            }
            else
                day = cast(ubyte) currMaxDay;
        }
        return this;
    }

    /++
        Day of the year this $(LREF Date) is on.
      +/
    @property int dayOfYear() const @safe pure nothrow @nogc
    {
        if (month >= Month.jan && month <= Month.dec)
        {
            immutable int[] lastDay = isLeapYear ? lastDayLeap : lastDayNonLeap;
            auto monthIndex = month - Month.jan;

            return lastDay[monthIndex] + day;
        }
        assert(0, "Invalid month.");
    }

    ///
    @safe unittest
    {
        assert(YearMonthDay(1999, cast(Month) 1, 1).dayOfYear == 1);
        assert(YearMonthDay(1999, cast(Month) 12, 31).dayOfYear == 365);
        assert(YearMonthDay(2000, cast(Month) 12, 31).dayOfYear == 366);
    }

    /++
        Whether this $(LREF Date) is in a leap year.
     +/
    @property bool isLeapYear() const @safe pure nothrow @nogc
    {
        return yearIsLeapYear(year);
    }

    private void setDayOfYear(bool useExceptions = false)(int days)
    {
        immutable int[] lastDay = isLeapYear ? lastDayLeap : lastDayNonLeap;

        bool dayOutOfRange = days <= 0 || days > (isLeapYear ? daysInLeapYear : daysInYear);

        static if (useExceptions)
        {
            if (dayOutOfRange) throw InvalidDay;
        }
        else
        {
            assert(!dayOutOfRange, "Invalid Day");
        }

        foreach (i; 1 .. lastDay.length)
        {
            if (days <= lastDay[i])
            {
                month = cast(Month)(cast(int) Month.jan + i - 1);
                day = cast(ubyte)(days - lastDay[i - 1]);
                return;
            }
        }
        assert(0, "Invalid day of the year.");
    }

    /++
        The last day in the month that this $(LREF Date) is in.
      +/
    @property ubyte daysInMonth() const @safe pure nothrow @nogc
    {
        return maxDay(year, month);
    }

    /++
        Whether the current year is a date in A.D.
      +/
    @property bool isAD() const @safe pure nothrow @nogc
    {
        return year > 0;
    }
}

/++
    Represents a date in the
    $(HTTP en.wikipedia.org/wiki/Proleptic_Gregorian_calendar, Proleptic
    Gregorian Calendar) ranging from 32,768 B.C. to 32,767 A.D. Positive years
    are A.D. Non-positive years are B.C.

    Year, month, and day are kept separately internally so that $(D Date) is
    optimized for calendar-based operations.

    $(D Date) uses the Proleptic Gregorian Calendar, so it assumes the Gregorian
    leap year calculations for its entire length. As per
    $(HTTP en.wikipedia.org/wiki/ISO_8601, ISO 8601), it treats 1 B.C. as
    year 0, i.e. 1 B.C. is 0, 2 B.C. is -1, etc. Use $(LREF yearBC) to use B.C.
    as a positive integer with 1 B.C. being the year prior to 1 A.D.

    Year 0 is a leap year.
 +/
extern(C++, "boost", "gregorian")
extern(C++, class)
struct date
{
extern(D):
public:

    private enum _julianShift = 1_721_425;

    ///
    uint toHash() @safe pure nothrow @nogc const scope
    {
        return _julianDay;
    }

    /++
        Throws:
            $(LREF DateTimeException) if the resulting
            $(LREF Date) would not be valid.

        Params:
            _year  = Year of the Gregorian Calendar. Positive values are A.D.
                    Non-positive values are B.C. with year 0 being the year
                    prior to 1 A.D.
            _month = Month of the year (January is 1).
            _day   = Day of the month.
     +/
    pragma(inline, false)
    static Date trustedCreate(int _year, int _month, int _day) @safe pure @nogc nothrow
    {
        Date ret;
        immutable int[] lastDay = yearIsLeapYear(_year) ? lastDayLeap : lastDayNonLeap;
        auto monthIndex = _month - Month.jan;

        const dayOfYear = lastDay[monthIndex] + _day;

        if (_month >= Month.jan && _month <= Month.dec) {} else
            assert(0, "Invalid month.");
        if (_year > 0)
        {
            if (_year == 1)
            {
                ret._julianDay = dayOfYear;
                goto R;
            }

            int years = _year - 1;
            auto days = (years / 400) * daysIn400Years;
            years %= 400;

            days += (years / 100) * daysIn100Years;
            years %= 100;

            days += (years / 4) * daysIn4Years;
            years %= 4;

            days += years * daysInYear;

            days += dayOfYear;

            ret._julianDay = days;
        }
        else if (_year == 0)
        {
            ret._julianDay = dayOfYear - daysInLeapYear;
        }
        else
        {
            int years = _year;
            auto days = (years / 400) * daysIn400Years;
            years %= 400;

            days += (years / 100) * daysIn100Years;
            years %= 100;

            days += (years / 4) * daysIn4Years;
            years %= 4;

            if (years < 0)
            {
                days -= daysInLeapYear;
                ++years;

                days += years * daysInYear;

                days -= daysInYear - dayOfYear;
            }
            else
                days -= daysInLeapYear - dayOfYear;

            ret._julianDay = days;
        }
    R:
        ret._julianDay += _julianShift;
        return ret;
    }

    version(D_Exceptions)
    ///
    this(scope const(char)[] str) @safe pure @nogc
    {
        this = fromString(str);
    }

    version(D_Exceptions)
    ///
    this(YearMonthDay ymd) @safe pure @nogc
    {
        with(ymd) this(year, month, day);
    }

    version(D_Exceptions)
    ///
    this(int _year, int _month, int _day) @safe pure @nogc
    {
        if (!valid!"months"(_month))
            throw InvalidMonth;
        if (!valid!"days"(_year, cast(Month) _month, _day))
            throw InvalidDay;
        this = trustedCreate(_year, _month, _day);
    }

    ///
    static bool fromYMD(int _year, int _month, int _day, out Date value) @safe pure nothrow @nogc
    {
        if (valid!"months"(_month) && valid!"days"(_year, cast(Month) _month, _day))
        {
            value = trustedCreate(_year, _month, _day);
            return true;
        }
        return false;
    }

    @safe unittest
    {
        import std.exception : assertNotThrown;
        // assert(Date(0, 12, 31) == Date.init);

        // Test A.D.
        assertThrown!DateTimeException(Date(1, 0, 1));
        assertThrown!DateTimeException(Date(1, 1, 0));
        assertThrown!DateTimeException(Date(1999, 13, 1));
        assertThrown!DateTimeException(Date(1999, 1, 32));
        assertThrown!DateTimeException(Date(1999, 2, 29));
        assertThrown!DateTimeException(Date(2000, 2, 30));
        assertThrown!DateTimeException(Date(1999, 3, 32));
        assertThrown!DateTimeException(Date(1999, 4, 31));
        assertThrown!DateTimeException(Date(1999, 5, 32));
        assertThrown!DateTimeException(Date(1999, 6, 31));
        assertThrown!DateTimeException(Date(1999, 7, 32));
        assertThrown!DateTimeException(Date(1999, 8, 32));
        assertThrown!DateTimeException(Date(1999, 9, 31));
        assertThrown!DateTimeException(Date(1999, 10, 32));
        assertThrown!DateTimeException(Date(1999, 11, 31));
        assertThrown!DateTimeException(Date(1999, 12, 32));

        assertNotThrown!DateTimeException(Date(1999, 1, 31));
        assertNotThrown!DateTimeException(Date(1999, 2, 28));
        assertNotThrown!DateTimeException(Date(2000, 2, 29));
        assertNotThrown!DateTimeException(Date(1999, 3, 31));
        assertNotThrown!DateTimeException(Date(1999, 4, 30));
        assertNotThrown!DateTimeException(Date(1999, 5, 31));
        assertNotThrown!DateTimeException(Date(1999, 6, 30));
        assertNotThrown!DateTimeException(Date(1999, 7, 31));
        assertNotThrown!DateTimeException(Date(1999, 8, 31));
        assertNotThrown!DateTimeException(Date(1999, 9, 30));
        assertNotThrown!DateTimeException(Date(1999, 10, 31));
        assertNotThrown!DateTimeException(Date(1999, 11, 30));
        assertNotThrown!DateTimeException(Date(1999, 12, 31));

        // Test B.C.
        assertNotThrown!DateTimeException(Date(0, 1, 1));
        assertNotThrown!DateTimeException(Date(-1, 1, 1));
        assertNotThrown!DateTimeException(Date(-1, 12, 31));
        assertNotThrown!DateTimeException(Date(-1, 2, 28));
        assertNotThrown!DateTimeException(Date(-4, 2, 29));

        assertThrown!DateTimeException(Date(-1, 2, 29));
        assertThrown!DateTimeException(Date(-2, 2, 29));
        assertThrown!DateTimeException(Date(-3, 2, 29));
    }


    /++
        Params:
            day = Julian day.
     +/
    this(int day) @safe pure nothrow @nogc
    {
        _julianDay = day;
    }

    @safe unittest
    {
        import std.range : chain;

        // Test A.D.
        // foreach (gd; chain(testGregDaysBC, testGregDaysAD))
        //     assert(Date(gd.day) == gd.date);
    }


    /++
        Compares this $(LREF Date) with the given $(LREF Date).

        Returns:
            $(BOOKTABLE,
            $(TR $(TD this &lt; rhs) $(TD &lt; 0))
            $(TR $(TD this == rhs) $(TD 0))
            $(TR $(TD this &gt; rhs) $(TD &gt; 0))
            )
     +/
    int opCmp(Date rhs) const @safe pure nothrow @nogc
    {
        return this._julianDay - rhs._julianDay;
    }

    @safe unittest
    {
        // Test A.D.
        // assert(Date(0, 12, 31).opCmp(Date.init) == 0);

        assert(Date(1999, 1, 1).opCmp(Date(1999, 1, 1)) == 0);
        assert(Date(1, 7, 1).opCmp(Date(1, 7, 1)) == 0);
        assert(Date(1, 1, 6).opCmp(Date(1, 1, 6)) == 0);

        assert(Date(1999, 7, 1).opCmp(Date(1999, 7, 1)) == 0);
        assert(Date(1999, 7, 6).opCmp(Date(1999, 7, 6)) == 0);

        assert(Date(1, 7, 6).opCmp(Date(1, 7, 6)) == 0);

        assert(Date(1999, 7, 6).opCmp(Date(2000, 7, 6)) < 0);
        assert(Date(2000, 7, 6).opCmp(Date(1999, 7, 6)) > 0);
        assert(Date(1999, 7, 6).opCmp(Date(1999, 8, 6)) < 0);
        assert(Date(1999, 8, 6).opCmp(Date(1999, 7, 6)) > 0);
        assert(Date(1999, 7, 6).opCmp(Date(1999, 7, 7)) < 0);
        assert(Date(1999, 7, 7).opCmp(Date(1999, 7, 6)) > 0);

        assert(Date(1999, 8, 7).opCmp(Date(2000, 7, 6)) < 0);
        assert(Date(2000, 8, 6).opCmp(Date(1999, 7, 7)) > 0);
        assert(Date(1999, 7, 7).opCmp(Date(2000, 7, 6)) < 0);
        assert(Date(2000, 7, 6).opCmp(Date(1999, 7, 7)) > 0);
        assert(Date(1999, 7, 7).opCmp(Date(1999, 8, 6)) < 0);
        assert(Date(1999, 8, 6).opCmp(Date(1999, 7, 7)) > 0);

        // Test B.C.
        assert(Date(0, 1, 1).opCmp(Date(0, 1, 1)) == 0);
        assert(Date(-1, 1, 1).opCmp(Date(-1, 1, 1)) == 0);
        assert(Date(-1, 7, 1).opCmp(Date(-1, 7, 1)) == 0);
        assert(Date(-1, 1, 6).opCmp(Date(-1, 1, 6)) == 0);

        assert(Date(-1999, 7, 1).opCmp(Date(-1999, 7, 1)) == 0);
        assert(Date(-1999, 7, 6).opCmp(Date(-1999, 7, 6)) == 0);

        assert(Date(-1, 7, 6).opCmp(Date(-1, 7, 6)) == 0);

        assert(Date(-2000, 7, 6).opCmp(Date(-1999, 7, 6)) < 0);
        assert(Date(-1999, 7, 6).opCmp(Date(-2000, 7, 6)) > 0);
        assert(Date(-1999, 7, 6).opCmp(Date(-1999, 8, 6)) < 0);
        assert(Date(-1999, 8, 6).opCmp(Date(-1999, 7, 6)) > 0);
        assert(Date(-1999, 7, 6).opCmp(Date(-1999, 7, 7)) < 0);
        assert(Date(-1999, 7, 7).opCmp(Date(-1999, 7, 6)) > 0);

        assert(Date(-2000, 8, 6).opCmp(Date(-1999, 7, 7)) < 0);
        assert(Date(-1999, 8, 7).opCmp(Date(-2000, 7, 6)) > 0);
        assert(Date(-2000, 7, 6).opCmp(Date(-1999, 7, 7)) < 0);
        assert(Date(-1999, 7, 7).opCmp(Date(-2000, 7, 6)) > 0);
        assert(Date(-1999, 7, 7).opCmp(Date(-1999, 8, 6)) < 0);
        assert(Date(-1999, 8, 6).opCmp(Date(-1999, 7, 7)) > 0);

        // Test Both
        assert(Date(-1999, 7, 6).opCmp(Date(1999, 7, 6)) < 0);
        assert(Date(1999, 7, 6).opCmp(Date(-1999, 7, 6)) > 0);

        assert(Date(-1999, 8, 6).opCmp(Date(1999, 7, 6)) < 0);
        assert(Date(1999, 7, 6).opCmp(Date(-1999, 8, 6)) > 0);

        assert(Date(-1999, 7, 7).opCmp(Date(1999, 7, 6)) < 0);
        assert(Date(1999, 7, 6).opCmp(Date(-1999, 7, 7)) > 0);

        assert(Date(-1999, 8, 7).opCmp(Date(1999, 7, 6)) < 0);
        assert(Date(1999, 7, 6).opCmp(Date(-1999, 8, 7)) > 0);

        assert(Date(-1999, 8, 6).opCmp(Date(1999, 6, 6)) < 0);
        assert(Date(1999, 6, 8).opCmp(Date(-1999, 7, 6)) > 0);

        auto date = Date(1999, 7, 6);
        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(date.opCmp(date) == 0);
        assert(date.opCmp(cdate) == 0);
        assert(date.opCmp(idate) == 0);
        assert(cdate.opCmp(date) == 0);
        assert(cdate.opCmp(cdate) == 0);
        assert(cdate.opCmp(idate) == 0);
        assert(idate.opCmp(date) == 0);
        assert(idate.opCmp(cdate) == 0);
        assert(idate.opCmp(idate) == 0);
    }

    /++
        Day of the week this $(LREF Date) is on.
      +/
    @property DayOfWeek dayOfWeek() const @safe pure nothrow @nogc
    {
        return getDayOfWeek(_julianDay);
    }

    @safe unittest
    {
        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.dayOfWeek == DayOfWeek.tue);
        static assert(!__traits(compiles, cdate.dayOfWeek = DayOfWeek.sun));
        assert(idate.dayOfWeek == DayOfWeek.tue);
        static assert(!__traits(compiles, idate.dayOfWeek = DayOfWeek.sun));
    }

    /++
        The Xth day of the Gregorian Calendar that this $(LREF Date) is on.
     +/
    @property int dayOfGregorianCal() const @safe pure nothrow @nogc
    {
        return _julianDay - _julianShift;
    }

    ///
    @safe unittest
    {
        assert(Date(1, 1, 1).dayOfGregorianCal == 1);
        assert(Date(1, 12, 31).dayOfGregorianCal == 365);
        assert(Date(2, 1, 1).dayOfGregorianCal == 366);

        assert(Date(0, 12, 31).dayOfGregorianCal == 0);
        assert(Date(0, 1, 1).dayOfGregorianCal == -365);
        assert(Date(-1, 12, 31).dayOfGregorianCal == -366);

        assert(Date(2000, 1, 1).dayOfGregorianCal == 730_120);
        assert(Date(2010, 12, 31).dayOfGregorianCal == 734_137);
    }

    @safe unittest
    {
        import std.range : chain;

        foreach (gd; chain(testGregDaysBC, testGregDaysAD))
            assert(gd.date.dayOfGregorianCal == gd.day);

        auto date = Date(1999, 7, 6);
        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(date.dayOfGregorianCal == 729_941);
        assert(cdate.dayOfGregorianCal == 729_941);
        assert(idate.dayOfGregorianCal == 729_941);
    }

    /++
        The Xth day of the Gregorian Calendar that this $(LREF Date) is on.

        Params:
            day = The day of the Gregorian Calendar to set this $(LREF Date) to.
     +/
    @property void dayOfGregorianCal(int day) @safe pure nothrow @nogc
    {
        this = Date(day + _julianShift);
    }

    ///
    @safe unittest
    {
        auto date = Date.init;
        date.dayOfGregorianCal = 1;
        assert(date == Date(1, 1, 1));

        date.dayOfGregorianCal = 365;
        assert(date == Date(1, 12, 31));

        date.dayOfGregorianCal = 366;
        assert(date == Date(2, 1, 1));

        date.dayOfGregorianCal = 0;
        assert(date == Date(0, 12, 31));

        date.dayOfGregorianCal = -365;
        assert(date == Date(-0, 1, 1));

        date.dayOfGregorianCal = -366;
        assert(date == Date(-1, 12, 31));

        date.dayOfGregorianCal = 730_120;
        assert(date == Date(2000, 1, 1));

        date.dayOfGregorianCal = 734_137;
        assert(date == Date(2010, 12, 31));
    }

    @safe unittest
    {
        auto date = Date(1999, 7, 6);
        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        date.dayOfGregorianCal = 187;
        assert(date.dayOfGregorianCal == 187);
        static assert(!__traits(compiles, cdate.dayOfGregorianCal = 187));
        static assert(!__traits(compiles, idate.dayOfGregorianCal = 187));
    }

    private enum uint _startDict = Date(1900, 1, 1)._julianDay; // [
    private enum uint _endDict = Date(2040, 1, 1)._julianDay; // )
    static immutable _dict = ()
    {
        YearMonthDay[Date._endDict - Date._startDict] dict;
        foreach (uint i; 0 .. dict.length)
            dict[i] = Date(i + Date._startDict).yearMonthDayImpl;
        return dict;
    }();

    YearMonthDay yearMonthDay() const @safe pure nothrow @nogc @property
    {
        uint day = _julianDay;
        if (day < _endDict)
        {
            import mir.checkedint: subu;
            bool overflow;
            auto index = subu(day, _startDict, overflow);
            if (!overflow)
                return _dict[index];
        }
        return yearMonthDayImpl;
    }

    pragma(inline, false)
    YearMonthDay yearMonthDayImpl() const @safe pure nothrow @nogc @property
    {
        YearMonthDay ymd;
        int days = dayOfGregorianCal;
        with(ymd)
        if (days > 0)
        {
            int years = (days / daysIn400Years) * 400 + 1;
            days %= daysIn400Years;

            {
                immutable tempYears = days / daysIn100Years;

                if (tempYears == 4)
                {
                    years += 300;
                    days -= daysIn100Years * 3;
                }
                else
                {
                    years += tempYears * 100;
                    days %= daysIn100Years;
                }
            }

            years += (days / daysIn4Years) * 4;
            days %= daysIn4Years;

            {
                immutable tempYears = days / daysInYear;

                if (tempYears == 4)
                {
                    years += 3;
                    days -= daysInYear * 3;
                }
                else
                {
                    years += tempYears;
                    days %= daysInYear;
                }
            }

            if (days == 0)
            {
                year = cast(short)(years - 1);
                month = Month.dec;
                day = 31;
            }
            else
            {
                year = cast(short) years;

                setDayOfYear(days);
            }
        }
        else if (days <= 0 && -days < daysInLeapYear)
        {
            year = 0;

            setDayOfYear(daysInLeapYear + days);
        }
        else
        {
            days += daysInLeapYear - 1;
            int years = (days / daysIn400Years) * 400 - 1;
            days %= daysIn400Years;

            {
                immutable tempYears = days / daysIn100Years;

                if (tempYears == -4)
                {
                    years -= 300;
                    days += daysIn100Years * 3;
                }
                else
                {
                    years += tempYears * 100;
                    days %= daysIn100Years;
                }
            }

            years += (days / daysIn4Years) * 4;
            days %= daysIn4Years;

            {
                immutable tempYears = days / daysInYear;

                if (tempYears == -4)
                {
                    years -= 3;
                    days += daysInYear * 3;
                }
                else
                {
                    years += tempYears;
                    days %= daysInYear;
                }
            }

            if (days == 0)
            {
                year = cast(short)(years + 1);
                month = Month.jan;
                day = 1;
            }
            else
            {
                year = cast(short) years;
                immutable newDoY = (yearIsLeapYear(year) ? daysInLeapYear : daysInYear) + days + 1;

                setDayOfYear(newDoY);
            }
        }
        return ymd;
    }

    /++
     $(LREF Date) for the last day in the quarter that this $(LREF Date) is in.
    +/
    @property Date endOfQuarter() const @safe pure nothrow @nogc
    {
        with(yearMonthDay)
        {
            int d = _julianDay - day;
            final switch (month) with(Month)
            {
                case jan: d += maxDay(year, jan); goto case;
                case feb: d += maxDay(year, feb); goto case;
                case mar: d += maxDay(year, mar); break;

                case apr: d += maxDay(year, apr); goto case;
                case may: d += maxDay(year, may); goto case;
                case jun: d += maxDay(year, jun); break;

                case jul: d += maxDay(year, jul); goto case;
                case aug: d += maxDay(year, aug); goto case;
                case sep: d += maxDay(year, sep); break;

                case oct: d += maxDay(year, oct); goto case;
                case nov: d += maxDay(year, nov); goto case;
                case dec: d += maxDay(year, dec); break;
            }
            return Date(d);
        }
    }

    ///
    @safe unittest
    {
        assert(Date(1999, 1, 6).endOfQuarter == Date(1999, 3, 31));
        assert(Date(1999, 2, 7).endOfQuarter == Date(1999, 3, 31));
        assert(Date(2000, 2, 7).endOfQuarter == Date(2000, 3, 31));
        assert(Date(2000, 6, 4).endOfQuarter == Date(2000, 6, 30));
    }

    /++
     $(LREF Date) for the last day in the month that this $(LREF Date) is in.
    +/
    @property Date endOfMonth() const @safe pure nothrow @nogc
    {
        with(yearMonthDay)
            return Date(_julianDay + maxDay(year, month) - day);
    }

    ///
    @safe unittest
    {
        assert(Date(1999, 1, 6).endOfMonth == Date(1999, 1, 31));
        assert(Date(1999, 2, 7).endOfMonth == Date(1999, 2, 28));
        assert(Date(2000, 2, 7).endOfMonth == Date(2000, 2, 29));
        assert(Date(2000, 6, 4).endOfMonth == Date(2000, 6, 30));
    }

    @safe unittest
    {
        // Test A.D.
        assert(Date(1999, 1, 1).endOfMonth == Date(1999, 1, 31));
        assert(Date(1999, 2, 1).endOfMonth == Date(1999, 2, 28));
        assert(Date(2000, 2, 1).endOfMonth == Date(2000, 2, 29));
        assert(Date(1999, 3, 1).endOfMonth == Date(1999, 3, 31));
        assert(Date(1999, 4, 1).endOfMonth == Date(1999, 4, 30));
        assert(Date(1999, 5, 1).endOfMonth == Date(1999, 5, 31));
        assert(Date(1999, 6, 1).endOfMonth == Date(1999, 6, 30));
        assert(Date(1999, 7, 1).endOfMonth == Date(1999, 7, 31));
        assert(Date(1999, 8, 1).endOfMonth == Date(1999, 8, 31));
        assert(Date(1999, 9, 1).endOfMonth == Date(1999, 9, 30));
        assert(Date(1999, 10, 1).endOfMonth == Date(1999, 10, 31));
        assert(Date(1999, 11, 1).endOfMonth == Date(1999, 11, 30));
        assert(Date(1999, 12, 1).endOfMonth == Date(1999, 12, 31));

        // Test B.C.
        assert(Date(-1999, 1, 1).endOfMonth == Date(-1999, 1, 31));
        assert(Date(-1999, 2, 1).endOfMonth == Date(-1999, 2, 28));
        assert(Date(-2000, 2, 1).endOfMonth == Date(-2000, 2, 29));
        assert(Date(-1999, 3, 1).endOfMonth == Date(-1999, 3, 31));
        assert(Date(-1999, 4, 1).endOfMonth == Date(-1999, 4, 30));
        assert(Date(-1999, 5, 1).endOfMonth == Date(-1999, 5, 31));
        assert(Date(-1999, 6, 1).endOfMonth == Date(-1999, 6, 30));
        assert(Date(-1999, 7, 1).endOfMonth == Date(-1999, 7, 31));
        assert(Date(-1999, 8, 1).endOfMonth == Date(-1999, 8, 31));
        assert(Date(-1999, 9, 1).endOfMonth == Date(-1999, 9, 30));
        assert(Date(-1999, 10, 1).endOfMonth == Date(-1999, 10, 31));
        assert(Date(-1999, 11, 1).endOfMonth == Date(-1999, 11, 30));
        assert(Date(-1999, 12, 1).endOfMonth == Date(-1999, 12, 31));

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        static assert(!__traits(compiles, cdate.endOfMonth = Date(1999, 7, 30)));
        static assert(!__traits(compiles, idate.endOfMonth = Date(1999, 7, 30)));
    }

    ///
    int opBinary(string op : "-")(Date lhs) const
    {
        return _julianDay - lhs._julianDay;
    }

    ///
    Date opBinary(string op : "+")(int lhs) const
    {
        return Date(_julianDay + lhs);
    }

    ///
    Date opBinaryRight(string op : "+")(int lhs) const
    {
        return Date(_julianDay + lhs);
    }

    ///
    Date opBinary(string op : "-")(int lhs) const
    {
        return Date(_julianDay - lhs);
    }

    const nothrow @nogc pure @safe
    Date add(string units)(long amount, AllowDayOverflow allowOverflow = AllowDayOverflow.yes)
    {
        with(yearMonthDay.add!units(amount)) return trustedCreate(year, month, day);
    }

    /++
        The $(HTTP en.wikipedia.org/wiki/Julian_day, Julian day) for this
        $(LREF Date) at noon (since the Julian day changes at noon).
      +/
    @property int julianDay() const @safe pure nothrow @nogc
    {
        return _julianDay;
    }

    @safe unittest
    {
        assert(Date(-4713, 11, 24).julianDay == 0);
        assert(Date(0, 12, 31).julianDay == _julianShift);
        assert(Date(1, 1, 1).julianDay == 1_721_426);
        assert(Date(1582, 10, 15).julianDay == 2_299_161);
        assert(Date(1858, 11, 17).julianDay == 2_400_001);
        assert(Date(1982, 1, 4).julianDay == 2_444_974);
        assert(Date(1996, 3, 31).julianDay == 2_450_174);
        assert(Date(2010, 8, 24).julianDay == 2_455_433);

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.julianDay == 2_451_366);
        assert(idate.julianDay == 2_451_366);
    }


    /++
        The modified $(HTTP en.wikipedia.org/wiki/Julian_day, Julian day) for
        any time on this date (since, the modified Julian day changes at
        midnight).
      +/
    @property long modJulianDay() const @safe pure nothrow @nogc
    {
        return julianDay - 2_400_001;
    }

    @safe unittest
    {
        assert(Date(1858, 11, 17).modJulianDay == 0);
        assert(Date(2010, 8, 24).modJulianDay == 55_432);

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.modJulianDay == 51_365);
        assert(idate.modJulianDay == 51_365);
    }

    version(D_BetterC){} else
    private string toStringImpl(alias fun)() const @safe pure nothrow
    {
        import mir.small_string : SmallString;
        SmallString!16 w;
        try
            fun(w);
        catch (Exception e)
            assert(0, __traits(identifier, fun) ~ " threw.");
        return w.asArray.idup;
    }

    version(D_BetterC){} else
    /++
        Converts this $(LREF Date) to a string with the format `YYYYMMDD`.
        If `writer` is set, the resulting string will be written directly
        to it.

        Returns:
            A `string` when not using an output range; `void` otherwise.
      +/
    string toISOString() const @safe pure nothrow
    {
        return toStringImpl!toISOString;
    }

    ///
    @safe unittest
    {
        assert(Date(2010, 7, 4).toISOString() == "20100704");
        assert(Date(1998, 12, 25).toISOString() == "19981225");
        assert(Date(0, 1, 5).toISOString() == "00000105");
        assert(Date(-4, 1, 5).toISOString() == "-00040105", Date(-4, 1, 5).toISOString());
    }

    @safe unittest
    {
        // Test A.D.
        assert(Date(9, 12, 4).toISOString() == "00091204");
        assert(Date(99, 12, 4).toISOString() == "00991204");
        assert(Date(999, 12, 4).toISOString() == "09991204");
        assert(Date(9999, 7, 4).toISOString() == "99990704");
        assert(Date(10000, 10, 20).toISOString() == "+100001020");

        // Test B.C.
        assert(Date(0, 12, 4).toISOString() == "00001204");
        assert(Date(-9, 12, 4).toISOString() == "-00091204");
        assert(Date(-99, 12, 4).toISOString() == "-00991204");
        assert(Date(-999, 12, 4).toISOString() == "-09991204");
        assert(Date(-9999, 7, 4).toISOString() == "-99990704");
        assert(Date(-10000, 10, 20).toISOString() == "-100001020");

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.toISOString() == "19990706");
        assert(idate.toISOString() == "19990706");
    }

    /// ditto
    void toISOString(W)(scope ref W w) const scope
        if (isOutputRange!(W, char))
    {
        import mir.format: printZeroPad;
        with(yearMonthDay)
        {
            if (year >= 10_000)
                w.put('+');
            w.printZeroPad(year, year >= 0 ? year < 10_000 ? 4 : 5 : year > -10_000 ? 5 : 6);
            w.printZeroPad(cast(uint)month, 2);
            w.printZeroPad(day, 2);
        }
    }

    @safe unittest
    {
        auto date = Date(1999, 7, 6);
        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(date.toString);
        assert(cdate.toString);
        assert(idate.toString);
    }

    version(D_BetterC){} else
    /++
    Converts this $(LREF Date) to a string with the format `YYYY-MM-DD`.
    If `writer` is set, the resulting string will be written directly
    to it.

    Returns:
        A `string` when not using an output range; `void` otherwise.
      +/
    string toISOExtString() const @safe pure nothrow
    {
        return toStringImpl!toISOExtString;
    }

    ///ditto
    alias toString = toISOExtString;

    ///
    @safe unittest
    {
        assert(Date(2010, 7, 4).toISOExtString() == "2010-07-04");
        assert(Date(1998, 12, 25).toISOExtString() == "1998-12-25");
        assert(Date(0, 1, 5).toISOExtString() == "0000-01-05");
        assert(Date(-4, 1, 5).toISOExtString() == "-0004-01-05");
    }

    @safe pure unittest
    {
        import std.array : appender;

        auto w = appender!(char[])();
        Date(2010, 7, 4).toISOString(w);
        assert(w.data == "20100704");
        w.clear();
        Date(1998, 12, 25).toISOString(w);
        assert(w.data == "19981225");
    }

    @safe unittest
    {
        // Test A.D.
        assert(Date(9, 12, 4).toISOExtString() == "0009-12-04");
        assert(Date(99, 12, 4).toISOExtString() == "0099-12-04");
        assert(Date(999, 12, 4).toISOExtString() == "0999-12-04");
        assert(Date(9999, 7, 4).toISOExtString() == "9999-07-04");
        assert(Date(10000, 10, 20).toISOExtString() == "+10000-10-20");

        // Test B.C.
        assert(Date(0, 12, 4).toISOExtString() == "0000-12-04");
        assert(Date(-9, 12, 4).toISOExtString() == "-0009-12-04");
        assert(Date(-99, 12, 4).toISOExtString() == "-0099-12-04");
        assert(Date(-999, 12, 4).toISOExtString() == "-0999-12-04");
        assert(Date(-9999, 7, 4).toISOExtString() == "-9999-07-04");
        assert(Date(-10000, 10, 20).toISOExtString() == "-10000-10-20");

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.toISOExtString() == "1999-07-06");
        assert(idate.toISOExtString() == "1999-07-06");
    }

    /// ditto
    void toISOExtString(W)(scope ref W w) const scope
        if (isOutputRange!(W, char))
    {
        import mir.format: printZeroPad;
        with(yearMonthDay)
        {
            if (year >= 10_000)
                w.put('+');
            w.printZeroPad(year, year >= 0 ? year < 10_000 ? 4 : 5 : year > -10_000 ? 5 : 6);
            w.put('-');
            w.printZeroPad(cast(uint)month, 2);
            w.put('-');
            w.printZeroPad(day, 2);
        }
    }

    @safe pure unittest
    {
        import std.array : appender;

        auto w = appender!(char[])();
        Date(2010, 7, 4).toISOExtString(w);
        assert(w.data == "2010-07-04");
        w.clear();
        Date(-4, 1, 5).toISOExtString(w);
        assert(w.data == "-0004-01-05");
    }

    version(D_BetterC){} else
    /++
        Converts this $(LREF Date) to a string with the format `YYYY-Mon-DD`.
        If `writer` is set, the resulting string will be written directly
        to it.

        Returns:
            A `string` when not using an output range; `void` otherwise.
      +/
    string toSimpleString() const @safe pure nothrow
    {
        return toStringImpl!toSimpleString;
    }

    ///
    @safe unittest
    {
        assert(Date(2010, 7, 4).toSimpleString() == "2010-Jul-04");
        assert(Date(1998, 12, 25).toSimpleString() == "1998-Dec-25");
        assert(Date(0, 1, 5).toSimpleString() == "0000-Jan-05");
        assert(Date(-4, 1, 5).toSimpleString() == "-0004-Jan-05");
    }

    @safe unittest
    {
        // Test A.D.
        assert(Date(9, 12, 4).toSimpleString() == "0009-Dec-04");
        assert(Date(99, 12, 4).toSimpleString() == "0099-Dec-04");
        assert(Date(999, 12, 4).toSimpleString() == "0999-Dec-04");
        assert(Date(9999, 7, 4).toSimpleString() == "9999-Jul-04");
        assert(Date(10000, 10, 20).toSimpleString() == "+10000-Oct-20");

        // Test B.C.
        assert(Date(0, 12, 4).toSimpleString() == "0000-Dec-04");
        assert(Date(-9, 12, 4).toSimpleString() == "-0009-Dec-04");
        assert(Date(-99, 12, 4).toSimpleString() == "-0099-Dec-04");
        assert(Date(-999, 12, 4).toSimpleString() == "-0999-Dec-04");
        assert(Date(-9999, 7, 4).toSimpleString() == "-9999-Jul-04");
        assert(Date(-10000, 10, 20).toSimpleString() == "-10000-Oct-20");

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.toSimpleString() == "1999-Jul-06");
        assert(idate.toSimpleString() == "1999-Jul-06");
    }

    /// ditto
    void toSimpleString(W)(scope ref W w) const scope
        if (isOutputRange!(W, char))
    {
        import mir.format: printZeroPad;
        with(yearMonthDay)
        {
            if (year >= 10_000)
                w.put('+');
            w.printZeroPad(year, year >= 0 ? year < 10_000 ? 4 : 5 : year > -10_000 ? 5 : 6);
            w.put('-');
            w.put(month.monthToString);
            w.put('-');
            w.printZeroPad(day, 2);
        }
    }

    @safe pure unittest
    {
        import std.array : appender;

        auto w = appender!(char[])();
        Date(9, 12, 4).toSimpleString(w);
        assert(w.data == "0009-Dec-04");
        w.clear();
        Date(-10000, 10, 20).toSimpleString(w);
        assert(w.data == "-10000-Oct-20");
    }

    /++
    Creates a $(LREF Date) from a string with the format YYYYMMDD.

    Params:
        str = A string formatted in the way that $(LREF .date.toISOString) formats dates.
        value = (optional) result value.

    Throws:
        $(LREF DateTimeException) if the given string is
        not in the correct format or if the resulting $(LREF Date) would not
        be valid. Two arguments overload is `nothrow`.
    Returns:
        `bool` on success for two arguments overload, and the resulting date for single argument overdload.
    +/
    static bool fromISOString(C)(scope const(C)[] str, out Date value) @safe pure nothrow @nogc
        if (isSomeChar!C)
    {
        import mir.parse: fromString;

        if (str.length < 8)
            return false;

        auto yearStr = str[0 .. $ - 4];

        if ((yearStr[0] == '+' || yearStr[0] == '-') != (yearStr.length > 4))
            return false;

        uint day, month;
        int year;

        return 
            fromString(str[$ - 2 .. $], day)
         && fromString(str[$ - 4 .. $ - 2], month)
         && fromString(yearStr, year)
         && fromYMD(year, month, day, value);
    }

    /// ditto
    static Date fromISOString(C)(scope const(C)[] str) @safe pure
        if (isSomeChar!C)
    {
        Date ret;
        if (fromISOString(str, ret))
            return ret;
        throw InvalidISOString;
    }

    ///
    @safe unittest
    {
        assert(Date.fromISOString("20100704") == Date(2010, 7, 4));
        assert(Date.fromISOString("19981225") == Date(1998, 12, 25));
        assert(Date.fromISOString("00000105") == Date(0, 1, 5));
        assert(Date.fromISOString("-00040105") == Date(-4, 1, 5));
    }

    @safe unittest
    {
        assertThrown!DateTimeException(Date.fromISOString(""));
        assertThrown!DateTimeException(Date.fromISOString("990704"));
        assertThrown!DateTimeException(Date.fromISOString("0100704"));
        assertThrown!DateTimeException(Date.fromISOString("2010070"));
        assertThrown!DateTimeException(Date.fromISOString("120100704"));
        assertThrown!DateTimeException(Date.fromISOString("-0100704"));
        assertThrown!DateTimeException(Date.fromISOString("+0100704"));
        assertThrown!DateTimeException(Date.fromISOString("2010070a"));
        assertThrown!DateTimeException(Date.fromISOString("20100a04"));
        assertThrown!DateTimeException(Date.fromISOString("2010a704"));

        assertThrown!DateTimeException(Date.fromISOString("99-07-04"));
        assertThrown!DateTimeException(Date.fromISOString("010-07-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-07-0"));
        assertThrown!DateTimeException(Date.fromISOString("12010-07-04"));
        assertThrown!DateTimeException(Date.fromISOString("-010-07-04"));
        assertThrown!DateTimeException(Date.fromISOString("+010-07-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-07-0a"));
        assertThrown!DateTimeException(Date.fromISOString("2010-0a-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-a7-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010/07/04"));
        assertThrown!DateTimeException(Date.fromISOString("2010/7/04"));
        assertThrown!DateTimeException(Date.fromISOString("2010/7/4"));
        assertThrown!DateTimeException(Date.fromISOString("2010/07/4"));
        assertThrown!DateTimeException(Date.fromISOString("2010-7-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-7-4"));
        assertThrown!DateTimeException(Date.fromISOString("2010-07-4"));

        assertThrown!DateTimeException(Date.fromISOString("99Jul04"));
        assertThrown!DateTimeException(Date.fromISOString("010Jul04"));
        assertThrown!DateTimeException(Date.fromISOString("2010Jul0"));
        assertThrown!DateTimeException(Date.fromISOString("12010Jul04"));
        assertThrown!DateTimeException(Date.fromISOString("-010Jul04"));
        assertThrown!DateTimeException(Date.fromISOString("+010Jul04"));
        assertThrown!DateTimeException(Date.fromISOString("2010Jul0a"));
        assertThrown!DateTimeException(Date.fromISOString("2010Jua04"));
        assertThrown!DateTimeException(Date.fromISOString("2010aul04"));

        assertThrown!DateTimeException(Date.fromISOString("99-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOString("010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-Jul-0"));
        assertThrown!DateTimeException(Date.fromISOString("12010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOString("-010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOString("+010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-Jul-0a"));
        assertThrown!DateTimeException(Date.fromISOString("2010-Jua-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-Jal-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-aul-04"));

        assertThrown!DateTimeException(Date.fromISOString("2010-07-04"));
        assertThrown!DateTimeException(Date.fromISOString("2010-Jul-04"));

        assert(Date.fromISOString("19990706") == Date(1999, 7, 6));
        assert(Date.fromISOString("-19990706") == Date(-1999, 7, 6));
        assert(Date.fromISOString("+019990706") == Date(1999, 7, 6));
        assert(Date.fromISOString("19990706") == Date(1999, 7, 6));
    }

    // bug# 17801
    @safe unittest
    {
        import std.conv : to;
        import std.meta : AliasSeq;
        static foreach (C; AliasSeq!(char, wchar, dchar))
        {
            static foreach (S; AliasSeq!(C[], const(C)[], immutable(C)[]))
                assert(Date.fromISOString(to!S("20121221")) == Date(2012, 12, 21));
        }
    }

    /++
    Creates a $(LREF Date) from a string with the format YYYY-MM-DD.

    Params:
        str = A string formatted in the way that $(LREF .date.toISOExtString) formats dates.
        value = (optional) result value.

    Throws:
        $(LREF DateTimeException) if the given string is
        not in the correct format or if the resulting $(LREF Date) would not
        be valid. Two arguments overload is `nothrow`.
    Returns:
        `bool` on success for two arguments overload, and the resulting date for single argument overdload.
    +/
    static bool fromISOExtString(C)(scope const(C)[] str, out Date value) @safe pure nothrow @nogc
        if (isSomeChar!C)
    {
        import mir.parse: fromString;

        if (str.length < 10 || str[$-3] != '-' || str[$-6] != '-')
            return false;

        auto yearStr = str[0 .. $ - 6];

        if ((yearStr[0] == '+' || yearStr[0] == '-') != (yearStr.length > 4))
            return false;

        uint day, month;
        int year;

        return
            fromString(str[$ - 2 .. $], day)
         && fromString(str[$ - 5 .. $ - 3], month)
         && fromString(yearStr, year)
         && fromYMD(year, month, day, value);
    }

    /// ditto
    static Date fromISOExtString(C)(scope const(C)[] str) @safe pure
        if (isSomeChar!C)
    {
        Date ret;
        if (fromISOExtString(str, ret))
            return ret;
        throw InvalidISOExtendedString;
    }

    ///
    @safe unittest
    {
        assert(Date.fromISOExtString("2010-07-04") == Date(2010, 7, 4));
        assert(Date.fromISOExtString("1998-12-25") == Date(1998, 12, 25));
        assert(Date.fromISOExtString("0000-01-05") == Date(0, 1, 5));
        assert(Date.fromISOExtString("-0004-01-05") == Date(-4, 1, 5));
    }

    @safe unittest
    {
        assertThrown!DateTimeException(Date.fromISOExtString(""));
        assertThrown!DateTimeException(Date.fromISOExtString("990704"));
        assertThrown!DateTimeException(Date.fromISOExtString("0100704"));
        assertThrown!DateTimeException(Date.fromISOExtString("120100704"));
        assertThrown!DateTimeException(Date.fromISOExtString("-0100704"));
        assertThrown!DateTimeException(Date.fromISOExtString("+0100704"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010070a"));
        assertThrown!DateTimeException(Date.fromISOExtString("20100a04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010a704"));

        assertThrown!DateTimeException(Date.fromISOExtString("99-07-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("010-07-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-07-0"));
        assertThrown!DateTimeException(Date.fromISOExtString("12010-07-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("-010-07-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("+010-07-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-07-0a"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-0a-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-a7-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010/07/04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010/7/04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010/7/4"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010/07/4"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-7-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-7-4"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-07-4"));

        assertThrown!DateTimeException(Date.fromISOExtString("99Jul04"));
        assertThrown!DateTimeException(Date.fromISOExtString("010Jul04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010Jul0"));
        assertThrown!DateTimeException(Date.fromISOExtString("12010Jul04"));
        assertThrown!DateTimeException(Date.fromISOExtString("-010Jul04"));
        assertThrown!DateTimeException(Date.fromISOExtString("+010Jul04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010Jul0a"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010Jua04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010aul04"));

        assertThrown!DateTimeException(Date.fromISOExtString("99-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-Jul-0"));
        assertThrown!DateTimeException(Date.fromISOExtString("12010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("-010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("+010-Jul-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-Jul-0a"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-Jua-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-Jal-04"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-aul-04"));

        assertThrown!DateTimeException(Date.fromISOExtString("20100704"));
        assertThrown!DateTimeException(Date.fromISOExtString("2010-Jul-04"));

        assert(Date.fromISOExtString("1999-07-06") == Date(1999, 7, 6));
        assert(Date.fromISOExtString("-1999-07-06") == Date(-1999, 7, 6));
        assert(Date.fromISOExtString("+01999-07-06") == Date(1999, 7, 6));
    }

    // bug# 17801
    @safe unittest
    {
        import std.conv : to;
        import std.meta : AliasSeq;
        static foreach (C; AliasSeq!(char, wchar, dchar))
        {
            static foreach (S; AliasSeq!(C[], const(C)[], immutable(C)[]))
                assert(Date.fromISOExtString(to!S("2012-12-21")) == Date(2012, 12, 21));
        }
    }


    /++
    Creates a $(LREF Date) from a string with the format YYYY-Mon-DD.

    Params:
        str = A string formatted in the way that $(LREF .date.toSimpleString) formats dates. The function is case sensetive.
        value = (optional) result value.

    Throws:
        $(LREF DateTimeException) if the given string is
        not in the correct format or if the resulting $(LREF Date) would not
        be valid. Two arguments overload is `nothrow`.
    Returns:
        `bool` on success for two arguments overload, and the resulting date for single argument overdload.
    +/
    static bool fromSimpleString(C)(scope const(C)[] str, out Date value) @safe pure nothrow @nogc
        if (isSomeChar!C)
    {
        import mir.parse: fromString;

        if (str.length < 11 || str[$-3] != '-' || str[$-7] != '-')
            return false;

        auto yearStr = str[0 .. $ - 7];

        if ((yearStr[0] == '+' || yearStr[0] == '-') != (yearStr.length > 4))
            return false;

        Month month;

        switch (str[$ - 6 .. $ - 3])
        {
            case "Jan": month = Month.jan; break;
            case "Feb": month = Month.feb; break;
            case "Mar": month = Month.mar; break;
            case "Apr": month = Month.apr; break;
            case "May": month = Month.may; break;
            case "Jun": month = Month.jun; break;
            case "Jul": month = Month.jul; break;
            case "Aug": month = Month.aug; break;
            case "Sep": month = Month.sep; break;
            case "Oct": month = Month.oct; break;
            case "Nov": month = Month.nov; break;
            case "Dec": month = Month.dec; break;
            default: return false;
        }

        uint day;
        int year;

        return
            fromString(str[$ - 2 .. $], day)
         && fromString(yearStr, year)
         && fromYMD(year, month, day, value);
    }

    /// ditto
    static Date fromSimpleString(C)(scope const(C)[] str) @safe pure
        if (isSomeChar!C)
    {
        Date ret;
        if (fromSimpleString(str, ret))
            return ret;
        throw new DateTimeException("Invalid Simple String");
    }

    ///
    @safe unittest
    {
        assert(Date.fromSimpleString("2010-Jul-04") == Date(2010, 7, 4));
        assert(Date.fromSimpleString("1998-Dec-25") == Date(1998, 12, 25));
        assert(Date.fromSimpleString("0000-Jan-05") == Date(0, 1, 5));
        assert(Date.fromSimpleString("-0004-Jan-05") == Date(-4, 1, 5));
    }

    @safe unittest
    {
        assertThrown!DateTimeException(Date.fromSimpleString(""));
        assertThrown!DateTimeException(Date.fromSimpleString("990704"));
        assertThrown!DateTimeException(Date.fromSimpleString("0100704"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010070"));
        assertThrown!DateTimeException(Date.fromSimpleString("120100704"));
        assertThrown!DateTimeException(Date.fromSimpleString("-0100704"));
        assertThrown!DateTimeException(Date.fromSimpleString("+0100704"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010070a"));
        assertThrown!DateTimeException(Date.fromSimpleString("20100a04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010a704"));

        assertThrown!DateTimeException(Date.fromSimpleString("99-07-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("010-07-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-07-0"));
        assertThrown!DateTimeException(Date.fromSimpleString("12010-07-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("-010-07-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("+010-07-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-07-0a"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-0a-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-a7-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010/07/04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010/7/04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010/7/4"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010/07/4"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-7-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-7-4"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-07-4"));

        assertThrown!DateTimeException(Date.fromSimpleString("99Jul04"));
        assertThrown!DateTimeException(Date.fromSimpleString("010Jul04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010Jul0"));
        assertThrown!DateTimeException(Date.fromSimpleString("12010Jul04"));
        assertThrown!DateTimeException(Date.fromSimpleString("-010Jul04"));
        assertThrown!DateTimeException(Date.fromSimpleString("+010Jul04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010Jul0a"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010Jua04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010aul04"));

        assertThrown!DateTimeException(Date.fromSimpleString("99-Jul-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("010-Jul-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-Jul-0"));
        assertThrown!DateTimeException(Date.fromSimpleString("12010-Jul-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("-010-Jul-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("+010-Jul-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-Jul-0a"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-Jua-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-Jal-04"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-aul-04"));

        assertThrown!DateTimeException(Date.fromSimpleString("20100704"));
        assertThrown!DateTimeException(Date.fromSimpleString("2010-07-04"));

        assert(Date.fromSimpleString("1999-Jul-06") == Date(1999, 7, 6));
        assert(Date.fromSimpleString("-1999-Jul-06") == Date(-1999, 7, 6));
        assert(Date.fromSimpleString("+01999-Jul-06") == Date(1999, 7, 6));
    }

    // bug# 17801
    @safe unittest
    {
        import std.conv : to;
        import std.meta : AliasSeq;
        static foreach (C; AliasSeq!(char, wchar, dchar))
        {
            static foreach (S; AliasSeq!(C[], const(C)[], immutable(C)[]))
                assert(Date.fromSimpleString(to!S("2012-Dec-21")) == Date(2012, 12, 21));
        }
    }

    /++
    Creates a $(LREF Date) from a string with the format YYYY-MM-DD, YYYYMMDD, or YYYY-Mon-DD.

    Params:
        str = A string formatted in the way that $(LREF .date.toISOExtString), $(LREF .date.toISOString), and $(LREF .date.toSimpleString) format dates. The function is case sensetive.
        value = (optional) result value.

    Throws:
        $(LREF DateTimeException) if the given string is
        not in the correct format or if the resulting $(LREF Date) would not
        be valid. Two arguments overload is `nothrow`.
    Returns:
        `bool` on success for two arguments overload, and the resulting date for single argument overdload.
    +/
    static bool fromString(C)(scope const(C)[] str, out Date value) @safe pure nothrow @nogc
    {
        return fromISOExtString(str, value)
            || fromISOString(str, value)
            || fromSimpleString(str, value);
    }

    ///
    @safe pure @nogc unittest
    {
        assert(Date.fromString("2010-07-04") == Date(2010, 7, 4));
        assert(Date.fromString("20100704") == Date(2010, 7, 4));
        assert(Date.fromString("2010-Jul-04") == Date(2010, 7, 4));
    }

    /// ditto
    static Date fromString(C)(scope const(C)[] str) @safe pure
        if (isSomeChar!C)
    {
        Date ret;
        if (fromString(str, ret))
            return ret;
        throw InvalidString;
    }

    /++
        Returns the $(LREF Date) farthest in the past which is representable by
        $(LREF Date).
      +/
    @property static Date min() @safe pure nothrow @nogc
    {
        return Date(-(int.max / 2));
    }

    /++
        Returns the $(LREF Date) farthest in the future which is representable
        by $(LREF Date).
      +/
    @property static Date max() @safe pure nothrow @nogc
    {
        return Date(int.max / 2);
    }

private:

    /+
        Whether the given values form a valid date.

        Params:
            year  = The year to test.
            month = The month of the Gregorian Calendar to test.
            day   = The day of the month to test.
     +/
    static bool _valid(int year, int month, int day) @safe pure nothrow @nogc
    {
        if (!valid!"months"(month))
            return false;
        return valid!"days"(year, month, day);
    }


package:

    /+
        Adds the given number of days to this $(LREF Date). A negative number
        will subtract.

        The month will be adjusted along with the day if the number of days
        added (or subtracted) would overflow (or underflow) the current month.
        The year will be adjusted along with the month if the increase (or
        decrease) to the month would cause it to overflow (or underflow) the
        current year.

        $(D _addDays(numDays)) is effectively equivalent to
        $(D date.dayOfGregorianCal = date.dayOfGregorianCal + days).

        Params:
            days = The number of days to add to this Date.
      +/
    ref Date _addDays(long days) return @safe pure nothrow @nogc
    {
        _julianDay = cast(int)(_julianDay + days);
        return this;
    }

    @safe unittest
    {
        // Test A.D.
        {
            auto date = Date(1999, 2, 28);
            date._addDays(1);
            assert(date == Date(1999, 3, 1));
            date._addDays(-1);
            assert(date == Date(1999, 2, 28));
        }

        {
            auto date = Date(2000, 2, 28);
            date._addDays(1);
            assert(date == Date(2000, 2, 29));
            date._addDays(1);
            assert(date == Date(2000, 3, 1));
            date._addDays(-1);
            assert(date == Date(2000, 2, 29));
        }

        {
            auto date = Date(1999, 6, 30);
            date._addDays(1);
            assert(date == Date(1999, 7, 1));
            date._addDays(-1);
            assert(date == Date(1999, 6, 30));
        }

        {
            auto date = Date(1999, 7, 31);
            date._addDays(1);
            assert(date == Date(1999, 8, 1));
            date._addDays(-1);
            assert(date == Date(1999, 7, 31));
        }

        {
            auto date = Date(1999, 1, 1);
            date._addDays(-1);
            assert(date == Date(1998, 12, 31));
            date._addDays(1);
            assert(date == Date(1999, 1, 1));
        }

        {
            auto date = Date(1999, 7, 6);
            date._addDays(9);
            assert(date == Date(1999, 7, 15));
            date._addDays(-11);
            assert(date == Date(1999, 7, 4));
            date._addDays(30);
            assert(date == Date(1999, 8, 3));
            date._addDays(-3);
            assert(date == Date(1999, 7, 31));
        }

        {
            auto date = Date(1999, 7, 6);
            date._addDays(365);
            assert(date == Date(2000, 7, 5));
            date._addDays(-365);
            assert(date == Date(1999, 7, 6));
            date._addDays(366);
            assert(date == Date(2000, 7, 6));
            date._addDays(730);
            assert(date == Date(2002, 7, 6));
            date._addDays(-1096);
            assert(date == Date(1999, 7, 6));
        }

        // Test B.C.
        {
            auto date = Date(-1999, 2, 28);
            date._addDays(1);
            assert(date == Date(-1999, 3, 1));
            date._addDays(-1);
            assert(date == Date(-1999, 2, 28));
        }

        {
            auto date = Date(-2000, 2, 28);
            date._addDays(1);
            assert(date == Date(-2000, 2, 29));
            date._addDays(1);
            assert(date == Date(-2000, 3, 1));
            date._addDays(-1);
            assert(date == Date(-2000, 2, 29));
        }

        {
            auto date = Date(-1999, 6, 30);
            date._addDays(1);
            assert(date == Date(-1999, 7, 1));
            date._addDays(-1);
            assert(date == Date(-1999, 6, 30));
        }

        {
            auto date = Date(-1999, 7, 31);
            date._addDays(1);
            assert(date == Date(-1999, 8, 1));
            date._addDays(-1);
            assert(date == Date(-1999, 7, 31));
        }

        {
            auto date = Date(-1999, 1, 1);
            date._addDays(-1);
            assert(date == Date(-2000, 12, 31));
            date._addDays(1);
            assert(date == Date(-1999, 1, 1));
        }

        {
            auto date = Date(-1999, 7, 6);
            date._addDays(9);
            assert(date == Date(-1999, 7, 15));
            date._addDays(-11);
            assert(date == Date(-1999, 7, 4));
            date._addDays(30);
            assert(date == Date(-1999, 8, 3));
            date._addDays(-3);
        }

        {
            auto date = Date(-1999, 7, 6);
            date._addDays(365);
            assert(date == Date(-1998, 7, 6));
            date._addDays(-365);
            assert(date == Date(-1999, 7, 6));
            date._addDays(366);
            assert(date == Date(-1998, 7, 7));
            date._addDays(730);
            assert(date == Date(-1996, 7, 6));
            date._addDays(-1096);
            assert(date == Date(-1999, 7, 6));
        }

        // Test Both
        {
            auto date = Date(1, 7, 6);
            date._addDays(-365);
            assert(date == Date(0, 7, 6));
            date._addDays(365);
            assert(date == Date(1, 7, 6));
            date._addDays(-731);
            assert(date == Date(-1, 7, 6));
            date._addDays(730);
            assert(date == Date(1, 7, 5));
        }

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        static assert(!__traits(compiles, cdate._addDays(12)));
        static assert(!__traits(compiles, idate._addDays(12)));
    }

    int _julianDay;

    /// ASDF(JSON) serialization support
    public void serialize(S)(ref S serializer) pure
    {
        import mir.format: print;
        import mir.small_string : SmallString;
        SmallString!16 w;
        print(w, this);
        serializer.putValue(w[]);
    }

    /// ASDF(JSON) deserialization support
    public static Date deserialize(D)(auto ref D deserializer)
    {
        return fromString(cast(const(char)[])deserializer);
    }
}

/// ditto
alias Date = date;

/++
    Returns the number of days from the current day of the week to the given
    day of the week. If they are the same, then the result is 0.
    Params:
        currDoW = The current day of the week.
        dow     = The day of the week to get the number of days to.
  +/
int daysToDayOfWeek(DayOfWeek currDoW, DayOfWeek dow) @safe pure nothrow @nogc
{
    if (currDoW == dow)
        return 0;
    if (currDoW < dow)
        return dow - currDoW;
    return DayOfWeek.sun - currDoW + dow + 1;
}

///
@safe pure nothrow @nogc unittest
{
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.mon) == 0);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.sun) == 6);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.wed) == 2);
}

@safe unittest
{
    assert(daysToDayOfWeek(DayOfWeek.sun, DayOfWeek.sun) == 0);
    assert(daysToDayOfWeek(DayOfWeek.sun, DayOfWeek.mon) == 1);
    assert(daysToDayOfWeek(DayOfWeek.sun, DayOfWeek.tue) == 2);
    assert(daysToDayOfWeek(DayOfWeek.sun, DayOfWeek.wed) == 3);
    assert(daysToDayOfWeek(DayOfWeek.sun, DayOfWeek.thu) == 4);
    assert(daysToDayOfWeek(DayOfWeek.sun, DayOfWeek.fri) == 5);
    assert(daysToDayOfWeek(DayOfWeek.sun, DayOfWeek.sat) == 6);

    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.sun) == 6);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.mon) == 0);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.tue) == 1);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.wed) == 2);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.thu) == 3);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.fri) == 4);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.sat) == 5);

    assert(daysToDayOfWeek(DayOfWeek.tue, DayOfWeek.sun) == 5);
    assert(daysToDayOfWeek(DayOfWeek.tue, DayOfWeek.mon) == 6);
    assert(daysToDayOfWeek(DayOfWeek.tue, DayOfWeek.tue) == 0);
    assert(daysToDayOfWeek(DayOfWeek.tue, DayOfWeek.wed) == 1);
    assert(daysToDayOfWeek(DayOfWeek.tue, DayOfWeek.thu) == 2);
    assert(daysToDayOfWeek(DayOfWeek.tue, DayOfWeek.fri) == 3);
    assert(daysToDayOfWeek(DayOfWeek.tue, DayOfWeek.sat) == 4);

    assert(daysToDayOfWeek(DayOfWeek.wed, DayOfWeek.sun) == 4);
    assert(daysToDayOfWeek(DayOfWeek.wed, DayOfWeek.mon) == 5);
    assert(daysToDayOfWeek(DayOfWeek.wed, DayOfWeek.tue) == 6);
    assert(daysToDayOfWeek(DayOfWeek.wed, DayOfWeek.wed) == 0);
    assert(daysToDayOfWeek(DayOfWeek.wed, DayOfWeek.thu) == 1);
    assert(daysToDayOfWeek(DayOfWeek.wed, DayOfWeek.fri) == 2);
    assert(daysToDayOfWeek(DayOfWeek.wed, DayOfWeek.sat) == 3);

    assert(daysToDayOfWeek(DayOfWeek.thu, DayOfWeek.sun) == 3);
    assert(daysToDayOfWeek(DayOfWeek.thu, DayOfWeek.mon) == 4);
    assert(daysToDayOfWeek(DayOfWeek.thu, DayOfWeek.tue) == 5);
    assert(daysToDayOfWeek(DayOfWeek.thu, DayOfWeek.wed) == 6);
    assert(daysToDayOfWeek(DayOfWeek.thu, DayOfWeek.thu) == 0);
    assert(daysToDayOfWeek(DayOfWeek.thu, DayOfWeek.fri) == 1);
    assert(daysToDayOfWeek(DayOfWeek.thu, DayOfWeek.sat) == 2);

    assert(daysToDayOfWeek(DayOfWeek.fri, DayOfWeek.sun) == 2);
    assert(daysToDayOfWeek(DayOfWeek.fri, DayOfWeek.mon) == 3);
    assert(daysToDayOfWeek(DayOfWeek.fri, DayOfWeek.tue) == 4);
    assert(daysToDayOfWeek(DayOfWeek.fri, DayOfWeek.wed) == 5);
    assert(daysToDayOfWeek(DayOfWeek.fri, DayOfWeek.thu) == 6);
    assert(daysToDayOfWeek(DayOfWeek.fri, DayOfWeek.fri) == 0);
    assert(daysToDayOfWeek(DayOfWeek.fri, DayOfWeek.sat) == 1);

    assert(daysToDayOfWeek(DayOfWeek.sat, DayOfWeek.sun) == 1);
    assert(daysToDayOfWeek(DayOfWeek.sat, DayOfWeek.mon) == 2);
    assert(daysToDayOfWeek(DayOfWeek.sat, DayOfWeek.tue) == 3);
    assert(daysToDayOfWeek(DayOfWeek.sat, DayOfWeek.wed) == 4);
    assert(daysToDayOfWeek(DayOfWeek.sat, DayOfWeek.thu) == 5);
    assert(daysToDayOfWeek(DayOfWeek.sat, DayOfWeek.fri) == 6);
    assert(daysToDayOfWeek(DayOfWeek.sat, DayOfWeek.sat) == 0);
}

package:


/+
    Array of the short (three letter) names of each month.
  +/
immutable string[12] _monthNames = ["Jan",
                                    "Feb",
                                    "Mar",
                                    "Apr",
                                    "May",
                                    "Jun",
                                    "Jul",
                                    "Aug",
                                    "Sep",
                                    "Oct",
                                    "Nov",
                                    "Dec"];

/++
    The maximum valid Day in the given month in the given year.

    Params:
        year  = The year to get the day for.
        month = The month of the Gregorian Calendar to get the day for.
 +/
public ubyte maxDay(int year, int month) @safe pure nothrow @nogc
in
{
    assert(valid!"months"(month));
}
do
{
    switch (month)
    {
        case Month.jan, Month.mar, Month.may, Month.jul, Month.aug, Month.oct, Month.dec:
            return 31;
        case Month.feb:
            return yearIsLeapYear(year) ? 29 : 28;
        case Month.apr, Month.jun, Month.sep, Month.nov:
            return 30;
        default:
            assert(0, "Invalid month.");
    }
}

@safe unittest
{
    // Test A.D.
    assert(maxDay(1999, 1) == 31);
    assert(maxDay(1999, 2) == 28);
    assert(maxDay(1999, 3) == 31);
    assert(maxDay(1999, 4) == 30);
    assert(maxDay(1999, 5) == 31);
    assert(maxDay(1999, 6) == 30);
    assert(maxDay(1999, 7) == 31);
    assert(maxDay(1999, 8) == 31);
    assert(maxDay(1999, 9) == 30);
    assert(maxDay(1999, 10) == 31);
    assert(maxDay(1999, 11) == 30);
    assert(maxDay(1999, 12) == 31);

    assert(maxDay(2000, 1) == 31);
    assert(maxDay(2000, 2) == 29);
    assert(maxDay(2000, 3) == 31);
    assert(maxDay(2000, 4) == 30);
    assert(maxDay(2000, 5) == 31);
    assert(maxDay(2000, 6) == 30);
    assert(maxDay(2000, 7) == 31);
    assert(maxDay(2000, 8) == 31);
    assert(maxDay(2000, 9) == 30);
    assert(maxDay(2000, 10) == 31);
    assert(maxDay(2000, 11) == 30);
    assert(maxDay(2000, 12) == 31);

    // Test B.C.
    assert(maxDay(-1999, 1) == 31);
    assert(maxDay(-1999, 2) == 28);
    assert(maxDay(-1999, 3) == 31);
    assert(maxDay(-1999, 4) == 30);
    assert(maxDay(-1999, 5) == 31);
    assert(maxDay(-1999, 6) == 30);
    assert(maxDay(-1999, 7) == 31);
    assert(maxDay(-1999, 8) == 31);
    assert(maxDay(-1999, 9) == 30);
    assert(maxDay(-1999, 10) == 31);
    assert(maxDay(-1999, 11) == 30);
    assert(maxDay(-1999, 12) == 31);

    assert(maxDay(-2000, 1) == 31);
    assert(maxDay(-2000, 2) == 29);
    assert(maxDay(-2000, 3) == 31);
    assert(maxDay(-2000, 4) == 30);
    assert(maxDay(-2000, 5) == 31);
    assert(maxDay(-2000, 6) == 30);
    assert(maxDay(-2000, 7) == 31);
    assert(maxDay(-2000, 8) == 31);
    assert(maxDay(-2000, 9) == 30);
    assert(maxDay(-2000, 10) == 31);
    assert(maxDay(-2000, 11) == 30);
    assert(maxDay(-2000, 12) == 31);
}

/+
    Returns the day of the week for the given day of the Gregorian/Julian Calendar.

    Params:
        day = The day of the Gregorian/Julian Calendar for which to get the day of
              the week.
  +/
DayOfWeek getDayOfWeek(int day) @safe pure nothrow @nogc
{
    // January 1st, 1 A.D. was a Monday
    if (day >= 0)
        return cast(DayOfWeek)(day % 7);
    else
    {
        immutable dow = cast(DayOfWeek)((day % 7) + 7);

        if (dow == 7)
            return DayOfWeek.mon;
        else
            return dow;
    }
}

private:

enum daysInYear     = 365;  // The number of days in a non-leap year.
enum daysInLeapYear = 366;  // The numbef or days in a leap year.
enum daysIn4Years   = daysInYear * 3 + daysInLeapYear;  // Number of days in 4 years.
enum daysIn100Years = daysIn4Years * 25 - 1;  // The number of days in 100 years.
enum daysIn400Years = daysIn100Years * 4 + 1; // The number of days in 400 years.

/+
    Array of integers representing the last days of each month in a year.
  +/
immutable int[13] lastDayNonLeap = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334, 365];

/+
    Array of integers representing the last days of each month in a leap year.
  +/
immutable int[13] lastDayLeap = [0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335, 366];


/+
    Returns the string representation of the given month.
  +/
string monthToString(Month month) @safe pure @nogc nothrow
{
    assert(month >= Month.jan && month <= Month.dec, "Invalid month");
    return _monthNames[month - Month.jan];
}

@safe unittest
{
    assert(monthToString(Month.jan) == "Jan");
    assert(monthToString(Month.feb) == "Feb");
    assert(monthToString(Month.mar) == "Mar");
    assert(monthToString(Month.apr) == "Apr");
    assert(monthToString(Month.may) == "May");
    assert(monthToString(Month.jun) == "Jun");
    assert(monthToString(Month.jul) == "Jul");
    assert(monthToString(Month.aug) == "Aug");
    assert(monthToString(Month.sep) == "Sep");
    assert(monthToString(Month.oct) == "Oct");
    assert(monthToString(Month.nov) == "Nov");
    assert(monthToString(Month.dec) == "Dec");
}

version(unittest)
{
    // All of these helper arrays are sorted in ascending order.
    auto testYearsBC = [-1999, -1200, -600, -4, -1, 0];
    auto testYearsAD = [1, 4, 1000, 1999, 2000, 2012];

    // I'd use a Tuple, but I get forward reference errors if I try.
    struct MonthDay
    {
        Month month;
        short day;

        this(int m, short d)
        {
            month = cast(Month) m;
            day = d;
        }
    }

    MonthDay[] testMonthDays = [MonthDay(1, 1),
                                MonthDay(1, 2),
                                MonthDay(3, 17),
                                MonthDay(7, 4),
                                MonthDay(10, 27),
                                MonthDay(12, 30),
                                MonthDay(12, 31)];

    auto testDays = [1, 2, 9, 10, 16, 20, 25, 28, 29, 30, 31];

    Date[] testDatesBC;
    Date[] testDatesAD;

    // I'd use a Tuple, but I get forward reference errors if I try.
    struct GregDay { int day; Date date; }
    auto testGregDaysBC = [GregDay(-1_373_427, Date(-3760, 9, 7)), // Start of the Hebrew Calendar
                           GregDay(-735_233, Date(-2012, 1, 1)),
                           GregDay(-735_202, Date(-2012, 2, 1)),
                           GregDay(-735_175, Date(-2012, 2, 28)),
                           GregDay(-735_174, Date(-2012, 2, 29)),
                           GregDay(-735_173, Date(-2012, 3, 1)),
                           GregDay(-734_502, Date(-2010, 1, 1)),
                           GregDay(-734_472, Date(-2010, 1, 31)),
                           GregDay(-734_471, Date(-2010, 2, 1)),
                           GregDay(-734_444, Date(-2010, 2, 28)),
                           GregDay(-734_443, Date(-2010, 3, 1)),
                           GregDay(-734_413, Date(-2010, 3, 31)),
                           GregDay(-734_412, Date(-2010, 4, 1)),
                           GregDay(-734_383, Date(-2010, 4, 30)),
                           GregDay(-734_382, Date(-2010, 5, 1)),
                           GregDay(-734_352, Date(-2010, 5, 31)),
                           GregDay(-734_351, Date(-2010, 6, 1)),
                           GregDay(-734_322, Date(-2010, 6, 30)),
                           GregDay(-734_321, Date(-2010, 7, 1)),
                           GregDay(-734_291, Date(-2010, 7, 31)),
                           GregDay(-734_290, Date(-2010, 8, 1)),
                           GregDay(-734_260, Date(-2010, 8, 31)),
                           GregDay(-734_259, Date(-2010, 9, 1)),
                           GregDay(-734_230, Date(-2010, 9, 30)),
                           GregDay(-734_229, Date(-2010, 10, 1)),
                           GregDay(-734_199, Date(-2010, 10, 31)),
                           GregDay(-734_198, Date(-2010, 11, 1)),
                           GregDay(-734_169, Date(-2010, 11, 30)),
                           GregDay(-734_168, Date(-2010, 12, 1)),
                           GregDay(-734_139, Date(-2010, 12, 30)),
                           GregDay(-734_138, Date(-2010, 12, 31)),
                           GregDay(-731_215, Date(-2001, 1, 1)),
                           GregDay(-730_850, Date(-2000, 1, 1)),
                           GregDay(-730_849, Date(-2000, 1, 2)),
                           GregDay(-730_486, Date(-2000, 12, 30)),
                           GregDay(-730_485, Date(-2000, 12, 31)),
                           GregDay(-730_484, Date(-1999, 1, 1)),
                           GregDay(-694_690, Date(-1901, 1, 1)),
                           GregDay(-694_325, Date(-1900, 1, 1)),
                           GregDay(-585_118, Date(-1601, 1, 1)),
                           GregDay(-584_753, Date(-1600, 1, 1)),
                           GregDay(-584_388, Date(-1600, 12, 31)),
                           GregDay(-584_387, Date(-1599, 1, 1)),
                           GregDay(-365_972, Date(-1001, 1, 1)),
                           GregDay(-365_607, Date(-1000, 1, 1)),
                           GregDay(-183_351, Date(-501, 1, 1)),
                           GregDay(-182_986, Date(-500, 1, 1)),
                           GregDay(-182_621, Date(-499, 1, 1)),
                           GregDay(-146_827, Date(-401, 1, 1)),
                           GregDay(-146_462, Date(-400, 1, 1)),
                           GregDay(-146_097, Date(-400, 12, 31)),
                           GregDay(-110_302, Date(-301, 1, 1)),
                           GregDay(-109_937, Date(-300, 1, 1)),
                           GregDay(-73_778, Date(-201, 1, 1)),
                           GregDay(-73_413, Date(-200, 1, 1)),
                           GregDay(-38_715, Date(-105, 1, 1)),
                           GregDay(-37_254, Date(-101, 1, 1)),
                           GregDay(-36_889, Date(-100, 1, 1)),
                           GregDay(-36_524, Date(-99, 1, 1)),
                           GregDay(-36_160, Date(-99, 12, 31)),
                           GregDay(-35_794, Date(-97, 1, 1)),
                           GregDay(-18_627, Date(-50, 1, 1)),
                           GregDay(-18_262, Date(-49, 1, 1)),
                           GregDay(-3652, Date(-9, 1, 1)),
                           GregDay(-2191, Date(-5, 1, 1)),
                           GregDay(-1827, Date(-5, 12, 31)),
                           GregDay(-1826, Date(-4, 1, 1)),
                           GregDay(-1825, Date(-4, 1, 2)),
                           GregDay(-1462, Date(-4, 12, 30)),
                           GregDay(-1461, Date(-4, 12, 31)),
                           GregDay(-1460, Date(-3, 1, 1)),
                           GregDay(-1096, Date(-3, 12, 31)),
                           GregDay(-1095, Date(-2, 1, 1)),
                           GregDay(-731, Date(-2, 12, 31)),
                           GregDay(-730, Date(-1, 1, 1)),
                           GregDay(-367, Date(-1, 12, 30)),
                           GregDay(-366, Date(-1, 12, 31)),
                           GregDay(-365, Date(0, 1, 1)),
                           GregDay(-31, Date(0, 11, 30)),
                           GregDay(-30, Date(0, 12, 1)),
                           GregDay(-1, Date(0, 12, 30)),
                           GregDay(0, Date(0, 12, 31))];

    auto testGregDaysAD = [GregDay(1, Date(1, 1, 1)),
                           GregDay(2, Date(1, 1, 2)),
                           GregDay(32, Date(1, 2, 1)),
                           GregDay(365, Date(1, 12, 31)),
                           GregDay(366, Date(2, 1, 1)),
                           GregDay(731, Date(3, 1, 1)),
                           GregDay(1096, Date(4, 1, 1)),
                           GregDay(1097, Date(4, 1, 2)),
                           GregDay(1460, Date(4, 12, 30)),
                           GregDay(1461, Date(4, 12, 31)),
                           GregDay(1462, Date(5, 1, 1)),
                           GregDay(17_898, Date(50, 1, 1)),
                           GregDay(35_065, Date(97, 1, 1)),
                           GregDay(36_160, Date(100, 1, 1)),
                           GregDay(36_525, Date(101, 1, 1)),
                           GregDay(37_986, Date(105, 1, 1)),
                           GregDay(72_684, Date(200, 1, 1)),
                           GregDay(73_049, Date(201, 1, 1)),
                           GregDay(109_208, Date(300, 1, 1)),
                           GregDay(109_573, Date(301, 1, 1)),
                           GregDay(145_732, Date(400, 1, 1)),
                           GregDay(146_098, Date(401, 1, 1)),
                           GregDay(182_257, Date(500, 1, 1)),
                           GregDay(182_622, Date(501, 1, 1)),
                           GregDay(364_878, Date(1000, 1, 1)),
                           GregDay(365_243, Date(1001, 1, 1)),
                           GregDay(584_023, Date(1600, 1, 1)),
                           GregDay(584_389, Date(1601, 1, 1)),
                           GregDay(693_596, Date(1900, 1, 1)),
                           GregDay(693_961, Date(1901, 1, 1)),
                           GregDay(729_755, Date(1999, 1, 1)),
                           GregDay(730_120, Date(2000, 1, 1)),
                           GregDay(730_121, Date(2000, 1, 2)),
                           GregDay(730_484, Date(2000, 12, 30)),
                           GregDay(730_485, Date(2000, 12, 31)),
                           GregDay(730_486, Date(2001, 1, 1)),
                           GregDay(733_773, Date(2010, 1, 1)),
                           GregDay(733_774, Date(2010, 1, 2)),
                           GregDay(733_803, Date(2010, 1, 31)),
                           GregDay(733_804, Date(2010, 2, 1)),
                           GregDay(733_831, Date(2010, 2, 28)),
                           GregDay(733_832, Date(2010, 3, 1)),
                           GregDay(733_862, Date(2010, 3, 31)),
                           GregDay(733_863, Date(2010, 4, 1)),
                           GregDay(733_892, Date(2010, 4, 30)),
                           GregDay(733_893, Date(2010, 5, 1)),
                           GregDay(733_923, Date(2010, 5, 31)),
                           GregDay(733_924, Date(2010, 6, 1)),
                           GregDay(733_953, Date(2010, 6, 30)),
                           GregDay(733_954, Date(2010, 7, 1)),
                           GregDay(733_984, Date(2010, 7, 31)),
                           GregDay(733_985, Date(2010, 8, 1)),
                           GregDay(734_015, Date(2010, 8, 31)),
                           GregDay(734_016, Date(2010, 9, 1)),
                           GregDay(734_045, Date(2010, 9, 30)),
                           GregDay(734_046, Date(2010, 10, 1)),
                           GregDay(734_076, Date(2010, 10, 31)),
                           GregDay(734_077, Date(2010, 11, 1)),
                           GregDay(734_106, Date(2010, 11, 30)),
                           GregDay(734_107, Date(2010, 12, 1)),
                           GregDay(734_136, Date(2010, 12, 30)),
                           GregDay(734_137, Date(2010, 12, 31)),
                           GregDay(734_503, Date(2012, 1, 1)),
                           GregDay(734_534, Date(2012, 2, 1)),
                           GregDay(734_561, Date(2012, 2, 28)),
                           GregDay(734_562, Date(2012, 2, 29)),
                           GregDay(734_563, Date(2012, 3, 1)),
                           GregDay(734_858, Date(2012, 12, 21))];

    // I'd use a Tuple, but I get forward reference errors if I try.
    struct DayOfYear { int day; MonthDay md; }
    auto testDaysOfYear = [DayOfYear(1, MonthDay(1, 1)),
                           DayOfYear(2, MonthDay(1, 2)),
                           DayOfYear(3, MonthDay(1, 3)),
                           DayOfYear(31, MonthDay(1, 31)),
                           DayOfYear(32, MonthDay(2, 1)),
                           DayOfYear(59, MonthDay(2, 28)),
                           DayOfYear(60, MonthDay(3, 1)),
                           DayOfYear(90, MonthDay(3, 31)),
                           DayOfYear(91, MonthDay(4, 1)),
                           DayOfYear(120, MonthDay(4, 30)),
                           DayOfYear(121, MonthDay(5, 1)),
                           DayOfYear(151, MonthDay(5, 31)),
                           DayOfYear(152, MonthDay(6, 1)),
                           DayOfYear(181, MonthDay(6, 30)),
                           DayOfYear(182, MonthDay(7, 1)),
                           DayOfYear(212, MonthDay(7, 31)),
                           DayOfYear(213, MonthDay(8, 1)),
                           DayOfYear(243, MonthDay(8, 31)),
                           DayOfYear(244, MonthDay(9, 1)),
                           DayOfYear(273, MonthDay(9, 30)),
                           DayOfYear(274, MonthDay(10, 1)),
                           DayOfYear(304, MonthDay(10, 31)),
                           DayOfYear(305, MonthDay(11, 1)),
                           DayOfYear(334, MonthDay(11, 30)),
                           DayOfYear(335, MonthDay(12, 1)),
                           DayOfYear(363, MonthDay(12, 29)),
                           DayOfYear(364, MonthDay(12, 30)),
                           DayOfYear(365, MonthDay(12, 31))];

    auto testDaysOfLeapYear = [DayOfYear(1, MonthDay(1, 1)),
                               DayOfYear(2, MonthDay(1, 2)),
                               DayOfYear(3, MonthDay(1, 3)),
                               DayOfYear(31, MonthDay(1, 31)),
                               DayOfYear(32, MonthDay(2, 1)),
                               DayOfYear(59, MonthDay(2, 28)),
                               DayOfYear(60, MonthDay(2, 29)),
                               DayOfYear(61, MonthDay(3, 1)),
                               DayOfYear(91, MonthDay(3, 31)),
                               DayOfYear(92, MonthDay(4, 1)),
                               DayOfYear(121, MonthDay(4, 30)),
                               DayOfYear(122, MonthDay(5, 1)),
                               DayOfYear(152, MonthDay(5, 31)),
                               DayOfYear(153, MonthDay(6, 1)),
                               DayOfYear(182, MonthDay(6, 30)),
                               DayOfYear(183, MonthDay(7, 1)),
                               DayOfYear(213, MonthDay(7, 31)),
                               DayOfYear(214, MonthDay(8, 1)),
                               DayOfYear(244, MonthDay(8, 31)),
                               DayOfYear(245, MonthDay(9, 1)),
                               DayOfYear(274, MonthDay(9, 30)),
                               DayOfYear(275, MonthDay(10, 1)),
                               DayOfYear(305, MonthDay(10, 31)),
                               DayOfYear(306, MonthDay(11, 1)),
                               DayOfYear(335, MonthDay(11, 30)),
                               DayOfYear(336, MonthDay(12, 1)),
                               DayOfYear(364, MonthDay(12, 29)),
                               DayOfYear(365, MonthDay(12, 30)),
                               DayOfYear(366, MonthDay(12, 31))];

    void initializeTests() @safe
    {
        foreach (year; testYearsBC)
        {
            foreach (md; testMonthDays)
                testDatesBC ~= Date(year, md.month, md.day);
        }

        foreach (year; testYearsAD)
        {
            foreach (md; testMonthDays)
                testDatesAD ~= Date(year, md.month, md.day);
        }
    }
}
