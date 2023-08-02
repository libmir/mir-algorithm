/++
Fast BetterC Date type with Boost ABI and mangling compatability.

$(SCRIPT inhibitQuickIndex = 1;)
$(DIVC quickindex,
$(BOOKTABLE,
$(TR $(TH Category) $(TH Functions))
$(TR $(TD Main date types) $(TD
    $(LREF Date)
    $(LREF YearMonth)
    $(LREF YearQuarter)
))
$(TR $(TD Other date types) $(TD
    $(LREF Month)
    $(LREF Quarter)
    $(LREF DayOfWeek)
))
$(TR $(TD Date checking) $(TD
    $(LREF valid)
    $(LREF yearIsLeapYear)
))
$(TR $(TD Date conversion) $(TD
    $(LREF daysToDayOfWeek)
    $(LREF quarter)
))
$(TR $(TD Other) $(TD
    $(LREF AllowDayOverflow)
    $(LREF DateTimeException)
    $(LREF AssumePeriod)
))
))
License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: $(HTTP jmdavisprog.com, Jonathan M Davis), Ilia Ki (boost-like and BetterC rework)
+/
module mir.date;

import mir.primitives: isOutputRange;
import mir.serde: serdeProxy;
import mir.timestamp: Timestamp;
import std.traits: isSomeChar, Unqual;

version(mir_test)
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
version (mir_test)
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
version (mir_test)
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
version (mir_test)
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

version (mir_test)
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
    private static immutable InvalidMonth = new DateTimeException("Date: Invalid Month");
    private static immutable InvalidDay = new DateTimeException("Date: Invalid Day");
    private static immutable InvalidISOString = new DateTimeException("Date: Invalid ISO String");
    private static immutable InvalidISOExtendedString = new DateTimeException("Date: Invalid ISO Extended String");
    private static immutable InvalidSimpleString = new DateTimeException("Date: Invalid Simple String");
    private static immutable InvalidString = new DateTimeException("Date: Invalid String");
}

version (mir_test)
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
@serdeProxy!Timestamp
struct YearMonthDay
{
    short year  = 1;
    Month month = Month.jan;
    ubyte day   = 1;

    ///
    Quarter quarter() @safe pure nothrow @nogc @property
    {
        return month.quarter;
    }

    ///
    Timestamp timestamp() @safe pure nothrow @nogc const @property
    {
        return Timestamp(year, cast(ubyte)month, day);
    }

    ///
    alias opCast(T : Timestamp) = timestamp;

@safe pure @nogc:

    ///
    YearQuarter yearQuarter() @safe pure nothrow @nogc @property
    {
        return YearQuarter(year, this.quarter);
    }

    ///
    alias opCast(T : YearQuarter) = yearQuarter;

    ///
    version(mir_test)
    unittest
    {
        import mir.timestamp;
        auto timestamp = cast(Timestamp) YearMonthDay(2020, Month.may, 12);
    }

    ///
    this(short year, Month month, ubyte day) @safe pure nothrow @nogc
    {
        this.year = year;
        this.month = month;
        this.day = day;
    }

    ///
    this(Date date) @safe pure nothrow @nogc
    {
        this = date.yearMonthDay;
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d = YearMonthDay(2020, Month.may, 31);
        auto ym = d.YearMonth;
        assert(ym.year == 2020);
        assert(ym.month == Month.may);
    }

    //
    version(mir_test)
    @safe unittest
    {
        auto d = YearMonthDay(2050, Month.dec, 31);
        auto ym = d.YearMonth;
        assert(ym.year == 2050);
        assert(ym.month == Month.dec);
    }

    ///
    this(YearMonth yearMonth, AssumePeriod assumePeriod = AssumePeriod.begin) @safe pure nothrow @nogc
    {
        with(yearMonth) this(year, month, day(assumePeriod));
    }

    ///
    this(YearQuarter yearQuarter, AssumePeriod assumePeriodMonth = AssumePeriod.begin, AssumePeriod assumePeriodDay = AssumePeriod.begin) @safe pure nothrow @nogc
    {
        with(yearQuarter) this(year, month(assumePeriodMonth), day(assumePeriodDay));
    }

    version(D_Exceptions)
    ///
    this(Timestamp timestamp) @safe pure @nogc
    {
        if (timestamp.precision != Timestamp.Precision.day)
        {
            static immutable exc = new Exception("YearMonthDay: invalid timestamp precision");
            { import mir.exception : toMutable; throw exc.toMutable; }
        }
        with(timestamp) this(year, cast(Month)month, day);
    }

    ///
    @safe pure nothrow @nogc
    ref YearMonthDay add(string units : "months")(long months, AllowDayOverflow allowOverflow = AllowDayOverflow.yes)
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

    ///
    @safe pure nothrow @nogc
    ref YearMonthDay add(string units : "quarters")(long quarters)
    {
        return add!"months"(quarters * 4);
    }

    // Shares documentation with "years" version.
    @safe pure nothrow @nogc
    ref YearMonthDay add(string units : "years")(long years, AllowDayOverflow allowOverflow = AllowDayOverflow.yes)
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
    version (mir_test)
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
            if (dayOutOfRange) { import mir.exception : toMutable; throw InvalidDay.toMutable; }
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
Controls the assumed start period of days for `YearMonth` or days and quarters
for `YearQuarter`
+/
enum AssumePeriod {
    ///
    begin,
    ///
    end
}

/// Represents a date as a pair of years and months. 
@serdeProxy!Timestamp
struct YearMonth
{
    short year  = 1;
    Month month = Month.jan;

    version(D_BetterC){} else
    {
        private string toStringImpl(alias fun)() const @safe pure nothrow
        {
            import mir.small_string : SmallString;
            SmallString!16 w;
            try
                fun(w);
            catch (Exception e)
                assert(0, __traits(identifier, fun) ~ " threw.");
            return w[].idup;
        }

        string toISOExtString() const @safe pure nothrow
        {
            return toStringImpl!toISOExtString;
        }

        alias toString = toISOExtString;
    }

    ///
    void toISOExtString(W)(scope ref W w) const scope
        if (isOutputRange!(W, char))
    {
        import mir.format: printZeroPad;
        if (year >= 10_000)
            w.put('+');
        w.printZeroPad(year, year >= 0 ? year < 10_000 ? 4 : 5 : year > -10_000 ? 5 : 6);
        w.put('-');
        w.printZeroPad(cast(uint)month, 2);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(1999, Month.jan);
        assert(ym.toISOExtString == "1999-01");
    }

    //
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(10_001, Month.jan);
        assert(ym.toISOExtString == "+10001-01");
    }

    @property ubyte day(AssumePeriod assumePeriod = AssumePeriod.begin) const @safe pure nothrow @nogc
    {
        final switch (assumePeriod)
        {
            case AssumePeriod.begin:
                return 1;
            case AssumePeriod.end:
                return daysInMonth;
        }
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearMonth(1999, cast(Month) 1).day(AssumePeriod.begin) == 1);
        assert(YearMonth(1999, cast(Month) 12).day(AssumePeriod.end) == 31);
    }

    ///
    Quarter quarter() @safe pure nothrow @nogc @property
    {
        return month.quarter;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearMonth(1999, Month.jan).quarter == 1);
    }

    ///
    Timestamp timestamp() @safe pure nothrow @nogc const @property
    {
        return Timestamp(year, cast(ubyte)month);
    }

    ///
    alias opCast(T : Timestamp) = timestamp;

    ///
    version(mir_test)
    unittest
    {
        import mir.timestamp;
        auto ym0 = YearMonth(2020, Month.may);
        auto timestamp1 = cast(Timestamp) ym0;
        auto ym1 = YearMonth(timestamp1);
    }

    ///
    this(short year, Month month) @safe pure nothrow @nogc
    {
        this.year = year;
        this.month = month;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(2000, Month.dec);
    }

    ///
    this(short year, ushort month) @safe pure @nogc
    {
        static immutable exc = new Exception("Month out of bounds [1, 12]");
        if (1 > month || month > 12)
            { import mir.exception : toMutable; throw exc.toMutable; }
        this.year = year;
        this.month = cast(Month)month;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(2000, 12);
    }

    ///
    this(Date date) @safe pure nothrow @nogc
    {
        this(date.YearMonthDay);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(Date(2000, Month.dec, 31));
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d = Date(2020, Month.may, 31);
        auto ym = d.YearMonth;
        assert(ym.year == 2020);
        assert(ym.month == Month.may);
    }

    //
    version(mir_test)
    @safe unittest
    {
        auto d = Date(2050, Month.dec, 31);
        auto ym = d.YearMonth;
        assert(ym.year == 2050);
        assert(ym.month == Month.dec);
    }

    ///
    this(YearMonthDay yearMonthDay) @safe pure nothrow @nogc
    {
        with(yearMonthDay) this(year, month);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(YearMonthDay(2000, Month.dec, 31));
    }

    ///
    this(YearQuarter yearQuarter, AssumePeriod assumePeriod = AssumePeriod.begin) @safe pure nothrow @nogc
    {
        with(yearQuarter) this(year, month(assumePeriod));
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym1 = YearMonth(YearQuarter(2000, Quarter.q1));
        auto ym2 = YearMonth(YearQuarter(2000, Quarter.q1), AssumePeriod.end);
    }

    version(D_Exceptions)
    ///
    this(Timestamp timestamp) @safe pure @nogc
    {
        if (timestamp.precision != Timestamp.Precision.month)
        {
            static immutable exc = new Exception("YearMonth: invalid timestamp precision");
            { import mir.exception : toMutable; throw exc.toMutable; }
        }
        with(timestamp) this(year, cast(Month)month);
    }

    Date nthWeekday(int n, DayOfWeek dow) const @safe pure nothrow @nogc
    {
        auto d = trustedWithDayOfMonth(1);
        auto dc = d.dayOfWeek.daysToDayOfWeek(dow) + (n - 1) * 7;
        d = d + dc;
        return d;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(2000, Month.nov);
        assert(ym.nthWeekday(1, DayOfWeek.mon) == Date(2000, 11, 6));
        assert(ym.nthWeekday(5, DayOfWeek.mon) == Date(2000, 12, 4));
    }

    ///
    Date trustedWithDayOfMonth(int days) const @safe pure nothrow @nogc
    {
        assert(days <= lengthOfMonth);
        return Date.trustedCreate(year, month, days);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(2000, Month.nov);
        assert(ym.trustedWithDayOfMonth(6) == Date(2000, 11, 6));
    }

    ///
    int opCmp(YearMonth rhs) const pure nothrow @nogc @safe
    {
        if (auto d = this.year - rhs.year)
            return d;
        return this.month - rhs.month;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth(2000, Month.nov);
        assert(ym.opCmp(YearMonth(2000, Month.nov)) == 0);
        assert(ym.opCmp(YearMonth(2000, Month.oct)) == 1);
        assert(ym.opCmp(YearMonth(2000, Month.dec)) == -1);
        assert(ym.opCmp(YearMonth(2001, Month.nov)) == -1);
    }

    ///
    size_t toHash() const pure nothrow @nogc @safe
    {
        return year * 16 + month;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearMonth(2000, Month.dec).toHash == 32012);
    }

    ///
    Date endOfMonth() const nothrow @property @nogc @safe pure
    {
        return Date.trustedCreate(year, month, lengthOfMonth);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearMonth(2000, Month.dec).endOfMonth == Date(2000, Month.dec, 31));
    }

    ///
    ushort lengthOfMonth() const pure nothrow @property @nogc @safe
    {
        return maxDay(year, month);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearMonth(2000, Month.dec).lengthOfMonth == 31);
    }

    ///
    this(scope const(char)[] str) @safe pure @nogc
    {
        this = fromISOExtString(str);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearMonth("1999-01");
        assert(ym.year == 1999);
        assert(ym.month == 1);
    }

    static bool fromISOExtString(C)(scope const(C)[] str, out YearMonth value) @safe pure @nogc
        if (isSomeChar!C)
    {
        import mir.parse: fromString;
        if (str.length < 7 || str[$-3] != '-')
            return false;

        auto yearStr = str[0 .. $ - 3];

        if ((yearStr[0] == '+' || yearStr[0] == '-') != (yearStr.length > 4))
            return false;

        short year;
        ushort month;

        const ret =
         fromString(str[$ - 2 .. $], month)
         && fromString(yearStr, year);

        value = YearMonth(year, month);
        return ret;
    }

    static YearMonth fromISOExtString(C)(scope const(C)[] str) @safe pure
        if (isSomeChar!C)
    {
        YearMonth ret;
        if (fromISOExtString(str, ret))
            return ret;
        static immutable exc = new Exception("Invalid YearMonth string");
        { import mir.exception : toMutable; throw exc.toMutable; }
    }

nothrow:

    ///
    deprecated("please use addMonths instead")
    @safe pure nothrow @nogc
    ref YearMonth add(string units : "months")(long months)
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

        return this;
    }

    ///
    version(mir_test_deprecated)
    @safe unittest
    {
        auto ym0 = YearMonth(2020, Month.jan);

        ym0.add!"months"(1);
        assert(ym0.year == 2020);
        assert(ym0.month == Month.feb);

        auto ym1 = ym0.add!"months"(1);
        assert(ym1.year == 2020);
        assert(ym1.month == Month.mar);

        // also changes ym0
        assert(ym0.year == 2020);
        assert(ym0.month == Month.mar);

        ym1.add!"months"(10);
        assert(ym1.year == 2021);
        assert(ym1.month == Month.jan);

        ym1.add!"months"(-13);
        assert(ym1.year == 2019);
        assert(ym1.month == Month.dec);
    }

    ///
    deprecated("please use addQuarters instead")
    @safe pure nothrow @nogc
    ref YearMonth add(string units : "quarters")(long quarters)
    {
        return add!"months"(quarters * 3);
    }

    ///
    version(mir_test_deprecated)
    @safe unittest
    {
        auto yq0 = YearMonth(2020, Month.jan);

        yq0.add!"quarters"(1);
        assert(yq0.year == 2020);
        assert(yq0.month == Month.apr);

        auto yq1 = yq0.add!"quarters"(1);
        assert(yq1.year == 2020);
        assert(yq1.month == Month.jul);

        // also changes yq0
        assert(yq0.year == 2020);
        assert(yq0.month == Month.jul);

        yq1.add!"quarters"(2);
        assert(yq1.year == 2021);
        assert(yq1.month == Month.jan);

        yq1.add!"quarters"(-5);
        assert(yq1.year == 2019);
        assert(yq1.month == Month.oct);
    }

    ///
    deprecated("please use addYears instead")
    @safe pure nothrow @nogc
    ref YearMonth add(string units : "years")(long years)
    {
        year += years;
        return this;
    }

    ///
    version(mir_test_deprecated)
    @safe unittest
    {
        auto ym0 = YearMonth(2020, Month.jan);

        ym0.add!"years"(1);
        assert(ym0.year == 2021);
        assert(ym0.month == Month.jan);

        auto ym1 = ym0.add!"years"(1);
        assert(ym1.year == 2022);
        assert(ym1.month == Month.jan);

        // also changes ym0
        assert(ym0.year == 2022);
        assert(ym0.month == Month.jan);
    }

    ///
    @safe pure nothrow @nogc
    YearMonth addMonths(long months)
    {
        auto newYear = year;
        newYear += months / 12;
        months %= 12;
        auto newMonth = month;
        newMonth += months;

        if (months < 0)
        {
            if (newMonth < 1)
            {
                newMonth += 12;
                --newYear;
            }
        }
        else if (newMonth > 12)
        {
            newMonth -= 12;
            ++newYear;
        }

        return YearMonth(newYear, newMonth);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto ym0 = YearMonth(2020, Month.jan);

        auto ym1 = ym0.addMonths(15);
        assert(ym1.year == 2021);
        assert(ym1.month == Month.apr);

        auto ym2 = ym1.addMonths(-6);
        assert(ym2.year == 2020);
        assert(ym2.month == Month.oct);

        auto ym3 = YearMonth(2020, Month.dec).addMonths(3);
        assert(ym3.year == 2021);
        assert(ym3.month == Month.mar);

        // ym0 is left unchagned
        assert(ym0.year == 2020);
        assert(ym0.month == Month.jan);
    }

    ///
    @safe pure nothrow @nogc
    YearMonth addQuarters(long quarters)
    {
        return addMonths(quarters * 3);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto ym0 = YearMonth(2020, Month.jan);

        auto ym1 = ym0.addQuarters(5);
        assert(ym1.year == 2021);
        assert(ym1.month == Month.apr);

        auto ym2 = ym1.addQuarters(-2);
        assert(ym2.year == 2020);
        assert(ym2.month == Month.oct);

        auto ym3 = YearMonth(2020, Month.dec).addQuarters(1);
        assert(ym3.year == 2021);
        assert(ym3.month == Month.mar);

        // ym0 is left unchagned
        assert(ym0.year == 2020);
        assert(ym0.month == Month.jan);
    }

    ///
    @safe pure nothrow @nogc
    YearMonth addYears(long years)
    {
        auto newYear = this.year;
        newYear += years;
        return YearMonth(newYear, month);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto ym0 = YearMonth(2020, Month.jan);

        auto ym1 = ym0.addYears(1);
        assert(ym1.year == 2021);
        assert(ym1.month == Month.jan);
 
        // leaves ym0 unchanged
        assert(ym0.year == 2020);
        assert(ym0.month == Month.jan);
    }

    private void setMonthOfYear(bool useExceptions = false)(int days)
    {
        immutable int[] lastDay = isLeapYear ? lastDayLeap : lastDayNonLeap;

        bool dayOutOfRange = days <= 0 || days > (isLeapYear ? daysInLeapYear : daysInYear);

        static if (useExceptions)
        {
            if (dayOutOfRange) { import mir.exception : toMutable; throw InvalidDay.toMutable; }
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
                return;
            }
        }
        assert(0, "Invalid day of the year.");
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto ym = YearMonth(2020, Month.feb);
        ym.setMonthOfYear(10);
        assert(ym.year == 2020);
        assert(ym.month == Month.jan);
        ym.setMonthOfYear(100);
        assert(ym.year == 2020);
        assert(ym.month == Month.apr);
        ym.setMonthOfYear(200);
        assert(ym.year == 2020);
        assert(ym.month == Month.jul);
        ym.setMonthOfYear(300);
        assert(ym.year == 2020);
        assert(ym.month == Month.oct);
    }

    ///
    int opBinary(string op : "-")(YearMonth rhs)
    {
        alias a = this;
        alias b = rhs;
        return (a.year - b.year) * 12 + a.month - b.month;
    }

    ///
    YearMonth opBinary(string op)(int rhs)
        if (op == "+" || op == "-")
    {
        static if (op == "+")
           return addMonths(rhs);
        else
           return addMonths(-rhs);
    }

    ///
    alias opBinaryRight(string op : "+") = opBinary!"+";

    ///
    ref YearMonth opOpAssign(string op)(int rhs) return @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        static if (op == "+")
           this = addMonths(rhs);
        else
           this = addMonths(-rhs);
        return this;
    }

    ///
    @safe pure @nogc nothrow
    version(mir_test)
    unittest
    {
        auto x = YearMonth(2020, Month.mar);
        auto x1 = x + 1;
        assert(x1 == YearMonth(2020, Month.apr));
        auto x2 = x + 2;
        assert(x2 == YearMonth(2020, Month.may));
        auto x3 = x + 3;
        assert(x3 == YearMonth(2020, Month.jun));
    }

    ///
    @safe pure @nogc nothrow
    version(mir_test)
    unittest {
        auto ym = YearMonth(2020, Month.mar);
        ym += 2;
        assert(ym == YearMonth(2020, Month.may));
        ym -= 1;
        assert(ym == YearMonth(2020, Month.apr));
    }

    /// Get a slice of YearMonths
    @safe pure @nogc nothrow
    version(mir_test)
    unittest {
        import mir.ndslice.topology: iota;

        static immutable result1 = [YearMonth(2020, Month.mar), YearMonth(2020, Month.apr), YearMonth(2020, Month.may), YearMonth(2020, Month.jun)];
        static immutable result2 = [YearMonth(2020, Month.mar), YearMonth(2020, Month.may), YearMonth(2020, Month.jul), YearMonth(2020, Month.sep)];

        auto ym = YearMonth(2020, Month.mar);

        auto x = ym + 4.iota!uint;
        assert(x == result1);

        // every other month
        auto y = ym + iota!uint([4], 0, 2);
        assert(y == result2);
    }

    /++
        Day of the year this $(LREF Date) is on.
      +/
    @property int dayOfYear(AssumePeriod assumePeriod = AssumePeriod.begin) const @safe pure nothrow @nogc
    {
        if (month >= Month.jan && month <= Month.dec)
        {
            immutable int[] lastDay = isLeapYear ? lastDayLeap : lastDayNonLeap;
            auto monthIndex = month - Month.jan;

            return lastDay[monthIndex] + day(assumePeriod);
        }
        assert(0, "Invalid month.");
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearMonth(1999, cast(Month) 1).dayOfYear == 1);
        assert(YearMonth(1999, cast(Month) 12).dayOfYear(AssumePeriod.begin) == 335);
        assert(YearMonth(1999, cast(Month) 12).dayOfYear(AssumePeriod.end) == 365);
        assert(YearMonth(2000, cast(Month) 12).dayOfYear(AssumePeriod.begin) == 336);
        assert(YearMonth(2000, cast(Month) 12).dayOfYear(AssumePeriod.end) == 366);
    }

    /++
        Whether this $(LREF Date) is in a leap year.
     +/
    @property bool isLeapYear() const @safe pure nothrow @nogc
    {
        return yearIsLeapYear(year);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearMonth(1999, cast(Month) 12).isLeapYear == false);
        assert(YearMonth(2000, cast(Month) 12).isLeapYear == true);
    }

    /++
        The last day in the month that this $(LREF Date) is in.
      +/
    @property ubyte daysInMonth() const @safe pure nothrow @nogc
    {
        return maxDay(year, month);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        assert(YearMonth(2020, Month.dec).daysInMonth == 31);
    }

    /++
        Whether the current year is a date in A.D.
      +/
    @property bool isAD() const @safe pure nothrow @nogc
    {
        return year > 0;
    }
    
    ///
    version(mir_test)
    @safe unittest
    {
        assert(YearMonth(2020, Month.jan).isAD == true);
    }
}

///
enum Quarter : short
{
    ///
    q1 = 1,
    ///
    q2,
    ///
    q3,
    ///
    q4,
}

/++
Returns the quarter for a given month.

Params:
    month = month

+/
@safe pure @nogc nothrow
Quarter quarter(Month month)
{
    return cast(Quarter)((cast(ubyte)month - 1) / 3 + 1);
}

///
version(mir_test)
@safe pure @nogc nothrow
unittest {
    assert(Month.jan.quarter == Quarter.q1);
    assert(Month.feb.quarter == Quarter.q1);
    assert(Month.mar.quarter == Quarter.q1);
    assert(Month.apr.quarter == Quarter.q2);
    assert(Month.may.quarter == Quarter.q2);
    assert(Month.jun.quarter == Quarter.q2);
    assert(Month.jul.quarter == Quarter.q3);
    assert(Month.aug.quarter == Quarter.q3);
    assert(Month.sep.quarter == Quarter.q3);
    assert(Month.oct.quarter == Quarter.q4);
    assert(Month.nov.quarter == Quarter.q4);
    assert(Month.dec.quarter == Quarter.q4);
}

private
@safe pure @nogc nothrow
Month monthInQuarter(Quarter quarter, AssumePeriod assumePeriod = AssumePeriod.begin)
{
    assert (assumePeriod == AssumePeriod.begin || assumePeriod == AssumePeriod.end);
    return cast(Month) ((cast(byte)quarter - 1) * 3 + 1 + 2 * assumePeriod);
}

version(mir_test)
@safe pure @nogc nothrow
unittest {
    assert(Quarter.q1.monthInQuarter == Month.jan);
    assert(Quarter.q1.monthInQuarter(AssumePeriod.end) == Month.mar);
    assert(Quarter.q2.monthInQuarter == Month.apr);
    assert(Quarter.q2.monthInQuarter(AssumePeriod.end) == Month.jun);
    assert(Quarter.q3.monthInQuarter == Month.jul);
    assert(Quarter.q3.monthInQuarter(AssumePeriod.end) == Month.sep);
    assert(Quarter.q4.monthInQuarter == Month.oct);
    assert(Quarter.q4.monthInQuarter(AssumePeriod.end) == Month.dec);
}

/// Represents a date as a pair of years and quarters. 
@serdeProxy!Timestamp
struct YearQuarter
{
    short year  = 1;
    Quarter quarter = Quarter.q1;
    
    ///
    @property Month month(AssumePeriod assumePeriod = AssumePeriod.begin) const @safe pure nothrow @nogc
    {
        return quarter.monthInQuarter(assumePeriod);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(2000, Quarter.q4);
        assert(yq.month == 10);
        assert(yq.month(AssumePeriod.end) == 12);
    }

    ///
    @property ubyte day(AssumePeriod assumePeriod = AssumePeriod.begin) const @safe pure nothrow @nogc
    {
        final switch (assumePeriod)
        {
            case AssumePeriod.begin:
                return 1;
            case AssumePeriod.end:
                return daysInMonth;
        }
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(2000, Quarter.q4);
        assert(yq.day == 1);
        assert(yq.day(AssumePeriod.end) == 31);
    }

    ///
    Timestamp timestamp() @safe pure nothrow @nogc const @property
    {
        return Timestamp(year, cast(ubyte)month);
    }

    ///
    version(mir_test)
    unittest
    {
        import mir.timestamp;
        auto yq = YearQuarter(2020, Quarter.q2);
        auto ts = yq.timestamp;
    }

    ///
    alias opCast(T : Timestamp) = timestamp;

    ///
    version(mir_test)
    unittest
    {
        import mir.timestamp;
        auto yq = YearQuarter(2020, Quarter.q2);
        auto timestamp = cast(Timestamp) yq;
    }

    ///
    this(short year, Quarter quarter) @safe pure nothrow @nogc
    {
        this.year = year;
        this.quarter = quarter;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(2000, Quarter.q4);
    }

    ///
    this(short year, Month month) @safe pure nothrow @nogc
    {
        this.year = year;
        this.quarter = month.quarter;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(2000, Month.dec);
    }

    ///
    this(Date date) @safe pure nothrow @nogc
    {
        this = date.yearQuarter;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(Date(2000, Month.dec, 31));
    }

    ///
    this(YearMonthDay yearMonthDay) @safe pure nothrow @nogc
    {
        with(yearMonthDay) this(year, quarter);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto ym = YearQuarter(YearMonthDay(2000, Month.dec, 31));
    }

    ///
    this(YearMonth yearMonth) @safe pure nothrow @nogc
    {
        with(yearMonth) this(year, quarter);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(YearMonth(2000, Month.dec));
    }

    version(D_Exceptions)
    ///
    this(Timestamp timestamp) @safe pure @nogc
    {
        if (timestamp.precision != Timestamp.Precision.month)
        {
            static immutable exc = new Exception("YearMonth: invalid timestamp precision");
            { import mir.exception : toMutable; throw exc.toMutable; }
        }
        with(timestamp) this(year, cast(Month)month);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        import mir.timestamp;
        auto ts = Timestamp(2020, 4);
        auto yq = YearQuarter(ts);
    }

    ///
    deprecated("please use addQuarters instead")
    @safe pure nothrow @nogc
    ref YearQuarter add(string units : "quarters")(long quarters)
    {
        auto years = quarters / 4;
        quarters %= 4;
        auto newQuarter = quarter + quarters;

        if (quarters < 0)
        {
            if (newQuarter < 1)
            {
                newQuarter += 4;
                --years;
            }
        }
        else if (newQuarter > 4)
        {
            newQuarter -= 4;
            ++years;
        }

        year += years;
        quarter = cast(Quarter) newQuarter;

        return this;
    }

    ///
    version(mir_test_deprecated)
    @safe unittest
    {
        auto yq0 = YearQuarter(2020, Quarter.q1);

        yq0.add!"quarters"(1);
        assert(yq0.year == 2020);
        assert(yq0.quarter == Quarter.q2);

        auto yq1 = yq0.add!"quarters"(1);
        assert(yq1.year == 2020);
        assert(yq1.quarter == Quarter.q3);

        // also changes yq0
        assert(yq0.year == 2020);
        assert(yq0.quarter == Quarter.q3);

        yq1.add!"quarters"(2);
        assert(yq1.year == 2021);
        assert(yq1.quarter == Quarter.q1);

        yq1.add!"quarters"(-5);
        assert(yq1.year == 2019);
        assert(yq1.quarter == Quarter.q4);
    }

    ///
    deprecated("please use addYears instead")
    @safe pure nothrow @nogc
    ref YearQuarter add(string units : "years")(long years)
    {
        year += years;
        return this;
    }

    ///
    version(mir_test_deprecated)
    @safe unittest
    {
        auto yq0 = YearQuarter(2020, Quarter.q1);

        yq0.add!"years"(1);
        assert(yq0.year == 2021);
        assert(yq0.quarter == Quarter.q1);

        auto yq1 = yq0.add!"years"(1);
        assert(yq1.year == 2022);
        assert(yq1.quarter == Quarter.q1);

        // also changes yq0
        assert(yq0.year == 2022);
        assert(yq0.quarter == Quarter.q1);
    }

    ///
    @safe pure nothrow @nogc
    YearQuarter addQuarters(long quarters)
    {
        auto years = quarters / 4;
        auto newYear = year;
        newYear += years;
        quarters %= 4;
        auto newQuarter = quarter + quarters;

        if (quarters < 0)
        {
            if (newQuarter < 1)
            {
                newQuarter += 4;
                --newYear;
            }
        }
        else if (newQuarter > 4)
        {
            newQuarter -= 4;
            ++newYear;
        }

        return YearQuarter(newYear, cast(Quarter) newQuarter);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto yq0 = YearQuarter(2020, Quarter.q1);

        auto yq1 = yq0.addQuarters(5);
        assert(yq1.year == 2021);
        assert(yq1.quarter == Quarter.q2);

        auto yq2 = yq1.addQuarters(-2);
        assert(yq2.year == 2020);
        assert(yq2.quarter == Quarter.q4);

        auto yq3 = YearQuarter(2020, Quarter.q4).addQuarters(1);
        assert(yq3.year == 2021);
        assert(yq3.quarter == Quarter.q1);

        // yq0 is left unchagned
        assert(yq0.year == 2020);
        assert(yq0.quarter == Quarter.q1);
    }

    ///
    @safe pure nothrow @nogc
    YearQuarter addYears(long years)
    {
        auto newYear = this.year;
        newYear += years;
        return YearQuarter(newYear, quarter);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto yq0 = YearQuarter(2020, Quarter.q1);

        auto yq1 = yq0.addYears(1);
        assert(yq1.year == 2021);
        assert(yq1.quarter == Quarter.q1);
 
        // leaves yq0 unchanged
        assert(yq0.year == 2020);
        assert(yq0.quarter == Quarter.q1);
    }

    private void setQuarterOfYear(bool useExceptions = false)(int days)
    {
        immutable int[] lastDay = isLeapYear ? lastDayQuarterLeap : lastDayQuarterNonLeap;

        bool dayOutOfRange = days <= 0 || days > (isLeapYear ? daysInLeapYear : daysInYear);

        static if (useExceptions)
        {
            if (dayOutOfRange) { import mir.exception : toMutable; throw InvalidDay.toMutable; }
        }
        else
        {
            assert(!dayOutOfRange, "Invalid Day");
        }

        foreach (i; 1 .. lastDay.length)
        {
            if (days <= lastDay[i])
            {
                quarter = cast(Quarter)(cast(int) Quarter.q1 + i - 1);
                return;
            }
        }
        assert(0, "Invalid day of the year.");
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(2020, Quarter.q3);
        yq.setQuarterOfYear(10);
        assert(yq.year == 2020);
        assert(yq.quarter == Quarter.q1);
        yq.setQuarterOfYear(100);
        assert(yq.year == 2020);
        assert(yq.quarter == Quarter.q2);
        yq.setQuarterOfYear(200);
        assert(yq.year == 2020);
        assert(yq.quarter == Quarter.q3);
        yq.setQuarterOfYear(300);
        assert(yq.year == 2020);
        assert(yq.quarter == Quarter.q4);
    }

    ///
    int opBinary(string op : "-")(YearQuarter rhs)
    {
        alias a = this;
        alias b = rhs;
        return (a.year - b.year) * 4 + a.quarter - b.quarter;
    }

    ///
    YearQuarter opBinary(string op)(int rhs)
        if (op == "+" || op == "-")
    {
        static if (op == "+")
           return addQuarters(rhs);
        else
           return addQuarters(-rhs);
    }

    ///
    alias opBinaryRight(string op : "+") = opBinary!"+";

    ///
    ref YearQuarter opOpAssign(string op)(int rhs) return @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        static if (op == "+")
           this = addQuarters(rhs);
        else
           this = addQuarters(-rhs);
        return this;
    }

    ///
    @safe pure @nogc nothrow
    version(mir_test)
    unittest
    {
        auto x = YearQuarter(2020, Quarter.q1);
        auto x1 = x + 1;
        assert(x1 == YearQuarter(2020, Quarter.q2));
        auto x2 = x + 2;
        assert(x2 == YearQuarter(2020, Quarter.q3));
        auto x3 = x + 3;
        assert(x3 == YearQuarter(2020, Quarter.q4));
    }

    ///
    @safe pure @nogc nothrow
    version(mir_test)
    unittest {
        auto yq = YearQuarter(2020, Quarter.q1);
        yq += 2;
        assert(yq == YearQuarter(2020, Quarter.q3));
        yq -= 1;
        assert(yq == YearQuarter(2020, Quarter.q2));
    }

    /// Get a slice of YearQuarters
    @safe pure @nogc nothrow
    version(mir_test)
    unittest {
        import mir.ndslice.topology: iota;

        static immutable result1 = [YearQuarter(2020, Quarter.q1), YearQuarter(2020, Quarter.q2), YearQuarter(2020, Quarter.q3), YearQuarter(2020, Quarter.q4)];
        static immutable result2 = [YearQuarter(2020, Quarter.q1), YearQuarter(2020, Quarter.q3), YearQuarter(2021, Quarter.q1), YearQuarter(2021, Quarter.q3)];

        auto yq = YearQuarter(2020, Quarter.q1);

        auto x = yq + 4.iota!uint;
        assert(x == result1);

        // every other quarter
        auto y = yq + iota!uint([4], 0, 2);
        assert(y == result2);
    }

    /++
        Day of the quarter this $(LREF Date) is on.
      +/
    @property int dayOfQuarter(AssumePeriod assumePeriodMonth, AssumePeriod assumePeriodDay) const @safe pure nothrow @nogc
    {
        if (quarter >= Quarter.q1 && quarter <= Quarter.q4)
        {
            immutable int[] lastDayQuarter = isLeapYear ? lastDayQuarterLeap : lastDayQuarterNonLeap;
            auto quarterIndex = quarter - Quarter.q1;
            immutable int[] lastDay = isLeapYear ? lastDayLeap : lastDayNonLeap;
            auto monthIndex = month(assumePeriodMonth) - Month.jan;

            return lastDay[monthIndex] - lastDayQuarter[quarterIndex] + day(assumePeriodDay);
        }
        assert(0, "Invalid quarter.");
    }

    /// ditto
    @property int dayOfQuarter(AssumePeriod assumePeriod = AssumePeriod.begin) const @safe pure nothrow @nogc
    {
        return dayOfQuarter(assumePeriod, assumePeriod);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearQuarter(1999, cast(Quarter) 1).dayOfQuarter == 1);
        assert(YearQuarter(1999, cast(Quarter) 1).dayOfQuarter(AssumePeriod.begin, AssumePeriod.end) == 31);
        assert(YearQuarter(1999, cast(Quarter) 1).dayOfQuarter(AssumePeriod.end) == 90);

        assert(YearQuarter(2000, cast(Quarter) 1).dayOfQuarter(AssumePeriod.begin, AssumePeriod.end) == 31);
        assert(YearQuarter(2000, cast(Quarter) 1).dayOfQuarter(AssumePeriod.end) == 91);

        assert(YearQuarter(2000, cast(Quarter) 4).dayOfQuarter == 1);
        assert(YearQuarter(2000, cast(Quarter) 4).dayOfQuarter(AssumePeriod.begin, AssumePeriod.end) == 31);
        assert(YearQuarter(2000, cast(Quarter) 4).dayOfQuarter(AssumePeriod.end) == 92);
    }

    /++
        Day of the year this $(LREF Date) is on.
      +/
    @property int dayOfYear(AssumePeriod assumePeriodMonth, AssumePeriod assumePeriodDay) const @safe pure nothrow @nogc
    {
        if (quarter >= Quarter.q1 && quarter <= Quarter.q4)
        {
            immutable int[] lastDayQuarter = isLeapYear ? lastDayQuarterLeap : lastDayQuarterNonLeap;
            auto quarterIndex = quarter - Quarter.q1;

            return lastDayQuarter[quarterIndex] + dayOfQuarter(assumePeriodMonth, assumePeriodDay);
        }
        assert(0, "Invalid quarter.");
    }
    
    /// ditto
    @property int dayOfYear(AssumePeriod assumePeriod = AssumePeriod.begin) const @safe pure nothrow @nogc
    {
        return dayOfYear(assumePeriod, assumePeriod);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearQuarter(1999, cast(Quarter) 1).dayOfYear == 1);
        assert(YearQuarter(1999, cast(Quarter) 4).dayOfYear == 274);
        assert(YearQuarter(1999, cast(Quarter) 4).dayOfYear(AssumePeriod.begin, AssumePeriod.end) == 304);
        assert(YearQuarter(1999, cast(Quarter) 4).dayOfYear(AssumePeriod.end) == 365);
        assert(YearQuarter(2000, cast(Quarter) 4).dayOfYear == 275);
        assert(YearQuarter(2000, cast(Quarter) 4).dayOfYear(AssumePeriod.begin, AssumePeriod.end) == 305);
        assert(YearQuarter(2000, cast(Quarter) 4).dayOfYear(AssumePeriod.end) == 366);
    }

    /++
        Whether this $(LREF Date) is in a leap year.
     +/
    @property bool isLeapYear() const @safe pure nothrow @nogc
    {
        return yearIsLeapYear(year);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(YearQuarter(1999, cast(Quarter) 4).isLeapYear == false);
        assert(YearQuarter(2000, cast(Quarter) 4).isLeapYear == true);
    }

    /++
        The last day in the month that this $(LREF Date) is in.
      +/
    @property ubyte daysInMonth(AssumePeriod assumePeriod = AssumePeriod.begin) const @safe pure nothrow @nogc
    {
        return maxDay(year, month(assumePeriod));
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto yq = YearQuarter(2020, Quarter.q3);
        assert(yq.daysInMonth == 31);
        assert(yq.daysInMonth(AssumePeriod.end) == 30);
    }

    /++
        Whether the current year is a date in A.D.
      +/
    @property bool isAD() const @safe pure nothrow @nogc
    {
        return year > 0;
    }

    ///
    version(mir_test)
    @safe unittest
    {
        assert(YearQuarter(2020, Quarter.q1).isAD == true);
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
// extern(C++, "boost", "gregorian")
// extern(C++, class)
extern(C++, "mir")
@serdeProxy!YearMonthDay
struct Date
{
extern(D):
public:

    private enum _julianShift = 1_721_425;

    ///
    uint toHash() @safe pure nothrow @nogc const scope
    {
        return _dayNumber;
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
                ret._dayNumber = dayOfYear;
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

            ret._dayNumber = days;
        }
        else if (_year == 0)
        {
            ret._dayNumber = dayOfYear - daysInLeapYear;
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

            ret._dayNumber = days;
        }
    R:
        ret._dayNumber -= 1;
        return ret;
    }

    ///
    Timestamp timestamp() @safe pure nothrow @nogc const @property
    {
        return yearMonthDay.timestamp;
    }

    ///
    version(mir_test)
    @safe unittest
    {
        import mir.timestamp;
        auto d1 = Date(2020, Month.may, 15);
        auto ts2 = d1.timestamp;
    }

    version(D_Exceptions)
    ///
    this(Timestamp timestamp) @safe pure @nogc
    {
        if (timestamp.precision != Timestamp.Precision.day)
        {
            static immutable exc = new Exception("Date: invalid timestamp precision");
            { import mir.exception : toMutable; throw exc.toMutable; }
        }
        with(timestamp) this(year, cast(Month)month, day);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        import mir.timestamp;
        auto ts = Date(2020, Month.may, 15).timestamp;
        auto d2 = Date(ts);
    }

    version(D_Exceptions)
    ///
    this(scope const(char)[] str) @safe pure @nogc
    {
        this = fromString(str);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d = Date("2020-12-31");
    }

    version(D_Exceptions)
    ///
    this(YearMonthDay ymd) @safe pure @nogc
    {
        with(ymd) this(year, month, day);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d = Date(YearMonthDay(2020, Month.may, 31));
    }

    version(D_Exceptions)
    ///
    this(YearQuarter yq, AssumePeriod assumePeriodMonth, AssumePeriod assumePeriodDay) @safe pure @nogc
    {
        with(yq) this(year, month(assumePeriodMonth), day(assumePeriodDay));
    }

    version(D_Exceptions)
    ///
    this(YearQuarter yq, AssumePeriod assumePeriod = AssumePeriod.begin) @safe pure @nogc
    {
        this(yq, assumePeriod, assumePeriod);
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d1 = Date(YearQuarter(2020, Quarter.q2));
        auto d2 = Date(YearQuarter(2020, Quarter.q2), AssumePeriod.end);
    }

    version(D_Exceptions)
    ///
    this(YearMonth ym, AssumePeriod assumePeriod = AssumePeriod.begin) @safe pure @nogc nothrow
    {
        with(ym) this = trustedCreate(year, month, day(assumePeriod));
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d1 = Date(YearMonth(2020, Month.may));
        auto d2 = Date(YearMonth(2020, Month.may), AssumePeriod.end);
    }

    version(D_Exceptions)
    ///
    this(int _year, int _month, int _day) @safe pure @nogc
    {
        if (!valid!"months"(_month))
            { import mir.exception : toMutable; throw InvalidMonth.toMutable; }
        if (!valid!"days"(_year, cast(Month) _month, _day))
            { import mir.exception : toMutable; throw InvalidDay.toMutable; }
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

    version (mir_test)
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
    deprecated("Use `fromDayNumber` adjusted by -1_721_426")
    this(int day) @safe pure nothrow @nogc
    {
        _dayNumber = day - (1 + _julianShift);
    }

    version (mir_test)
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
        return this._dayNumber - rhs._dayNumber;
    }

    version (mir_test)
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
        return getDayOfWeek(_dayNumber);
    }

    version (mir_test)
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
    Params:
        dayNumber = Day Of Gregorian Calendar Minus One
    +/
    static Date fromDayNumber(int dayNumber) @safe pure nothrow @nogc
    {
        Date date;
        date._dayNumber = dayNumber;
        return date;
    }

    /++
    Returns;
        Day Of Gregorian Calendar Minus One
    +/
    int dayNumber() @safe pure nothrow @nogc const @property
    {
        return _dayNumber;
    }

    /++
        The Xth day of the Gregorian Calendar that this $(LREF Date) is on.
     +/
    @property int dayOfGregorianCal() const @safe pure nothrow @nogc
    {
        return _dayNumber + 1;
    }

    ///
    version (mir_test)
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

    version (mir_test)
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
        
        Note:
            Zero value corresponds to 
     +/
    @property void dayOfGregorianCal(int day) @safe pure nothrow @nogc
    {
        _dayNumber = day - 1;
    }

    ///
    version (mir_test)
    @safe unittest
    {
        import mir.test;
        auto date = Date.init;
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

    version (mir_test)
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

    private enum uint _startDict = Date(1900, 1, 1)._dayNumber; // [
    private enum uint _endDict = Date(2040, 1, 1)._dayNumber; // )
    static immutable _dictYMD = ()
    {
        YearMonthDay[Date._endDict - Date._startDict] dict;
        foreach (uint i; 0 .. dict.length)
            dict[i] = Date.fromDayNumber(i + Date._startDict).yearMonthDayImpl;
        return dict;
    }();

    ///
    YearMonthDay yearMonthDay() const @safe pure nothrow @nogc @property
    {
        uint day = _dayNumber;
        if (day < _endDict)
        {
            import mir.checkedint: subu;
            bool overflow;
            auto index = subu(day, _startDict, overflow);
            if (!overflow)
                return _dictYMD[index];
        }
        return yearMonthDayImpl;
    }

    ///
    YearQuarter yearQuarter() const @safe pure nothrow @nogc @property
    {
        uint day = _dayNumber;
        if (day < _endDict)
        {
            return yearMonthDay().YearQuarter;
        }
        return yearQuarterImpl;
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d = Date(2020, Month.may, 31);
        auto yq = d.yearQuarter;
        assert(yq.year == 2020);
        assert(yq.quarter == Quarter.q2);
    }

    //
    version(mir_test)
    @safe unittest
    {
        auto d = Date(2050, Month.dec, 31);
        auto yq = d.yearQuarter;
        assert(yq.year == 2050);
        assert(yq.quarter == Quarter.q4);
    }

    ///
    short year() const @safe pure nothrow @nogc @property
    {
        return yearQuarter.year;
    }

    ///
    Quarter quarter() const @safe pure nothrow @nogc @property
    {
        return yearQuarter.quarter;
    }

    ///
    Month month() const @safe pure nothrow @nogc @property
    {
        return yearMonthDay.month;
    }

    ///
    ubyte day() const @safe pure nothrow @nogc @property
    {
        return yearMonthDay.day;
    }

    ///
    version(mir_test)
    @safe unittest
    {
        auto d = Date(2020, Month.may, 31);
        assert(d.year == 2020);
        assert(d.quarter == Quarter.q2);
        assert(d.month == Month.may);
        assert(d.day == 31);
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



    pragma(inline, false)
    YearQuarter yearQuarterImpl() const @safe pure nothrow @nogc @property
    {
        YearQuarter yq;
        int days = dayOfGregorianCal;
        with(yq)
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
                quarter = Quarter.q4;
            }
            else
            {
                year = cast(short) years;
                setQuarterOfYear(days);
            }
        }
        else if (days <= 0 && -days < daysInLeapYear)
        {
            year = 0;

            setQuarterOfYear(daysInLeapYear + days);
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
                quarter = Quarter.q2;
            }
            else
            {
                year = cast(short) years;
                immutable newDoY = (yearIsLeapYear(year) ? daysInLeapYear : daysInYear) + days + 1;

                setQuarterOfYear(newDoY);
            }
        }
        return yq;
    }

    version(mir_test)
    @safe unittest
    {
        auto d = Date(2020, Month.may, 31);
        auto yq = d.yearQuarterImpl;
    }

    /++
     $(LREF Date) for the last day in the quarter that this $(LREF Date) is in.
    +/
    @property Date endOfQuarter() const @safe pure nothrow @nogc
    {
        with(yearMonthDay)
        {
            int d = _dayNumber - day;
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
            return Date.fromDayNumber(d);
        }
    }

    ///
    version (mir_test)
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
            return Date.fromDayNumber(_dayNumber + maxDay(year, month) - day);
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(Date(1999, 1, 6).endOfMonth == Date(1999, 1, 31));
        assert(Date(1999, 2, 7).endOfMonth == Date(1999, 2, 28));
        assert(Date(2000, 2, 7).endOfMonth == Date(2000, 2, 29));
        assert(Date(2000, 6, 4).endOfMonth == Date(2000, 6, 30));
    }

    version (mir_test)
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
    int opBinary(string op : "-")(Date rhs) const
    {
        return _dayNumber - rhs._dayNumber;
    }

    ///
    Date opBinary(string op : "+")(int rhs) const
    {
        return Date.fromDayNumber(_dayNumber + rhs);
    }

    ///
    Date opBinaryRight(string op : "+")(int rhs) const
    {
        return Date.fromDayNumber(_dayNumber + rhs);
    }

    ///
    Date opBinary(string op : "-")(int rhs) const
    {
        return Date.fromDayNumber(_dayNumber - rhs);
    }

    ///
    ref Date opOpAssign(string op)(int rhs) return @safe pure nothrow @nogc
        if (op == "+" || op == "-")
    {
        static if (op == "+")
           this._addDays(rhs);
        else
           this._addDays(-rhs);
        return this;
    }
    
    ///
    @safe pure @nogc
    version(mir_test)
    unittest {
        auto d = Date(2020, 1, 1);
        d += 2;
        assert(d == Date(2020, 1, 3));
        d -= 1;
        assert(d == Date(2020, 1, 2));
    }


    /// Get a slice of Dates
    @safe pure @nogc
    version(mir_test)
    unittest {
        import mir.ndslice.topology: iota, map;

        static immutable result1 = [Date(2020, Month.mar, 1), Date(2020, Month.mar, 2), Date(2020, Month.mar, 3), Date(2020, Month.mar, 4)];
        static immutable result2 = [Date(2020, Month.mar, 1), Date(2020, Month.mar, 3), Date(2020, Month.mar, 5), Date(2020, Month.mar, 7)];
        static immutable result3 = [Date(2020, Month.mar, 1), Date(2020, Month.apr, 1), Date(2020, Month.may, 1), Date(2020, Month.jun, 1)];
        static immutable result4 = [Date(2020, Month.mar, 1), Date(2020, Month.jun, 1), Date(2020, Month.sep, 1), Date(2020, Month.dec, 1)];
        static immutable result5 = [Date(2020, Month.mar, 1), Date(2021, Month.mar, 1), Date(2022, Month.mar, 1), Date(2023, Month.mar, 1)];

        auto d = Date(2020, Month.mar, 1);

        auto x = d + 4.iota!uint;
        assert(x == result1);

        // every other date
        auto y = d + iota!uint([4], 0, 2);
        assert(y == result2);

        // every month
        auto z = (d.YearMonth + 4.iota!uint).map!Date;
        assert(z == result3);

        // every quarter
        auto a = (d.YearQuarter + 4.iota!uint).map!(a => a.Date(AssumePeriod.end, AssumePeriod.begin));
        assert(a == result4);

        // every year
        auto b = (d.year + 4.iota!uint).map!(a => YearMonthDay(cast(short) a, Month.mar, 1).Date);
        assert(b == result5);
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
        return _dayNumber + (1 + _julianShift);
    }

    version (mir_test)
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

    version (mir_test)
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
        import mir.appender: UnsafeArrayBuffer;
        char[16] buffer = void;
        auto w = UnsafeArrayBuffer!char(buffer);
        fun(w);
        return w.data.idup;
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
    version (mir_test)
    @safe unittest
    {
        assert(Date.init.toISOString == "null");
        assert(Date(2010, 7, 4).toISOString == "20100704");
        assert(Date(1998, 12, 25).toISOString == "19981225");
        assert(Date(0, 1, 5).toISOString == "00000105");
        assert(Date(-4, 1, 5).toISOString == "-00040105", Date(-4, 1, 5).toISOString());
    }

    version (mir_test)
    @safe unittest
    {
        // Test A.D.
        assert(Date(9, 12, 4).toISOString == "00091204");
        assert(Date(99, 12, 4).toISOString == "00991204");
        assert(Date(999, 12, 4).toISOString == "09991204");
        assert(Date(9999, 7, 4).toISOString == "99990704");
        assert(Date(10000, 10, 20).toISOString == "+100001020");

        // Test B.C.
        assert(Date(0, 12, 4).toISOString == "00001204");
        assert(Date(-9, 12, 4).toISOString == "-00091204");
        assert(Date(-99, 12, 4).toISOString == "-00991204");
        assert(Date(-999, 12, 4).toISOString == "-09991204");
        assert(Date(-9999, 7, 4).toISOString == "-99990704");
        assert(Date(-10000, 10, 20).toISOString == "-100001020");

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.toISOString == "19990706");
        assert(idate.toISOString == "19990706");
    }

    /// ditto
    void toISOString(W)(scope ref W w) const scope
        if (isOutputRange!(W, char))
    {
        import mir.format: printZeroPad;
        if(this == Date.init)
        {
            w.put("null");
            return;
        }
        with(yearMonthDay)
        {
            if (year >= 10_000)
                w.put('+');
            w.printZeroPad(year, year >= 0 ? year < 10_000 ? 4 : 5 : year > -10_000 ? 5 : 6);
            w.printZeroPad(cast(uint)month, 2);
            w.printZeroPad(day, 2);
        }
    }

    version (mir_test)
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
    version (mir_test)
    @safe unittest
    {
        assert(Date.init.toISOExtString == "null");
        assert(Date(2010, 7, 4).toISOExtString == "2010-07-04");
        assert(Date(1998, 12, 25).toISOExtString == "1998-12-25");
        assert(Date(0, 1, 5).toISOExtString == "0000-01-05");
        assert(Date(-4, 1, 5).toISOExtString == "-0004-01-05");
    }

    version (mir_test)
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

    version (mir_test)
    @safe unittest
    {
        // Test A.D.
        assert(Date(9, 12, 4).toISOExtString == "0009-12-04");
        assert(Date(99, 12, 4).toISOExtString == "0099-12-04");
        assert(Date(999, 12, 4).toISOExtString == "0999-12-04");
        assert(Date(9999, 7, 4).toISOExtString == "9999-07-04");
        assert(Date(10000, 10, 20).toISOExtString == "+10000-10-20");

        // Test B.C.
        assert(Date(0, 12, 4).toISOExtString == "0000-12-04");
        assert(Date(-9, 12, 4).toISOExtString == "-0009-12-04");
        assert(Date(-99, 12, 4).toISOExtString == "-0099-12-04");
        assert(Date(-999, 12, 4).toISOExtString == "-0999-12-04");
        assert(Date(-9999, 7, 4).toISOExtString == "-9999-07-04");
        assert(Date(-10000, 10, 20).toISOExtString == "-10000-10-20");

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.toISOExtString == "1999-07-06");
        assert(idate.toISOExtString == "1999-07-06");
    }

    /// ditto
    void toISOExtString(W)(scope ref W w) const scope
        if (isOutputRange!(W, char))
    {
        import mir.format: printZeroPad;
        if(this == Date.init)
        {
            w.put("null");
            return;
        }
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

    version (mir_test)
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
    version (mir_test)
    @safe unittest
    {
        assert(Date.init.toSimpleString == "null");
        assert(Date(2010, 7, 4).toSimpleString == "2010-Jul-04");
        assert(Date(1998, 12, 25).toSimpleString == "1998-Dec-25");
        assert(Date(0, 1, 5).toSimpleString == "0000-Jan-05");
        assert(Date(-4, 1, 5).toSimpleString == "-0004-Jan-05");
    }

    version (mir_test)
    @safe unittest
    {
        // Test A.D.
        assert(Date(9, 12, 4).toSimpleString == "0009-Dec-04");
        assert(Date(99, 12, 4).toSimpleString == "0099-Dec-04");
        assert(Date(999, 12, 4).toSimpleString == "0999-Dec-04");
        assert(Date(9999, 7, 4).toSimpleString == "9999-Jul-04");
        assert(Date(10000, 10, 20).toSimpleString == "+10000-Oct-20");

        // Test B.C.
        assert(Date(0, 12, 4).toSimpleString == "0000-Dec-04");
        assert(Date(-9, 12, 4).toSimpleString == "-0009-Dec-04");
        assert(Date(-99, 12, 4).toSimpleString == "-0099-Dec-04");
        assert(Date(-999, 12, 4).toSimpleString == "-0999-Dec-04");
        assert(Date(-9999, 7, 4).toSimpleString == "-9999-Jul-04");
        assert(Date(-10000, 10, 20).toSimpleString == "-10000-Oct-20");

        const cdate = Date(1999, 7, 6);
        immutable idate = Date(1999, 7, 6);
        assert(cdate.toSimpleString == "1999-Jul-06");
        assert(idate.toSimpleString == "1999-Jul-06");
    }

    /// ditto
    void toSimpleString(W)(scope ref W w) const scope
        if (isOutputRange!(W, char))
    {
        import mir.format: printZeroPad;
        if(this == Date.init)
        {
            w.put("null");
            return;
        }
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

    version (mir_test)
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
        { import mir.exception : toMutable; throw InvalidISOString.toMutable; }
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(Date.fromISOString("20100704") == Date(2010, 7, 4));
        assert(Date.fromISOString("19981225") == Date(1998, 12, 25));
        assert(Date.fromISOString("00000105") == Date(0, 1, 5));
        assert(Date.fromISOString("-00040105") == Date(-4, 1, 5));
    }

    version (mir_test)
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
    version (mir_test)
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
        { import mir.exception : toMutable; throw InvalidISOExtendedString.toMutable; }
    }

    ///
    version (mir_test)
    @safe unittest
    {
        assert(Date.fromISOExtString("2010-07-04") == Date(2010, 7, 4));
        assert(Date.fromISOExtString("1998-12-25") == Date(1998, 12, 25));
        assert(Date.fromISOExtString("0000-01-05") == Date(0, 1, 5));
        assert(Date.fromISOExtString("-0004-01-05") == Date(-4, 1, 5));
    }

    version (mir_test)
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
    version (mir_test)
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
    version (mir_test)
    @safe unittest
    {
        assert(Date.fromSimpleString("2010-Jul-04") == Date(2010, 7, 4));
        assert(Date.fromSimpleString("1998-Dec-25") == Date(1998, 12, 25));
        assert(Date.fromSimpleString("0000-Jan-05") == Date(0, 1, 5));
        assert(Date.fromSimpleString("-0004-Jan-05") == Date(-4, 1, 5));
    }

    version (mir_test)
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
    version (mir_test)
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
    version (mir_test)
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
        { import mir.exception : toMutable; throw InvalidString.toMutable; }
    }

    /++
        Returns the $(LREF Date) farthest in the past which is representable by
        $(LREF Date).
      +/
    @property static Date min() @safe pure nothrow @nogc
    {
        return Date.fromDayNumber(int.max);
    }

    /++
        Returns the $(LREF Date) farthest in the future which is representable
        by $(LREF Date).
      +/
    @property static Date max() @safe pure nothrow @nogc
    {
        return Date.fromDayNumber(int.min);
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
        _dayNumber = cast(int)(_dayNumber + days);
        return this;
    }

    version (mir_test)
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

    int _dayNumber;
}

/// ditto
deprecated("use `Date` instead")
alias date = Date;

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
version (mir_test)
@safe pure nothrow @nogc unittest
{
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.mon) == 0);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.sun) == 6);
    assert(daysToDayOfWeek(DayOfWeek.mon, DayOfWeek.wed) == 2);
}

version (mir_test)
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

version (mir_test)
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
    Array of integers representing the last days of each quarter in a year.
  +/
immutable int[5] lastDayQuarterNonLeap = [0, 90, 181, 273, 365];

/+
    Array of integers representing the last days of each quarter in a leap year.
  +/
immutable int[5] lastDayQuarterLeap = [0, 91, 182, 274, 366];

/+
    Returns the string representation of the given month.
  +/
string monthToString(Month month) @safe pure @nogc nothrow
{
    assert(month >= Month.jan && month <= Month.dec, "Invalid month");
    return _monthNames[month - Month.jan];
}

version (mir_test)
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

version (mir_test)
version(unittest)
{
    // All of these helper arrays are sorted in ascending order.
    auto testYearsBC = [-1999, -1200, -600, -4, -1, 0];
    auto testYearsAD = [1, 4, 1000, 1999, 2000, 2012];

    // I'd use a Tuple, but I get forward reference errors if I try.
    static struct MonthDay
    {
        Month month;
        short day;

        this(int m, short d) @safe
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
