/++
Timestamp
+/
module mir.timestamp;

private alias isDigit = (dchar c) => uint(c - '0') < 10;

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
    private static immutable InvalidString = new DateTimeException("Invalid String");
}

/++
Timestamp

Note: The component values in the binary encoding are always in UTC, while components in the text encoding are in the local time!
This means that transcoding requires a conversion between UTC and local time.

`Timestamp` precision is up to `10^-12` seconds;
+/
struct Timestamp
{
    import std.traits: isSomeChar;

    ///
    enum Precision : ubyte
    {
        ///
        year,
        ///
        month,
        ///
        day,
        ///
        minute,
        ///
        second,
        ///
        fraction,
    }

    ///
    this(scope const(char)[] str) @safe pure @nogc
    {
        this = fromString(str);
    }

    ///
    version (mir_test)
    @safe pure @nogc unittest
    {
        assert(Timestamp("2010-07-04") == Timestamp(2010, 7, 4));
        assert(Timestamp("20100704") == Timestamp(2010, 7, 4));
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30) == Timestamp.fromISOString("20210129T201244+0730"));
        static assert(Timestamp(2021, 01, 29,  4, 42, 44).withOffset(- (7 * 60 + 30)) == Timestamp.fromISOExtString("2021-01-28T21:12:44-07:30"));
    }

    version(all)
    {
        short offset;
    }
    else
    /+
    If the time in UTC is known, but the offset to local time is unknown, this can be represented with an offset of “-00:00”.
    This differs semantically from an offset of “Z” or “+00:00”, which imply that UTC is the preferred reference point for the specified time.
    RFC2822 describes a similar convention for email.
    private short _offset;
    +/
    {

        /++
        Timezone offset in minutes
        +/
        short offset() const @safe pure nothrow @nogc @property
        {
            return _offset >> 1;
        }

        /++
        Returns: true if timezone has offset
        +/
        bool hasOffset() const @safe pure nothrow @nogc @property
        {
            return _offset & 1;
        }
    }

    /++
    Year
    +/
    short year;
    /++
    +/
    Precision precision;

    /++
    Month
    
    If the value equals to thero then this and all the following members are undefined.
    +/
    ubyte month;
    /++
    Day
    
    If the value equals to thero then this and all the following members are undefined.
    +/
    ubyte day;
    /++
    Hour
    +/
    ubyte hour;

    version(D_Ddoc)
    {
    
        /++
        Minute

        Note: the field is implemented as property.
        +/
        ubyte minute;
        /++
        Second

        Note: the field is implemented as property.
        +/
        ubyte second;
        /++
        Fraction

        The `fraction_exponent` and `fraction_coefficient` denote the fractional seconds of the timestamp as a decimal value
        The fractional seconds’ value is `coefficient * 10 ^ exponent`.
        It must be greater than or equal to zero and less than 1.
        A missing coefficient defaults to zero.
        Fractions whose coefficient is zero and exponent is greater than -1 are ignored.
        
        'fractionCoefficient' allowed values are [0 ... 10^12-1].
        'fractionExponent' allowed values are [-12 ... 0].

        Note: the fields are implemented as property.
        +/
        byte fractionExponent;
        /// ditto
        long fractionCoefficient;
    }
    else
    {
        import mir.bitmanip: bitfields;
        version (LittleEndian)
        {

            mixin(bitfields!(
                    ubyte, "minute", 8,
                    ubyte, "second", 8,
                    byte, "fractionExponent", 8,
                    long, "fractionCoefficient", 40,
            ));
        }
        else
        {
            mixin(bitfields!(
                    long, "fractionCoefficient", 40,
                    byte, "fractionExponent", 8,
                    ubyte, "second", 8,
                    ubyte, "minute", 8,
            ));
        }
    }

    ///
    @safe pure nothrow @nogc
    this(short year)
    {
        this.year = year;
        this.precision = Precision.year;
    }

    ///
    @safe pure nothrow @nogc
    this(short year, ubyte month)
    {
        this.year = year;
        this.month = month;
        this.precision = Precision.month;
    }

    ///
    @safe pure nothrow @nogc
    this(short year, ubyte month, ubyte day)
    {
        this.year = year;
        this.month = month;
        this.day = day;
        this.precision = Precision.day;
    }

    ///
    @safe pure nothrow @nogc
    this(short year, ubyte month, ubyte day, ubyte hour, ubyte minute)
    {
        this.year = year;
        this.month = month;
        this.day = day;
        this.hour = hour;
        this.minute = minute;
        this.precision = Precision.minute;
    }

    ///
    @safe pure nothrow @nogc
    this(short year, ubyte month, ubyte day, ubyte hour, ubyte minute, ubyte second)
    {
        this.year = year;
        this.month = month;
        this.day = day;
        this.hour = hour;
        this.day = day;
        this.minute = minute;
        this.second = second;
        this.precision = Precision.second;
    }

    ///
    @safe pure nothrow @nogc
    this(short year, ubyte month, ubyte day, ubyte hour, ubyte minute, ubyte second, byte fractionExponent, ulong fractionCoefficient)
    {
        this.year = year;
        this.month = month;
        this.day = day;
        this.hour = hour;
        this.day = day;
        this.minute = minute;
        this.second = second;
        assert(fractionExponent < 0);
        this.fractionExponent = fractionExponent;
        this.fractionCoefficient = fractionCoefficient;
        this.precision = Precision.fraction;
    }

    /++
    Attaches local offset, doesn't adjust other fields.
    Local-time offsets may be represented as either `hour*60+minute` offsets from UTC,
    or as the zero to denote a local time of UTC. They are required on timestamps with time and are not allowed on date values.
    +/
    @safe pure nothrow @nogc const
    Timestamp withOffset(short minutes)
    {
        assert(-24 * 60 <= minutes && minutes <= 24 * 60, "Offset absolute value should be less or equal to 24 * 60");
        assert(precision >= Precision.minute, "Offsets are not allowed on date values.");
        Timestamp ret = this;
        ret.offset = minutes;
        return ret;
    }

    version(D_BetterC){} else
    private string toStringImpl(alias fun)() const @safe pure nothrow
    {
        import mir.appender: UnsafeArrayBuffer;
        char[64] buffer = void;
        auto w = UnsafeArrayBuffer!char(buffer);
        fun(w);
        return w.data.idup;
    }

    /++
    Converts this $(LREF Timestamp) to a string with the format `YYYY-MM-DDThh:mm:ss±hh:mm`.

    If `w` writer is set, the resulting string will be written directly
    to it.

    Returns:
        A `string` when not using an output range; `void` otherwise.
    +/
    alias toISOExtString = toISOStringImp!true;

    ///
    version (mir_test)
    @safe pure nothrow unittest
    {
        assert(Timestamp.init.toString == "0000T");
        assert(Timestamp(2010, 7, 4).toString == "2010-07-04");
        assert(Timestamp(1998, 12, 25).toString == "1998-12-25");
        assert(Timestamp(0, 1, 5).toString == "0000-01-05");
        assert(Timestamp(-4, 1, 5).toString == "-0004-01-05");

        // YYYY-MM-DDThh:mm:ss±hh:mm
        assert(Timestamp(2021).toString == "2021T");
        assert(Timestamp(2021, 01).toString == "2021-01T", Timestamp(2021, 01).toString);
        assert(Timestamp(2021, 01, 29).toString == "2021-01-29");
        assert(Timestamp(2021, 01, 29, 19, 42).toString == "2021-01-29T19:42Z");
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60).toString == "2021-01-29T19:42:44+07", Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60).toString);
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30).toString == "2021-01-29T20:12:44+07:30");
    }

    ///
    version (mir_test)
    @safe unittest
    {
        // Test A.D.
        assert(Timestamp(9, 12, 4).toISOExtString == "0009-12-04");
        assert(Timestamp(99, 12, 4).toISOExtString == "0099-12-04");
        assert(Timestamp(999, 12, 4).toISOExtString == "0999-12-04");
        assert(Timestamp(9999, 7, 4).toISOExtString == "9999-07-04");
        assert(Timestamp(10000, 10, 20).toISOExtString == "+10000-10-20");

        // Test B.C.
        assert(Timestamp(0, 12, 4).toISOExtString == "0000-12-04");
        assert(Timestamp(-9, 12, 4).toISOExtString == "-0009-12-04");
        assert(Timestamp(-99, 12, 4).toISOExtString == "-0099-12-04");
        assert(Timestamp(-999, 12, 4).toISOExtString == "-0999-12-04");
        assert(Timestamp(-9999, 7, 4).toISOExtString == "-9999-07-04");
        assert(Timestamp(-10000, 10, 20).toISOExtString == "-10000-10-20");

        const cdate = Timestamp(1999, 7, 6);
        immutable idate = Timestamp(1999, 7, 6);
        assert(cdate.toISOExtString == "1999-07-06");
        assert(idate.toISOExtString == "1999-07-06");
    }

    /// ditto
    alias toString = toISOExtString;

    /++
    Converts this $(LREF Timestamp) to a string with the format `YYYYMMDDThhmmss±hhmm`.

    If `w` writer is set, the resulting string will be written directly
    to it.

    Returns:
        A `string` when not using an output range; `void` otherwise.
    +/
    alias toISOString = toISOStringImp!false;

    ///
    version (mir_test)
    @safe pure nothrow unittest
    {
        assert(Timestamp.init.toISOString == "0000T");
        assert(Timestamp(2010, 7, 4).toISOString == "20100704");
        assert(Timestamp(1998, 12, 25).toISOString == "19981225");
        assert(Timestamp(0, 1, 5).toISOString == "00000105");
        assert(Timestamp(-4, 1, 5).toISOString == "-00040105");

        // YYYYMMDDThhmmss±hhmm
        assert(Timestamp(2021).toISOString == "2021T");
        assert(Timestamp(2021, 01).toISOString == "2021-01T"); // always extended
        assert(Timestamp(2021, 01, 29).toISOString == "20210129");
        assert(Timestamp(2021, 01, 29, 19, 42).toISOString == "20210129T1942Z");
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60).toISOString == "20210129T194244+07");
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30).toISOString == "20210129T201244+0730");
        static assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30).toISOString == "20210129T201244+0730");
    }

    /// Helpfer for time zone offsets
    void addMinutes(short minutes) @safe pure nothrow @nogc
    {
        int totalMinutes = minutes + (this.minute + this.hour * 60u);
        auto h = totalMinutes / 60;

        int dayShift;

        while (totalMinutes < 0)
        {
            totalMinutes += 24 * 60;
            dayShift--;
        }

        while (totalMinutes >= 24 * 60)
        {
            totalMinutes -= 24 * 60;
            dayShift++;
        }

        if (dayShift)
        {
            import mir.date: Date;
            auto ymd = (Date.trustedCreate(year, month, day) + dayShift).yearMonthDay;
            year = ymd.year;
            month = cast(ubyte)ymd.month;
            day = ymd.day;
        }

        hour = cast(ubyte) (totalMinutes / 60);
        minute = cast(ubyte) (totalMinutes % 60);
    }

    template toISOStringImp(bool ext)
    {
        version(D_BetterC){} else
        string toISOStringImp() const @safe pure nothrow
        {
            return toStringImpl!toISOStringImp;
        }

        /// ditto
        void toISOStringImp(W)(scope ref W w) const scope
            // if (isOutputRange!(W, char))
        {
            import mir.format: printZeroPad;
            // YYYY-MM-DDThh:mm:ss±hh:mm
            Timestamp t = this;

            if (t.offset)
            {
                assert(-24 * 60 <= t.offset && t.offset <= 24 * 60, "Offset absolute value should be less or equal to 24 * 60");
                assert(precision >= Precision.minute, "Offsets are not allowed on date values.");
                t.addMinutes(t.offset);
            }

            if (t.year >= 10_000)
                w.put('+');
            printZeroPad(w, t.year, t.year >= 0 ? t.year < 10_000 ? 4 : 5 : t.year > -10_000 ? 5 : 6);
            if (precision == Precision.year)
            {
                w.put('T');
                return;
            }
            if (ext || precision == Precision.month) w.put('-');

            printZeroPad(w, cast(uint)t.month, 2);
            if (precision == Precision.month)
            {
                w.put('T');
                return;
            }
            static if (ext) w.put('-');

            printZeroPad(w, t.day, 2);
            if (precision == Precision.day)
                return;
            w.put('T');

            printZeroPad(w, t.hour, 2);
            static if (ext) w.put(':');
            printZeroPad(w, t.minute, 2);

            if (precision >= Precision.second)
            {
                static if (ext) w.put(':');
                printZeroPad(w, t.second, 2);

                if (precision > Precision.second && (t.fractionExponent < 0 || t.fractionCoefficient))
                {
                    w.put('.');
                    printZeroPad(w, t.fractionCoefficient, -int(t.fractionExponent));
                }
            }

            if (t.offset == 0)
            {
                w.put('Z');
                return;
            }

            bool sign = t.offset < 0;
            uint absoluteOffset = !sign ? t.offset : -int(t.offset);
            uint offsetHour = absoluteOffset / 60u;
            uint offsetMinute = absoluteOffset % 60u;

            w.put(sign ? '-' : '+');
            printZeroPad(w, offsetHour, 2);
            if (offsetMinute)
            {
                static if (ext) w.put(':');
                printZeroPad(w, offsetMinute, 2);
            }
        }
    }

    /++
    Creates a $(LREF Timestamp) from a string with the format `YYYYMMDDThhmmss±hhmm
    or its leading part allowed by the standard.

    or its leading part allowed by the standard.

    Params:
        str = A string formatted in the way that $(LREF .Timestamp.toISOExtString) formats dates.
        value = (optional) result value.

    Throws:
        $(LREF DateTimeException) if the given string is
        not in the correct format. Two arguments overload is `nothrow`.
    Returns:
        `bool` on success for two arguments overload, and the resulting timestamp for single argument overdload.
    +/
    alias fromISOString = fromISOStringImpl!false;

    ///
    version (mir_test)
    @safe unittest
    {
        assert(Timestamp.fromISOString("20100704") == Timestamp(2010, 7, 4));
        assert(Timestamp.fromISOString("19981225") == Timestamp(1998, 12, 25));
        assert(Timestamp.fromISOString("00000105") == Timestamp(0, 1, 5));
        // assert(Timestamp.fromISOString("-00040105") == Timestamp(-4, 1, 5));

        assert(Timestamp(2021) == Timestamp.fromISOString("2021"));
        assert(Timestamp(2021) == Timestamp.fromISOString("2021T"));
        // assert(Timestamp(2021, 01) == Timestamp.fromISOString("2021-01"));
        // assert(Timestamp(2021, 01) == Timestamp.fromISOString("2021-01T"));
        assert(Timestamp(2021, 01, 29) == Timestamp.fromISOString("20210129"));
        assert(Timestamp(2021, 01, 29, 19, 42) == Timestamp.fromISOString("20210129T1942"));
        assert(Timestamp(2021, 01, 29, 19, 42) == Timestamp.fromISOString("20210129T1942Z"));
        assert(Timestamp(2021, 01, 29, 19, 42, 12) == Timestamp.fromISOString("20210129T194212"));
        assert(Timestamp(2021, 01, 29, 19, 42, 12, -3, 67) == Timestamp.fromISOString("20210129T194212.067Z"));
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60) == Timestamp.fromISOString("20210129T194244+07"));
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30) == Timestamp.fromISOString("20210129T201244+0730"));
        static assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30) == Timestamp.fromISOString("20210129T201244+0730"));
        static assert(Timestamp(2021, 01, 29,  4, 42, 44).withOffset(- (7 * 60 + 30)) == Timestamp.fromISOString("20210128T211244-0730"));
    }

    version (mir_test)
    @safe unittest
    {
        import std.exception: assertThrown;
        assertThrown!DateTimeException(Timestamp.fromISOString(""));
        assertThrown!DateTimeException(Timestamp.fromISOString("990704"));
        assertThrown!DateTimeException(Timestamp.fromISOString("0100704"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010070"));
        assertThrown!DateTimeException(Timestamp.fromISOString("120100704"));
        assertThrown!DateTimeException(Timestamp.fromISOString("-0100704"));
        assertThrown!DateTimeException(Timestamp.fromISOString("+0100704"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010070a"));
        assertThrown!DateTimeException(Timestamp.fromISOString("20100a04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010a704"));

        assertThrown!DateTimeException(Timestamp.fromISOString("99-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-07-0"));
        assertThrown!DateTimeException(Timestamp.fromISOString("12010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("-010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("+010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-07-0a"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-0a-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-a7-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010/07/04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010/7/04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010/7/4"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010/07/4"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-7-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-7-4"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-07-4"));

        assertThrown!DateTimeException(Timestamp.fromISOString("99Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010Jul0"));
        assertThrown!DateTimeException(Timestamp.fromISOString("12010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("-010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("+010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010Jul0a"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010Jua04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010aul04"));

        assertThrown!DateTimeException(Timestamp.fromISOString("99-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-Jul-0"));
        assertThrown!DateTimeException(Timestamp.fromISOString("12010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("-010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("+010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-Jul-0a"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-Jua-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-Jal-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-aul-04"));

        // assertThrown!DateTimeException(Timestamp.fromISOString("2010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOString("2010-Jul-04"));

        assert(Timestamp.fromISOString("19990706") == Timestamp(1999, 7, 6));
        // assert(Timestamp.fromISOString("-19990706") == Timestamp(-1999, 7, 6));
        // assert(Timestamp.fromISOString("+019990706") == Timestamp(1999, 7, 6));
        assert(Timestamp.fromISOString("19990706") == Timestamp(1999, 7, 6));
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
                assert(Timestamp.fromISOString(to!S("20121221")) == Timestamp(2012, 12, 21));
        }
    }

    /++
    Creates a $(LREF Timestamp) from a string with the format `YYYY-MM-DDThh:mm:ss±hh:mm`
    or its leading part allowed by the standard.


    Params:
        str = A string formatted in the way that $(LREF .Timestamp.toISOExtString) formats dates.
        value = (optional) result value.

    Throws:
        $(LREF DateTimeException) if the given string is
        not in the correct format. Two arguments overload is `nothrow`.
    Returns:
        `bool` on success for two arguments overload, and the resulting timestamp for single argument overdload.
    +/
    alias fromISOExtString = fromISOStringImpl!true;


    ///
    version (mir_test)
    @safe unittest
    {
        assert(Timestamp.fromISOExtString("2010-07-04") == Timestamp(2010, 7, 4));
        assert(Timestamp.fromISOExtString("1998-12-25") == Timestamp(1998, 12, 25));
        assert(Timestamp.fromISOExtString("0000-01-05") == Timestamp(0, 1, 5));
        assert(Timestamp.fromISOExtString("-0004-01-05") == Timestamp(-4, 1, 5));

        assert(Timestamp(2021) == Timestamp.fromISOExtString("2021"));
        assert(Timestamp(2021) == Timestamp.fromISOExtString("2021T"));
        assert(Timestamp(2021, 01) == Timestamp.fromISOExtString("2021-01"));
        assert(Timestamp(2021, 01) == Timestamp.fromISOExtString("2021-01T"));
        assert(Timestamp(2021, 01, 29) == Timestamp.fromISOExtString("2021-01-29"));
        assert(Timestamp(2021, 01, 29, 19, 42) == Timestamp.fromISOExtString("2021-01-29T19:42"));
        assert(Timestamp(2021, 01, 29, 19, 42) == Timestamp.fromISOExtString("2021-01-29T19:42Z"));
        assert(Timestamp(2021, 01, 29, 19, 42, 12) == Timestamp.fromISOExtString("2021-01-29T19:42:12"));
        assert(Timestamp(2021, 01, 29, 19, 42, 12, -3, 67) == Timestamp.fromISOExtString("2021-01-29T19:42:12.067Z"));
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60) == Timestamp.fromISOExtString("2021-01-29T19:42:44+07"));
        assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30) == Timestamp.fromISOExtString("2021-01-29T20:12:44+07:30"));
        static assert(Timestamp(2021, 01, 29, 12, 42, 44).withOffset(7 * 60 + 30) == Timestamp.fromISOExtString("2021-01-29T20:12:44+07:30"));
        static assert(Timestamp(2021, 01, 29,  4, 42, 44).withOffset(- (7 * 60 + 30)) == Timestamp.fromISOExtString("2021-01-28T21:12:44-07:30"));
    }

    version (mir_test)
    @safe unittest
    {
        import std.exception: assertThrown;

        assertThrown!DateTimeException(Timestamp.fromISOExtString(""));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("990704"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("0100704"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("120100704"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("-0100704"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("+0100704"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010070a"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("20100a04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010a704"));

        assertThrown!DateTimeException(Timestamp.fromISOExtString("99-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-07-0"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("12010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("-010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("+010-07-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-07-0a"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-0a-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-a7-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010/07/04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010/7/04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010/7/4"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010/07/4"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-7-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-7-4"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-07-4"));

        assertThrown!DateTimeException(Timestamp.fromISOExtString("99Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010Jul0"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("12010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("-010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("+010Jul04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010Jul0a"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010Jua04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010aul04"));

        assertThrown!DateTimeException(Timestamp.fromISOExtString("99-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-Jul-0"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("12010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("-010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("+010-Jul-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-Jul-0a"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-Jua-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-Jal-04"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-aul-04"));

        assertThrown!DateTimeException(Timestamp.fromISOExtString("20100704"));
        assertThrown!DateTimeException(Timestamp.fromISOExtString("2010-Jul-04"));

        assert(Timestamp.fromISOExtString("1999-07-06") == Timestamp(1999, 7, 6));
        assert(Timestamp.fromISOExtString("-1999-07-06") == Timestamp(-1999, 7, 6));
        assert(Timestamp.fromISOExtString("+01999-07-06") == Timestamp(1999, 7, 6));
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
                assert(Timestamp.fromISOExtString(to!S("2012-12-21")) == Timestamp(2012, 12, 21));
        }
    }

    /++
    Creates a $(LREF Timestamp) from a string with the format YYYY-MM-DD, YYYYMMDD, or YYYY-Mon-DD.

    Params:
        str = A string formatted in the way that $(LREF .Timestamp.toISOExtString) and $(LREF .Timestamp.toISOString) format dates. The function is case sensetive.
        value = (optional) result value.

    Throws:
        $(LREF DateTimeException) if the given string is
        not in the correct format. Two arguments overload is `nothrow`.
    Returns:
        `bool` on success for two arguments overload, and the resulting timestamp for single argument overdload.
    +/
    static bool fromString(C)(scope const(C)[] str, out Timestamp value) @safe pure nothrow @nogc
    {
        return fromISOExtString(str, value)
            || fromISOString(str, value);
    }

    ///
    version (mir_test)
    @safe pure @nogc unittest
    {
        assert(Timestamp.fromString("2010-07-04") == Timestamp(2010, 7, 4));
        assert(Timestamp.fromString("20100704") == Timestamp(2010, 7, 4));
    }

    /// ditto
    static Timestamp fromString(C)(scope const(C)[] str) @safe pure
        if (isSomeChar!C)
    {
        Timestamp ret;
        if (fromString(str, ret))
            return ret;
        throw InvalidString;
    }

    template fromISOStringImpl(bool ext)
    {
        static Timestamp fromISOStringImpl(C)(scope const(C)[] str) @safe pure
            if (isSomeChar!C)
        {
            Timestamp ret;
            if (fromISOStringImpl(str, ret))
                return ret;
            throw InvalidISOExtendedString;
        }

        static bool fromISOStringImpl(C)(scope const(C)[] str, out Timestamp value) @safe pure nothrow @nogc
            if (isSomeChar!C)
        {
            import mir.parse: fromString, parse;

            // YYYY
            static if (ext)
            {{
                auto startIsDigit = str.length && str[0].isDigit;
                auto strOldLength = str.length;
                if (!parse(str, value.year))
                    return false;
                auto l = strOldLength - str.length;
                if ((l == 4) != startIsDigit)
                    return false;
            }}
            else
            {
                if (str.length < 4 || !str[0].isDigit || !fromString(str[0 .. 4], value.year))
                    return false;
                str = str[4 .. $];
            }

            value.precision = Precision.year;
            if (str.length == 0 || str == "T")
                return true;
            
            static if (ext)
            {
                if (str[0] != '-')
                    return false;
                str = str[1 .. $];
            }

            // MM
            if (str.length < 2 || !str[0].isDigit || !fromString(str[0 .. 2], value.month))
                return false;
            str = str[2 .. $];
            value.precision = Precision.month;
            if (str.length == 0 || str == "T")
                return ext;

            static if (ext)
            {
                if (str[0] != '-')
                    return false;
                str = str[1 .. $];
            }

            // DD
            if (str.length < 2 || !str[0].isDigit || !fromString(str[0 .. 2], value.day))
                return false;
            str = str[2 .. $];
            value.precision = Precision.day;
            if (str.length == 0)
                return true;

            // T
            if (str[0] != 'T')
                return false;
            str = str[1 .. $];
            if (str.length == 0)
                return true;

            // hh
            if (str.length < 4 + ext || !str[0].isDigit || !fromString(str[0 .. 2], value.hour))
                return false;
            str = str[2 .. $];

            static if (ext)
            {
                if (str[0] != ':')
                    return false;
                str = str[1 .. $];
            }

            // mm
            {
                uint minute;
                if (!str[0].isDigit || !fromString(str[0 .. 2], minute))
                    return false;
                value.minute = cast(ubyte) minute;
                str = str[2 .. $];
                value.precision = Precision.minute;
                if (str.length == 0)
                    return true;
            }

            static if (ext)
            {
                if (str[0] != ':')
                    goto TZ;
                str = str[1 .. $];
            }

            // ss
            {
                uint second;
                if (str.length < 2 || !str[0].isDigit)
                    goto TZ;
                if (!fromString(str[0 .. 2], second))
                    return false;
                value.second = cast(ubyte) second;
                str = str[2 .. $];
                value.precision = Precision.second;
                if (str.length == 0)
                    return true;
            }

            // .
            if (str[0] != '.')
                goto TZ;
            str = str[1 .. $];
            value.precision = Precision.fraction;

            // fraction
            {
                const strOldLength = str.length;
                ulong fractionCoefficient;
                if (str.length < 1 || !str[0].isDigit || !parse!ulong(str, fractionCoefficient))
                    return false;
                sizediff_t fractionExponent = str.length - strOldLength;
                if (fractionExponent < -12)
                    return false;
                value.fractionExponent = cast(byte)fractionExponent;
                value.fractionCoefficient = fractionCoefficient;
                if (str.length == 0)
                    return true;
            }

        TZ:

            if (str == "Z")
                return true;

            int hour;
            int minute;
            if (str.length < 3 || str[0].isDigit || !fromString(str[0 .. 3], hour))
                return false;
            str = str[3 .. $];

            if (str.length)
            {
                static if (ext)
                {
                    if (str[0] != ':')
                        return false;
                    str = str[1 .. $];
                }
                if (str.length != 2 || !str[0].isDigit || !fromString(str[0 .. 2], minute))
                    return false;
            }

            value.offset = cast(short)(hour * 60 + (hour < 0 ? -minute : minute));
            value.addMinutes(cast(short)-int(value.offset));
            return true;
        }
    }
}
