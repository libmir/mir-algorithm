/++
Ranges.

See_also: $(MREF mir,_primitives).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2017-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
+/
module mir.range;

/++
Data size counter.

Does not store anything
+/
struct Counter(T)
{
    import std.range: isInputRange, ElementType;
    import std.traits: isImplicitlyConvertible, isSomeChar;
    ///
    size_t _count;

    /// Data count.
    size_t count()() @property
    {
        return _count;
    }

    private template canPutItem(U)
    {
        enum bool canPutItem =
            isImplicitlyConvertible!(U, T) ||
            isSomeChar!T && isSomeChar!U;
    }

    private template canPutRange(Range)
    {
        import std.array: front;
        enum bool canPutRange =
            isInputRange!Range &&
            is(typeof(Counter.init.put(Range.init.front)));
    }

    ///
    void put(U)(auto ref U item) if (canPutItem!U)
    {
        static if (isSomeChar!T && isSomeChar!U && T.sizeof < U.sizeof)
        {
            import std.utf: codeLength;
            _count += codeLength!T(item);
        }
        else
        {
            _count++;
        }
    }

    ///
    void put(Range)(Range items) if (canPutRange!Range)
    {
        // note, we disable this branch for appending one type of char to
        // another because we can't trust the length portion.
        static if (!(isSomeChar!T && isSomeChar!(ElementType!Range) &&
                     !is(immutable Range == immutable T[])) &&
                    is(typeof(items.length) == size_t))
        {
            _count += items.length;
        }
        else
        {
            import std.utf: codeLength;
            _count += codeLength!T(items);
        }
    }
}

///
unittest
{
    Counter!char counter;
    counter.put("Мир");
    assert(counter.count == 6);
}

///
unittest
{
    Counter!wchar counter;
    counter.put("Мир");
    assert(counter.count == 3);
}
