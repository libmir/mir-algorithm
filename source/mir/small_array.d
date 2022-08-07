/++
$(H1 Small Array)

The module contains self-contained generic small array implementaton.

$(LREF SmallArray) supports ASDF - Json Serialisation Library.

Copyright: 2020 Ilia Ki, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilia Ki
+/
module mir.small_array;

private static immutable errorMsg = "Cannot create SmallArray: input range exceeds maximum allowed length.";
version(D_Exceptions)
    private static immutable exception = new Exception(errorMsg);

///
template SmallArray(T, uint maxLength)
    if (maxLength)
{
    import mir.serde: serdeProxy, serdeScoped;
    import std.traits: Unqual, isIterable, isImplicitlyConvertible;

    static if (isImplicitlyConvertible!(const T, T))
        alias V = const T;
    else
        alias V = T;

    ///
    @serdeScoped
    @serdeProxy!(V[])
    struct SmallArray
    {
        uint _length;
        T[maxLength] _data;

        ///
        alias serdeKeysProxy = T;

    @safe pure @nogc:

        /// Constructor
        this(typeof(null))
        {
        }

        /// ditto
        this(scope V[] array)
        {
            this.opAssign(array);
        }

        /// ditto
        this(const SmallArray array) nothrow
        {
            this.opAssign(array);
        }

        /// ditto
        this(uint n)(const SmallArray!(T, n) array)
        {
            this.opAssign(array);
        }

        /// ditto
        this(uint n)(ref const SmallArray!(T, n) array)
        {
            this.opAssign(array);
        }

        /// ditto
        this(Range)(auto ref Range array)
            if (isIterable!Range)
        {
            foreach(ref c; array)
            {
                if (_length > _data.length)
                {
                    version(D_Exceptions) throw exception;
                    else assert(0, errorMsg);
                }
                _data[_length++] = c;
            }
        }

        /// `=` operator
        ref typeof(this) opAssign(typeof(null)) return
        {
            _length = 0;
            _data = T.init;
            return this;
        }

        /// ditto
        ref typeof(this) opAssign(V[] array) return @trusted
        {
            if (array.length > maxLength)
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data[0 .. _length] = T.init;
            _length = cast(uint) array.length;
            _data[0 .. _length] = array;
            return this;
        }

        /// ditto
        ref typeof(this) opAssign(ref const SmallArray rhs) return nothrow
        {
            _length = rhs._length;
            _data = rhs._data;
            return this;
        }
        
        /// ditto
        ref typeof(this) opAssign(const SmallArray rhs) return nothrow
        {
            _length = rhs._length;
            _data = rhs._data;
            return this;
        }

        /// ditto
        ref typeof(this) opAssign(uint n)(ref const SmallArray!(T, n) rhs) return
            if (n != maxLength)
        {
            static if (n < maxLength)
            {
                _data[0 .. n] = rhs._data;
                if (_length > n)
                    _data[n .. _length] = T.init;
            }
            else
            {
                if (rhs._length > maxLength)
                {
                    version(D_Exceptions) throw exception;
                    else assert(0, errorMsg);
                }
                _data = rhs._data[0 .. maxLength];
            }
            _length = rhs._length;
            return this;
        }

        /// ditto
        ref typeof(this) opAssign(uint n)(const SmallArray!(T, n) rhs) return
            if (n != maxLength)
        {
            static if (n < maxLength)
            {
                _data[0 .. n] = rhs._data;
                if (_length > n)
                    _data[n .. _length] = T.init;
            }
            else
            {
                if (rhs._length > maxLength)
                {
                    version(D_Exceptions) throw exception;
                    else assert(0, errorMsg);
                }
                _data = rhs._data[0 .. maxLength];
            }
            _length = rhs._length;
            return this;
        }

        ///
        void trustedAssign(V[] array) @trusted
        {
            _data[0 .. _length] = T.init;
            _length = cast(uint) array.length;
            _data[0 .. _length] = array;
        }

        ///
        ref typeof(this) append(T elem)
        {
            import core.lifetime: move;
            if (_length == maxLength)
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data[_length++] = move(elem);
            return this;
        }

        ///
        void trustedAppend(T elem)
        {
            import core.lifetime: move;
            _data[_length++] = move(elem);
        }

        ///
        ref typeof(this) append(V[] array)
        {
            if (_length + array.length > maxLength)
            {
                version(D_Exceptions) throw exception;
                else assert(0, errorMsg);
            }
            _data[_length .. _length + array.length] = array;
            _length += array.length;
            return this;
        }

        /// ditto
        alias put = append;

        /// ditto
        alias opOpAssign(string op : "~") = append;

        ///
        SmallArray concat(V[] array) scope const
        {
            SmallArray c = this;
            c.append(array);
            return c; 
        }

        /// ditto
        alias opBinary(string op : "~") = concat;

        /++
        Returns an scope common array.

        The property is used as common array representation self alias.

        The alias helps with `[]`, `[i]`, `[i .. j]`, `==`, and `!=` operations and implicit conversion to strings.
        +/
        inout(T)[] opIndex() inout @trusted return scope
        {
            return _data[0 .. _length];
        }

        ///
        ref inout(T) opIndex(size_t index) inout return scope
        {
            return opIndex[index];
        }

    const:

        ///
        bool empty() @property
        {
            return _length == 0;
        }

        ///
        size_t length() @property
        {
            return _length;
        }

        /// Hash implementation
        size_t toHash()
        {
            return hashOf(opIndex);
        }

        /// Comparisons operator overloads
        bool opEquals(ref const SmallArray rhs)
        {
            return opIndex == rhs.opIndex;
        }

        /// ditto
        bool opEquals(SmallArray rhs)
        {
            return opIndex == rhs.opIndex;
        }

        /// ditto
        bool opEquals()(V[] array)
        {
            return opIndex == array;
        }

        /// ditto
        bool opEquals(uint rhsMaxLength)(auto ref SmallArray!(T, rhsMaxLength) array)
        {
            return opIndex == array.opIndex;
        }

        /// ditto
        auto opCmp()(V[] array)
        {
            return __cmp(opIndex, array);
        }

        /// ditto
        auto opCmp(uint rhsMaxLength)(auto ref SmallArray!(T, rhsMaxLength) array)
        {
            return __cmp(opIndex, array.opIndex);
        }
    }
}

///
@safe pure @nogc version(mir_test) unittest
{
    SmallArray!(char, 16) s16;
    assert(s16.empty);

    auto s8 = SmallArray!(char, 8)("Hellow!!");
    assert(!s8.empty);
    assert(s8 == "Hellow!!");

    s16 = s8;
    assert(s16 == "Hellow!!");
    s16[7] = '@';
    s8 = null;
    assert(s8.empty);
    assert(s8 == null);
    s8 = s16;
    assert(s8 == "Hellow!@");

    auto s8_2 = s8;
    assert(s8_2 == "Hellow!@");
    assert(s8_2 == s8);

    assert(s8 < "Hey");
    assert(s8 > "Hellow!");

    assert(s8.opCmp("Hey") < 0);
    assert(s8.opCmp(s8) == 0);
}

/// Concatenation
@safe pure @nogc version(mir_test) unittest
{
    auto a = SmallArray!(char, 16)("asdf");
    a ~= " ";
    auto b = a ~ "qwerty";
    static assert(is(typeof(b) == SmallArray!(char, 16)));
    assert(b == "asdf qwerty");
    b.put('!');
    b.put("!");
    assert(b == "asdf qwerty!!");
}
