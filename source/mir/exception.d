/++
`@nogc` exceptions and errors definitions.

Most of the API Requires DIP1008.
+/
module mir.exception;

version(D_Exceptions):

version(D_Ddoc)
    private enum _version_D_Ddoc = true;
else
    private enum _version_D_Ddoc = false;

private enum NOGCEXP = __traits(compiles, (()@nogc {throw new Exception("");})());

package template staticException(string fmt, string file, int line)
{
    static immutable staticException = new Exception(fmt, file, line);
}

///
auto ref enforce(string fmt, string file = __FILE__, int line = __LINE__, Expr)(scope auto return ref Expr arg) @trusted
{
    version(LDC) pragma(inline, true);
    import core.lifetime: forward;
    import mir.utility: _expect;
    static if (__traits(compiles, arg !is null))
    {
        if (_expect(arg !is null, true))
            return forward!arg;
    }
    else
    {
        if (_expect(cast(bool)arg, true))
            return forward!arg;
    }
    throw staticException!(fmt, file, line);
}

///
@safe pure nothrow @nogc
version (mir_test) unittest
{
    import mir.exception;
    try enforce!"Msg"(false);
    catch(Exception e) assert(e.msg == "Msg");
}

/++
+/
class MirException : Exception
{
    ///
    mixin MirThrowableImpl;
}

/// Generic style
version (mir_test) static if (NOGCEXP)
@safe pure nothrow @nogc
unittest
{
    import mir.exception;
    try throw new MirException("Hi D", 2, "!");
    catch(Exception e) assert(e.msg == "Hi D2!");
}

/// C++ style
version (mir_test) static if (NOGCEXP)
@safe pure nothrow @nogc
unittest
{
    import mir.exception;
    import mir.format;
    try throw new MirException(stringBuf() << "Hi D" << 2 << "!" << getData);
    catch(Exception e) assert(e.msg == "Hi D2!");
}

/// Low-level style
version (mir_test) static if (NOGCEXP)
@safe pure nothrow @nogc
unittest
{
    import mir.exception;
    import mir.format;
    stringBuf buf;
    try throw new MirException(buf.print( "Hi D", 2, "!").data);
    catch(Exception e) assert(e.msg == "Hi D2!");
}

///
version (mir_test) static if (NOGCEXP)
@safe pure nothrow @nogc
unittest
{
    @safe pure nothrow @nogc 
    bool func(scope const(char)[] msg)
    {
        /// scope messages are copied
        try throw new MirException(msg);
        catch(Exception e) assert(e.msg == msg);

        /// immutable strings are not copied
        static immutable char[] gmsg = "global msg";
        try throw new MirException(gmsg);
        catch(Exception e) assert(e.msg is gmsg);

        return __ctfe;
    }

    assert(func("runtime-time check") == 0);

    static assert(func("compile-time check") == 1);
}

// ///
// auto ref enforce(T, Args...)(scope auto return ref T arg, lazy @nogc Args args, string file = __FILE__, int line = __LINE__) @nogc
//     if (Args.length)
// {
//     import mir.utility: _expect;
//     static if (__traits(compiles, arg !is null))
//     {
//         if (_expect(arg !is null, true))
//             return arg;
//     }
//     else
//     {
//         if (_expect(cast(bool)arg, true))
//             return arg;
//     }
//     import mir.format;
//     stringBuf buf;
//     throw new MirException(buf.print(args).data, file, line);
// }

// ///
// @safe pure nothrow @nogc
// version (mir_test) unittest static if (NOGCEXP)
// {
//     import mir.exception;
//     try enforce(false, "Hi D", 2, "!");
//     catch(Exception e) assert(e.msg == "Hi D2!");
// }

// ///
// auto ref enforce(T)(scope auto return ref T arg, lazy scope const(char)[] msg, string file = __FILE__, int line = __LINE__) @nogc
// {
//     import core.lifetime: forward;
//     import mir.utility: _expect;
//     static if (__traits(compiles, arg !is null))
//     {
//         if (_expect(arg !is null, true))
//             return forward!arg[0];
//     }
//     else
//     {
//         if (_expect(cast(bool)arg, true))
//             return forward!arg[0];
//     }
//     throw new MirException(msg, file, line);
// }

// ///
// @safe pure nothrow @nogc
// version (mir_test) unittest static if (NOGCEXP)
// {
//     import mir.exception;
//     try enforce(false, "Msg");
//     catch(Exception e) assert(e.msg == "Msg");
// }


/++
+/
class MirError : Error
{
    ///
    mixin MirThrowableImpl;
}

///
@system pure nothrow @nogc
version (mir_test) static if (NOGCEXP)
unittest
{
    @system pure nothrow @nogc 
    bool func(scope const(char)[] msg)
    {
        /// scope messages are copied
        try throw new MirException(msg);
        catch(Exception e) assert(e.msg == msg);
    
        /// immutable strings are not copied
        static immutable char[] gmsg = "global msg";
        try throw new MirError(gmsg);
        catch(Error e) assert(e.msg is gmsg);
    
        return __ctfe;
    }

    assert(func("runtime-time check") == 0);

    static assert(func("compile-time check") == 1);
}

/++
+/
mixin template MirThrowableImpl()
{
    private bool _global;
    private char[maxMsgLen] _payload = void;

    /++
    Params:
        msg = message. No-scope `msg` is assumed to have the same lifetime as the throwable. scope strings are copied to internal buffer.
        file = file name, zero terminated global string
        line = line number
        nextInChain = next exception in the chain (optional)
    +/
    @nogc @safe pure nothrow this(scope const(char)[] msg, string file = __FILE__, size_t line = __LINE__, Throwable nextInChain = null)
    {
        super((() @trusted => cast(immutable) mirExceptionInitilizePayloadImpl(_payload, msg))(), file, line, nextInChain);
    }

    /// ditto
    @nogc @safe pure nothrow this(scope const(char)[] msg, Throwable nextInChain, string file = __FILE__, size_t line = __LINE__)
    {
        this(msg, file, line, nextInChain);
    }

    /// ditto
    @nogc @safe pure nothrow this(string msg, string file = __FILE__, size_t line = __LINE__, Throwable nextInChain = null)
    {
        this._global = true;
        super(msg, file, line, nextInChain);
    }

    /// ditto
    @nogc @safe pure nothrow this(string msg, Throwable nextInChain, string file = __FILE__, size_t line = __LINE__)
    {
        this._global = true;
        super(msg, file, line, nextInChain);
    }

    ///
    ~this() @trusted
    {
        import mir.internal.memory: free;
        if (!_global && msg.ptr != _payload.ptr)
            free(cast(void*)msg.ptr);
    }

    /++
    Generic multiargument overload.
    Constructs a string using the `print` function.
    +/
    @nogc @safe pure nothrow this(Args...)(scope auto ref Args args, string file = __FILE__, size_t line = __LINE__, Throwable nextInChain = null)
        if (Args.length > 1)
    {
        import mir.format;
        stringBuf buf;
        this(buf.print(args).data, file, line, nextInChain);
    }
}

private enum maxMsgLen = 447;

pragma(inline, false)
pure nothrow @nogc @safe
const(char)[] mirExceptionInitilizePayloadImpl(ref return char[maxMsgLen] payload, scope const(char)[] msg)
{
    import mir.internal.memory: malloc;
    import core.stdc.string: memcpy;
    if (msg.length > payload.length)
    {
        if (auto ret = (() @trusted
            {
                if (__ctfe)
                    return null;
                if (auto ptr = malloc(msg.length))
                {
                    memcpy(ptr, msg.ptr, msg.length);
                    return cast(const(char)[]) ptr[0 .. msg.length];
                }
                return null;
            })())
            return ret;
        msg = msg[0 .. payload.length];
        // remove tail UTF-8 symbol chunk if any
        uint c = msg[$-1];
        if (c > 0b_0111_1111)
        {
            do {
                c = msg[$-1];
                msg = msg[0 .. $ - 1];
            }
            while (msg.length && c < 0b_1100_0000);
        }
    }
    if (__ctfe)
        payload[][0 .. msg.length] = msg;
    else
        (() @trusted => memcpy(payload.ptr, msg.ptr, msg.length))();
    return payload[0 .. msg.length];
}
