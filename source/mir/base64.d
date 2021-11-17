/++
$(H1 @nogc Simple Base64 parsing)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Harrison Ford
Copyright: 2021 Harrison Ford, Kaleidic Associates Advisory Limited, Symmetry Investments
+/
module mir.base64;
import mir.ndslice.topology;

package static immutable base64DecodeInvalidCharMsg = "Invalid character encountered.";
package static immutable base64DecodeInvalidLenMsg = "Cannot decode a buffer with given length (not a multiple of 4, missing padding?)";
version(D_Exceptions) {
    package static immutable base64DecodeInvalidCharException = new Exception(base64DecodeInvalidCharMsg);
    package static immutable base64DecodeInvalidLenException = new Exception(base64DecodeInvalidLenMsg);
}

// NOTE: I do not know if this would work on big-endian systems.
// Needs further testing to figure out if it *does* work on them.

// Technique borrowed from http://0x80.pl/notesen/2016-01-12-sse-base64-encoding.html#branchless-code-for-lookup-table
private char lookup_encoding(char PlusChar = '+', char SlashChar = '/')(ubyte i) @safe @nogc pure {
    assert(i < 64);

    ubyte shift;

    if (i < 26)
    {
        // range A-Z
        shift = 'A';
    }
    else if (i >= 26 && i < 52)
    {
        // range a-z
        shift = 'a' - 26;
    }
    else if (i >= 52 && i < 62)
    {
        // range 0-9
        shift = cast(ubyte)('0' - 52);
    }
    else if (i == 62)
    {
        // character plus
        shift = cast(ubyte)(PlusChar - 62);
    }
    else if (i == 63)
    {
        // character slash
        shift = cast(ubyte)(SlashChar - 63);
    }

    return cast(char)(i + shift);
}

// Do the inverse of above (convert an ASCII value into the Base64 character set)
private ubyte lookup_decoding(char PlusChar = '+', char SlashChar = '/')(char i) @safe @nogc pure
{
    // Branching bad, but this isn't performance sensitive
    if (i <= 'Z' && i >= 'A') {
        return cast(ubyte)(i - 'A');
    }
    else if (i <= 'z' && i >= 'a') {
        return cast(ubyte)(i - 'a' + 26); 
    }
    else if (i <= '9' && i >= '0') {
        return cast(ubyte)(i - '0' + 52);
    }
    else if (i == PlusChar) {
        return 62;
    }
    else if (i == SlashChar) {
        return 63;
    }
    // Just return 0 for padding,
    // as it typically means nothing.
    else if (i == '=') {
        return 0;
    }
    else {
        version(D_Exceptions) {
            throw base64DecodeInvalidCharException;
        } else {
            assert(0, base64DecodeInvalidCharMsg);
        }
    }

}

/++
Decode a Base64 encoded value, returning the buffer.
+/
ubyte[] decodeBase64(char PlusChar = '+', char SlashChar = '/')(scope const(char)[] data) @safe pure
{
    import mir.appender : scopedBuffer;
    auto app = scopedBuffer!ubyte;
    decodeBase64!(PlusChar, SlashChar)(data, app);
    return app.data.dup;
}

/++
Decode a Base64 encoded value, placing the result onto an Appender.
+/
void decodeBase64(char PlusChar = '+', char SlashChar = '/', Appender)(scope const(char)[] data,
                                                                       scope return ref Appender appender) @safe pure
{
    import mir.ndslice.slice : sliced;
    import mir.ndslice.chunks : chunks;
    // We expect data should be well-formed (with padding),
    // so we should throw if it is not well-formed.
    if (data.length % 4 != 0)
    {
        version(D_Exceptions) {
            throw base64DecodeInvalidLenException;
        } else {
            assert(0, base64DecodeInvalidLenMsg);
        }
    }
    
    ubyte[3] decodedByteGroup;
    ubyte sz = 0;
    auto groups = data.sliced.chunks(4);
    for (size_t i = 0; i < groups.length; i++)
    {
        auto group = groups[i];

        ubyte[4] decodedBytes;
        decodedBytes[0] = lookup_decoding!(PlusChar, SlashChar)(group[0]);
        decodedBytes[1] = lookup_decoding!(PlusChar, SlashChar)(group[1]);

        uint transformed_group = (decodedBytes[0] << 26) | (decodedBytes[1] << 20);

        // According to RFC4648 Section 3.3, we don't have to accept extra padding characters,
        // and we can safely throw (and stay within spec).
        // x=== is also invalid, so we can just throw on that here.
        if (group[0] == '=' || group[1] == '=')
        {
            version(D_Exceptions)
                throw base64DecodeInvalidCharException;
            else
                assert(0, base64DecodeInvalidCharMsg);
        }

        // xx=(=)?
        if (group[2] == '=')
        {
            // If we are not at the end of a string, according to RFC4648,
            // we can safely treat a padding character as "non-alphabet data",
            // and as such, we should throw. See RFC4648 Section 3.3 for more information
            if (i != (groups.length - 1))
            {
                version(D_Exceptions)
                    throw base64DecodeInvalidCharException;
                else
                    assert(0, base64DecodeInvalidCharMsg);
            }

            if (group[3] == '=')
            {
                // xx==
                sz = 1;
            }
            // xx=x (invalid)
            // Padding should not be in the middle of a chunk
            else
            {
                version(D_Exceptions)
                    throw base64DecodeInvalidCharException;
                else
                    assert(0, base64DecodeInvalidCharMsg);
            }
        }
        // xxx=
        else if (group[3] == '=')
        {
            // If we are not at the end of a string, according to RFC4648,
            // we can safely treat a padding character as "non-alphabet data",
            // and as such, we should throw. See RFC4648 Section 3.3 for more information
            if (i != (groups.length - 1))
            {
                version(D_Exceptions)
                    throw base64DecodeInvalidCharException;
                else
                    assert(0, base64DecodeInvalidCharMsg);
            }

            decodedBytes[2] = lookup_decoding!(PlusChar, SlashChar)(group[2]);
            transformed_group |= (decodedBytes[2] << 14);
            sz = 2;
        }
        // xxxx
        else 
        {
            decodedBytes[2] = lookup_decoding!(PlusChar, SlashChar)(group[2]);
            decodedBytes[3] = lookup_decoding!(PlusChar, SlashChar)(group[3]);
            transformed_group |= ((decodedBytes[2] << 14) | (decodedBytes[3] << 8)); 
            sz = 3;
        }

        decodedByteGroup[0] = (transformed_group >> 24) & 0xff;
        decodedByteGroup[1] = (transformed_group >> 16) & 0xff;
        decodedByteGroup[2] = (transformed_group >> 8) & 0xff;

        // Only emit the transformed bytes that we got data for. 
        appender.put(decodedByteGroup[0 .. sz]);
    }
}

/// Test decoding of data which has a length which can be
/// cleanly decoded.
unittest
{
    {
        enum data = "QUJD";
        assert(data.decodeBase64 == "ABC");
    }

    {
        enum data = "QQ==";
        assert(data.decodeBase64 == "A");
    }

    {
        enum data = "YSBiIGMgZCBlIGYgZyBoIGkgaiBrIGwgbSBuIG8gcCBxIHIgcyB0IHUgdiB3IHggeSB6";
        assert(data.decodeBase64 == "a b c d e f g h i j k l m n o p q r s t u v w x y z");
    }

    {
        enum data = "LCAuIDsgLyBbICcgXSBcID0gLSAwIDkgOCA3IDYgNSA0IDMgMiAxIGAgfiAhIEAgIyAkICUgXiAmICogKCApIF8gKyB8IDogPCA+ID8=";
        assert(data.decodeBase64 == ", . ; / [ ' ] \\ = - 0 9 8 7 6 5 4 3 2 1 ` ~ ! @ # $ % ^ & * ( ) _ + | : < > ?");
    }

    {
        enum data = "AAA=";
        assert(data.decodeBase64 == "\x00\x00");
    }

    {
        enum data = "AAAABBCC";
        assert(data.decodeBase64 == "\x00\x00\x00\x04\x10\x82");
    }

    {
        enum data = "AA==";
        assert(data.decodeBase64 == "\x00");
    }
    
    {
        enum data = "AA/=";
        assert(data.decodeBase64 == "\x00\x0f");
    }
}

/// Test decoding invalid data
unittest
{
    void testFail(const(char)[] input)
    {
        bool thrown = false;
        try {
            ubyte[] decoded = input.decodeBase64;
        } catch (Throwable t) {
            thrown = true;
        }

        assert(thrown);
    }

    testFail("===A");
    testFail("A=");
    testFail("AA=");
    testFail("A=AA");
    testFail("AA=A");
    testFail("AA=A====");
    testFail("=AAA");
    testFail("AAA=QUJD");
    // This fails because we don't allow extra padding (than what is necessary)
    testFail("AA======");
    // This fails because we don't allow padding before the end of the string (otherwise we'd have a side-channel)
    testFail("QU==QUJD");
    testFail("QU======QUJD");
    // Invalid data that's out of the alphabet
    testFail("!@##@@!@");
}

/++
Encode a ubyte array as Base64, returning the encoded value.
+/
const(char)[] encodeBase64(char PlusChar = '+', char SlashChar = '/')(scope const(ubyte)[] buf) @safe pure
{
    import mir.appender : scopedBuffer;
    // XXX: is a stringBuf more appropriate here?
    auto app = scopedBuffer!char;
    encodeBase64!(PlusChar, SlashChar)(buf, app);
    return app.data.dup;
}

/++
Encode a ubyte array as Base64, placing the result onto an Appender.
+/
void encodeBase64(char PlusChar = '+', char SlashChar = '/', Appender)(scope const(ubyte)[] input,
                                                                       scope return ref Appender appender) @safe pure
{
    import mir.ndslice.topology : bytegroup, map;
    import core.bitop : bswap;
    // Slice our input array so that n % 3 == 0 (we have a multiple of 3) 
    // If we have less then 3, then this is effectively a no-op (will result in a 0-length slice)
    char[4] encodedByteGroup;
    const(ubyte)[] window = input[0 .. input.length - (input.length % 3)];
    foreach(group; window.bytegroup!(3, uint).map!bswap) {
        const(ubyte) a = (group >> 26) & 0x3f;
        const(ubyte) b = (group >> 20) & 0x3f;
        const(ubyte) c = (group >> 14) & 0x3f;
        const(ubyte) d = (group >> 8) & 0x3f;

        encodedByteGroup[0] = a.lookup_encoding!(PlusChar, SlashChar);
        encodedByteGroup[1] = b.lookup_encoding!(PlusChar, SlashChar);
        encodedByteGroup[2] = c.lookup_encoding!(PlusChar, SlashChar);
        encodedByteGroup[3] = d.lookup_encoding!(PlusChar, SlashChar);
        appender.put(encodedByteGroup[]);
    }

    // If it's a clean multiple of 3, then it requires no padding.
    // If not, then we need to add padding.
    if (input.length % 3 != 0)
    {
        window = input[window.length .. input.length];

        uint group = (window[0] << 24);

        if (window.length == 1) {
            const(ubyte) a = (group >> 26) & 0x3f;
            const(ubyte) b = (group >> 20) & 0x3f;
            encodedByteGroup[0] = a.lookup_encoding!(PlusChar, SlashChar);
            encodedByteGroup[1] = b.lookup_encoding!(PlusChar, SlashChar);
            encodedByteGroup[2] = '=';
            encodedByteGroup[3] = '=';
            appender.put(encodedByteGroup[]);
        }
        else {
            // Just in case math fails or something
            assert(window.length == 2);

            group |= (window[1] << 16);
            const(ubyte) a = (group >> 26) & 0x3f;
            const(ubyte) b = (group >> 20) & 0x3f;
            const(ubyte) c = (group >> 14) & 0x3f;
            encodedByteGroup[0] = a.lookup_encoding!(PlusChar, SlashChar);
            encodedByteGroup[1] = b.lookup_encoding!(PlusChar, SlashChar);
            encodedByteGroup[2] = c.lookup_encoding!(PlusChar, SlashChar);
            encodedByteGroup[3] = '=';
            appender.put(encodedByteGroup[]);
        }
    }
}

/// Test encoding of data which has a length that can be cleanly
/// encoded.
unittest
{
    // 3 bytes
    {
        enum data = cast(ubyte[])"ABC";
        assert(data.encodeBase64 == "QUJD");
    }

    // 6 bytes
    {
        enum data = cast(ubyte[])"ABCDEF";
        assert(data.encodeBase64 == "QUJDREVG");
    }

    // 9 bytes
    {
        enum data = cast(ubyte[])"ABCDEFGHI";
        assert(data.encodeBase64 == "QUJDREVGR0hJ");
    }

    // 12 bytes
    {
        enum data = cast(ubyte[])"ABCDEFGHIJKL";
        assert(data.encodeBase64 == "QUJDREVGR0hJSktM");
    }
}

/// Test encoding of data which has a length which CANNOT be cleanly encoded.
/// This typically means that there's padding.
unittest
{
    // 1 byte 
    {
        enum data = cast(ubyte[])"A";
        assert(data.encodeBase64 == "QQ==");
    }
    // 2 bytes
    {
        enum data = cast(ubyte[])"AB";
        assert(data.encodeBase64 == "QUI=");
    }
    // 4 bytes
    {
        enum data = [0xDE, 0xAD, 0xBA, 0xBE];
        assert(data.encodeBase64 == "3q26vg==");
    }
    // 37 bytes
    {
        enum data = cast(ubyte[])"A Very Very Very Very Large Test Blob";
        assert(data.encodeBase64 == "QSBWZXJ5IFZlcnkgVmVyeSBWZXJ5IExhcmdlIFRlc3QgQmxvYg==");
    }
}

/// Make sure we can decode what we encode.
unittest
{
    // Test an example string
    {
        enum data = cast(ubyte[])"abc123!?$*&()'-=@~";
        assert(data.encodeBase64.decodeBase64 == data);
    }
    // Test an example from Ion data
    {
        enum data = cast(ubyte[])"a b c d e f g h i j k l m n o p q r s t u v w x y z";
        assert(data.encodeBase64.decodeBase64 == data);
    }
}