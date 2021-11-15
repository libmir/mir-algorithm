/++
$(H1 @nogc Simple Base64 parsing)

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Harrison Ford
Copyright: 2021 Harrison Ford, Kaleidic Associates Advisory Limited, Symmetry Investments
+/
module mir.base64;
import mir.ndslice.topology;
import core.bitop : bswap;

package static immutable base64DecodeInvalidCharMsg = "Invalid character encountered.";
package static immutable base64DecodeInvalidLenMsg = "Cannot decode a buffer with given length (not a multiple of 4, missing padding?)";
version(D_Exceptions) {
    package static immutable base64DecodeInvalidCharException = new Exception(base64DecodeInvalidCharMsg);
    package static immutable base64DecodeInvalidLenException = new Exception(base64DecodeInvalidLenMsg);
}

// NOTE: I do not know if this would work on big-endian systems.
// Needs further testing to figure out if it *does* work on them.

// Technique borrowed from http://0x80.pl/notesen/2016-01-12-sse-base64-encoding.html#branchless-code-for-lookup-table
private char lookup_encoding(ubyte i) @safe @nogc pure {
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
        shift = cast(ubyte)('+' - 62);
    }
    else if (i == 63)
    {
        // character slash
        shift = cast(ubyte)('/' - 63);
    }

    return cast(char)(i + shift);
}

// Do the inverse of above (convert an ASCII value into the Base64 character set)
private ubyte lookup_decoding(char i) @safe @nogc pure
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
    else if (i == '+') {
        return 62;
    }
    else if (i == '/') {
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
ubyte[] decodeBase64(scope ubyte[] buf) @safe pure
{
    import mir.appender : scopedBuffer;
    auto app = scopedBuffer!ubyte;
    decodeBase64(buf, app);
    return app.data.dup;
}

/++
Decode a Base64 encoded value, placing the result onto an Appender.
+/
void decodeBase64(Appender)(scope ubyte[] input, ref Appender appender) @safe @nogc pure
{
    // We expect data should be well-formed (with padding),
    // so we should throw if it is not well-formed.
    if (input.length % 4 != 0)
    {
        version(D_Exceptions) {
            throw base64DecodeInvalidLenException;
        } else {
            assert(0, base64DecodeInvalidLenMsg);
        }
    }
    foreach(group; input.bytegroup!(4, uint).map!bswap)
    {
        // We only expect valid ASCII values for these,
        // hence the 0x7f.
        const(ubyte) a = lookup_decoding((group >> 24) & 0x7f);
        const(ubyte) b = lookup_decoding((group >> 16) & 0x7f);
        const(ubyte) c = lookup_decoding((group >> 8) & 0x7f);
        const(ubyte) d = lookup_decoding((group) & 0x7f);

        // We do the inverse of how we encoded it...
        uint transformed_group = (a << 26) | (b << 20) | (c << 14) | (d << 8);

        const(ubyte) t_a = (transformed_group >> 24) & 0xff;
        const(ubyte) t_b = (transformed_group >> 16) & 0xff;
        const(ubyte) t_c = (transformed_group >> 8) & 0xff;
        const(ubyte) t_d = (transformed_group) & 0xff;

        // We should *always* have enough for at least
        // one, but we don't need to have enough for the rest..
        appender.put(t_a);

        // Only emit transformed groups if we have enough data for them.
        if (t_b == 0 && t_c == 0 && t_d == 0)
        {
            return;
        }
        else if (t_c == 0 && t_d == 0)
        {
            appender.put(t_b);
        } 
        else if (t_d == 0)
        {
            appender.put(t_b);
            appender.put(t_c);
        }
        else
        {
            appender.put(t_b);
            appender.put(t_c);
            appender.put(t_d);
        }
    }
}

/// Test decoding of data which has a length which can be
/// cleanly decoded.
unittest
{
    {
        ubyte[] data = cast(ubyte[])"QUJD";
        assert(data.decodeBase64 == "ABC");
    }

    {
        ubyte[] data = cast(ubyte[])"QQ==";
        assert(data.decodeBase64 == "A");
    }

    {
        ubyte[] data = cast(ubyte[])"YSBiIGMgZCBlIGYgZyBoIGkgaiBrIGwgbSBuIG8gcCBxIHIgcyB0IHUgdiB3IHggeSB6";
        assert(data.decodeBase64 == "a b c d e f g h i j k l m n o p q r s t u v w x y z");
    }

    {
        ubyte[] data = cast(ubyte[])"LCAuIDsgLyBbICcgXSBcID0gLSAwIDkgOCA3IDYgNSA0IDMgMiAxIGAgfiAhIEAgIyAkICUgXiAmICogKCApIF8gKyB8IDogPCA+ID8=";
        assert(data.decodeBase64 == ", . ; / [ ' ] \\ = - 0 9 8 7 6 5 4 3 2 1 ` ~ ! @ # $ % ^ & * ( ) _ + | : < > ?");
    }
}

/++
Encode a ubyte array as Base64, returning the encoded value.
+/
ubyte[] encodeBase64(scope ubyte[] buf) @safe pure
{
    import mir.appender : scopedBuffer;
    auto app = scopedBuffer!ubyte;
    encodeBase64(buf, app);
    return app.data.dup;
}

/++
Encode a ubyte array as Base64, placing the result onto an Appender.
+/
void encodeBase64(Appender)(scope ubyte[] input, ref Appender appender) @safe @nogc pure
{
    // Slice our input array so that n % 3 == 0 (we have a multiple of 3) 
    // If we have less then 3, then this is effectively a no-op (will result in a 0-length slice)
    ubyte[] window = input[0 .. input.length - (input.length % 3)];
    foreach(group; window.bytegroup!(3, uint).map!bswap) {
        const(ubyte) a = (group >> 26) & 0x3f;
        const(ubyte) b = (group >> 20) & 0x3f;
        const(ubyte) c = (group >> 14) & 0x3f;
        const(ubyte) d = (group >> 8) & 0x3f;

        appender.put(a.lookup_encoding);
        appender.put(b.lookup_encoding);
        appender.put(c.lookup_encoding);
        appender.put(d.lookup_encoding);
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
            appender.put(a.lookup_encoding);
            appender.put(b.lookup_encoding);
            appender.put('=');
            appender.put('=');
        }
        else {
            // Just in case math fails or something
            assert(window.length == 2);

            group |= (window[1] << 16);
            const(ubyte) a = (group >> 26) & 0x3f;
            const(ubyte) b = (group >> 20) & 0x3f;
            const(ubyte) c = (group >> 14) & 0x3f;
            appender.put(a.lookup_encoding);
            appender.put(b.lookup_encoding);
            appender.put(c.lookup_encoding);
            appender.put('=');
        }
    }
}

/// Test encoding of data which has a length that can be cleanly
/// encoded.
unittest
{
    // 3 bytes
    {
        ubyte[] data = cast(ubyte[])"ABC";
        assert(data.encodeBase64 == cast(ubyte[])"QUJD");
    }

    // 6 bytes
    {
        ubyte[] data = cast(ubyte[])"ABCDEF";
        assert(data.encodeBase64 == cast(ubyte[])"QUJDREVG");
    }

    // 9 bytes
    {
        ubyte[] data = cast(ubyte[])"ABCDEFGHI";
        assert(data.encodeBase64 == cast(ubyte[])"QUJDREVGR0hJ");
    }

    // 12 bytes
    {
        ubyte[] data = cast(ubyte[])"ABCDEFGHIJKL";
        assert(data.encodeBase64 == cast(ubyte[])"QUJDREVGR0hJSktM");
    }
}

/// Test encoding of data which has a length which CANNOT be cleanly encoded.
/// This typically means that there's padding.
unittest
{
    // 1 byte 
    {
        ubyte[] data = cast(ubyte[])"A";
        assert(data.encodeBase64 == cast(ubyte[])"QQ==");
    }
    // 2 bytes
    {
        ubyte[] data = cast(ubyte[])"AB";
        assert(data.encodeBase64 == cast(ubyte[])"QUI=");
    }
    // 4 bytes
    {
        ubyte[] data = [0xDE, 0xAD, 0xBA, 0xBE];
        assert(data.encodeBase64 == cast(ubyte[])"3q26vg==");
    }
    // 37 bytes
    {
        ubyte[] data = cast(ubyte[])"A Very Very Very Very Large Test Blob";
        assert(data.encodeBase64 == cast(ubyte[])"QSBWZXJ5IFZlcnkgVmVyeSBWZXJ5IExhcmdlIFRlc3QgQmxvYg==");
    }
}

/// Make sure we can decode what we encode.
unittest
{
    // Test an example string
    {
        enum ubyte[] data = cast(ubyte[])"abc123!?$*&()'-=@~";
        assert(data.encodeBase64.decodeBase64 == data);
    }
    // Test an example from Ion data
    {
        enum ubyte[] data = cast(ubyte[])"a b c d e f g h i j k l m n o p q r s t u v w x y z";
        assert(data.encodeBase64.decodeBase64 == data);
    }
}