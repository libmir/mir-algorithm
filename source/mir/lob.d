/++
+/
module mir.lob;

/++
Values of type clob are encoded as a sequence of octets that should be interpreted as text
with an unknown encoding (and thus opaque to the application).
+/
struct Clob
{
    ///
    const(char)[] data;
}

/++
This is a sequence of octets with no interpretation (and thus opaque to the application).
+/
struct Blob
{
    ///
    const(ubyte)[] data;
}
