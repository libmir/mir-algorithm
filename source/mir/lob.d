/++
+/
module mir.lob;

import mir.serde: serdeRegister;

/++
Values of type clob are encoded as a sequence of octets that should be interpreted as text
with an unknown encoding (and thus opaque to the application).
+/
@serdeRegister
struct Clob
{
    ///
    const(char)[] data;
}

/++
This is a sequence of octets with no interpretation (and thus opaque to the application).
+/
@serdeRegister
struct Blob
{
    ///
    const(ubyte)[] data;
}
