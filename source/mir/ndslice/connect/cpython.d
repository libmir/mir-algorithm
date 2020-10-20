/++
Utilities for $(LINK2 https://docs.python.org/3/c-api/buffer.html, Python Buffer Protocol).

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Copyright: 2020 Ilya Yaroshenko, Kaleidic Associates Advisory Limited, Symmetry Investments
Authors: Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
STD = $(TD $(SMALL $0))
PGB = $(LINK2 https://docs.python.org/3/c-api/buffer.html#c.PyObject_GetBuffer, PyObject_GetBuffer())
+/
module mir.ndslice.connect.cpython;

import mir.ndslice.slice;
import core.stdc.config;
import std.traits;

/++
Construct flags for $(PGB).
If `T` is not `const` or `immutable` then the flags require writable buffer.
If slice kind is $(SUBREF slice, Contiguous) then the flags require $(LINK2 https://docs.python.org/3/c-api/buffer.html#contiguity-requests, c_contiguous) buffer.

Params:
    kind = slice kind
    T = record type
Returns:
    flags for $(LREF Py_buffer) request.
+/
enum int pythonBufferFlags(SliceKind kind, T) = (kind == Contiguous ? PyBuf_c_contiguous : PyBuf_strides) | (is(T == const) || is (T == immutable) ? PyBuf_records_ro : PyBuf_records);

/++
Fills the slice (structure) from the python `view`.
The view should be created by $(PGB) that was called with $(LREF pythonBufferFlags).

Params:
    slice = output ndslice
    view = $(LREF Py_buffer) requested 
Returns:
    one of the `input_buffer_*` $(LREF PythonBufferErrorCode) on failure and `success` otherwise.
+/
PythonBufferErrorCode fromPythonBuffer(T, size_t N, SliceKind kind)(ref Slice!(T*, N, kind) slice, ref const Py_buffer view) nothrow @nogc @trusted
    if (N <= PyBuf_max_ndim)
{
    import core.stdc.string: strcmp;
    import mir.internal.utility: Iota;

    static if (!(is(T == const) || is(T == immutable)))
        assert(!view.readonly);

    enum N = slice.N;
    enum S = slice.S;

    if (N != view.ndim)
        return typeof(return).input_buffer_ndim_mismatch;
    if (T.sizeof != view.itemsize)
        return typeof(return).input_buffer_itemsize_mismatch;
    if (pythonBufferFormat!(Unqual!T).ptr.strcmp(view.format))
        return typeof(return).input_buffer_format_mismatch;
    if (kind == Canonical && view.strides[N - 1] != T.sizeof)
        return typeof(return).input_buffer_strides_mismatch;

    foreach(i; Iota!N)
        slice._lengths[i] = view.shape[i];
    foreach(i; Iota!S)
    {
        assert(view.strides[i] % T.sizeof == 0);
        slice._strides[i] = view.strides[i] / T.sizeof;
    }
    slice._iterator = cast(T*) view.buf;

    return typeof(return).success;
}

///
version(mir_test) unittest
{
    import mir.ndslice.slice: Slice;
    auto bar(ref const Py_buffer view)
    {
        Slice!(const(double)*, 2) mat;
        if (auto error = mat.fromPythonBuffer(view))
        {
            // has null pointer
        }
        return mat;
    }
}

/++
Fills the python view (structure) from the slice.
Params:
    slice = input ndslice
    view = output $(LREF Py_buffer).
        $(LREF Py_buffer.internal) is initialized with null value,
        $(LREF Py_buffer.obj) is not initialized.
        Other $(LREF Py_buffer) fields are initialized according to the flags and slice.
    flags = requester flags
    structureBuffer = Single chunk of memory with the same alignment and size as $(SUBREF _slice, Structure).
        The buffer is used to store shape and strides for the view.
Returns:
    one of the `cannot_create_*` $(LREF PythonBufferErrorCode) on failure and `success` otherwise.
+/
PythonBufferErrorCode toPythonBuffer(T, size_t N, SliceKind kind)(Slice!(T*, N, kind) slice, ref Py_buffer view, int flags, ref Structure!N structureBuffer) nothrow @nogc @trusted
    if (N <= PyBuf_max_ndim)
{
    structureBuffer.lengths = slice._lengths;
    structureBuffer.strides = slice.strides;

    foreach(ref stride; structureBuffer.strides)
        stride *= T.sizeof;

    /////////////////////
    /// always filled ///
    /////////////////////
    view.buf = slice._iterator;
    // skip view.obj
    view.len = slice.elementCount * T.sizeof;
    view.itemsize = T.sizeof;
    view.ndim = N;
    view.internal = null;

    static if (kind != Contiguous)
    {
        bool check_single_memory_block;
    }

    /// shape ///
    if ((flags & PyBuf_nd) == PyBuf_nd)
    {
        view.shape = cast(sizediff_t*) structureBuffer.lengths.ptr;
        /// strides ///
        if ((flags & PyBuf_strides) == PyBuf_strides)
            view.strides = cast(sizediff_t*) structureBuffer.strides.ptr;
        else
        {
            view.strides = null;
            static if (kind != Contiguous)
                check_single_memory_block = true;
        }
    }
    else
    {
        view.shape = null;
        view.strides = null;
        static if (kind != Contiguous)
            check_single_memory_block = true;
    }
    view.suboffsets = null;

    /// ! structure verification ! ///
    static if (kind == Contiguous)
    {
        static if (N != 1)
        {
            if ((flags & PyBuf_f_contiguous) == PyBuf_f_contiguous)
            {
                import mir.ndslice.dynamic: everted;
                import mir.ndslice.topology: iota;
                if (slice.everted.shape.iota.everted.strides != slice.strides)
                    return typeof(return).cannot_create_f_contiguous_buffer;
            }
        }
    }
    else
    {
        import mir.ndslice.dynamic: everted, normalizeStructure;
        import mir.ndslice.topology: iota;
        if ((flags & PyBuf_c_contiguous) == PyBuf_c_contiguous)
        {
            if (slice.shape.iota.strides != slice.strides && slice.everted.shape.iota.everted.strides != slice.strides)
                return typeof(return).cannot_create_c_contiguous_buffer;
        }
        else
        if ((flags & PyBuf_any_contiguous) == PyBuf_any_contiguous)
        {
            if (slice.shape.iota.strides != slice.strides && slice.everted.shape.iota.everted.strides != slice.strides)
                return typeof(return).cannot_create_any_contiguous_buffer;
        }
        else
        if (check_single_memory_block)
        {
            if (!slice.normalizeStructure)
                return typeof(return).cannot_create_a_buffer_without_strides;
        }
    }

    /// readonly ///
    static if (is(T == const) || is(T == immutable))
    {
        if (flags & PyBuf_writable)
            return typeof(return).cannot_create_writable_buffer;
        view.readonly = 1;
    }
    else
        view.readonly = 0;

    /// format ///
    if (flags & PyBuf_format)
    {
        enum fmt = pythonBufferFormat!(Unqual!T);
        static if (fmt is null)
            return typeof(return).cannot_create_format_string;
        else
            view.format = cast(char*)fmt.ptr;
    }
    else
        view.format = null;

    return typeof(return).success;
}

///
version(mir_test) unittest
{
    import mir.ndslice.slice : Slice, Structure, Universal, Contiguous;
    Py_buffer bar(SliceKind kind)(Slice!(double*, 2, kind) slice)
    {
        import core.stdc.stdlib;
        enum N = 2;

        auto structurePtr = cast(Structure!N*) Structure!N.sizeof.malloc;
        if (!structurePtr)
            assert(0);
        Py_buffer view;

        if (auto error = slice.toPythonBuffer(view, PyBuf_records_ro, *structurePtr))
        {
            view = view.init; // null buffer
            structurePtr.free;
        }
        else
        {
            assert(cast(sizediff_t*)&structurePtr.lengths == view.shape);
            assert(cast(sizediff_t*)&structurePtr.strides == view.strides);
        }

        return view;
    }

    alias barUni = bar!Universal;
    alias barCon = bar!Contiguous;
}

/// Python $(LINK2 https://docs.python.org/3/c-api/buffer.html#buffer-structure, Buffer structure).
extern(C)
struct bufferinfo
{
    ///
    void *buf;
    ///
    void *obj;
    ///
    sizediff_t len;
    ///
    sizediff_t itemsize;
    ///
    int readonly;
    ///
    int ndim;
    ///
    char *format;
    ///
    sizediff_t *shape;
    ///
    sizediff_t *strides;
    ///
    sizediff_t *suboffsets;
    ///
    void *internal;
}
/// ditto
alias Py_buffer = bufferinfo;

/++
Error codes for ndslice - Py_buffer conversion.
+/
enum PythonBufferErrorCode
{
    ///
    success,
    ///
    cannot_create_format_string,
    ///
    cannot_create_writable_buffer,
    ///
    cannot_create_f_contiguous_buffer,
    ///
    cannot_create_c_contiguous_buffer,
    ///
    cannot_create_any_contiguous_buffer,
    ///
    cannot_create_a_buffer_without_strides,
    ///
    input_buffer_ndim_mismatch,
    ///
    input_buffer_itemsize_mismatch,
    ///
    input_buffer_format_mismatch,
    ///
    input_buffer_strides_mismatch,
}

///
enum PyBuf_max_ndim = 64;

///
enum PyBuf_simple = 0;
///
enum PyBuf_writable = 0x0001;
///
enum PyBuf_writeable = PyBuf_writable;
///
enum PyBuf_format = 0x0004;
///
enum PyBuf_nd = 0x0008;
///
enum PyBuf_strides = (0x0010 | PyBuf_nd);
///
enum PyBuf_c_contiguous = (0x0020 | PyBuf_strides);
///
enum PyBuf_f_contiguous = (0x0040 | PyBuf_strides);
///
enum PyBuf_any_contiguous = (0x0080 | PyBuf_strides);
///
enum PyBuf_indirect = (0x0100 | PyBuf_strides);

///
enum PyBuf_contig = (PyBuf_nd | PyBuf_writable);
///
enum PyBuf_contig_ro = (PyBuf_nd);

///
enum PyBuf_strided = (PyBuf_strides | PyBuf_writable);
///
enum PyBuf_strided_ro = (PyBuf_strides);

///
enum PyBuf_records = (PyBuf_strides | PyBuf_writable | PyBuf_format);
///
enum PyBuf_records_ro = (PyBuf_strides | PyBuf_format);

/++
Returns $(HTTPS docs.python.org/3/c-api/buffer.html#c.Py_buffer.format, python format (type)) string.
For example, `"O"` for `PyObject` and "B" for ubyte.
+/
template pythonBufferFormat(T)
{
    static if (is(T == struct) && __traits(identifier, A) == "PyObject")
        enum pythonBufferFormat = "O";
    else
    static if (is(Unqual!T == short))
        enum pythonBufferFormat = "h";
    else
    static if (is(Unqual!T == ushort))
        enum pythonBufferFormat = "H";
    else
    static if (is(Unqual!T == int))
        enum pythonBufferFormat = "i";
    else
    static if (is(Unqual!T == uint))
        enum pythonBufferFormat = "I";
    else
    static if (is(Unqual!T == float))
        enum pythonBufferFormat = "f";
    else
    static if (is(Unqual!T == double))
        enum pythonBufferFormat = "d";
    else
    static if (is(Unqual!T == long))
        enum pythonBufferFormat = "q";
    else
    static if (is(Unqual!T == ulong))
        enum pythonBufferFormat = "Q";
    else
    static if (is(Unqual!T == ubyte))
        enum pythonBufferFormat = "B";
    else
    static if (is(Unqual!T == byte))
        enum pythonBufferFormat = "b";
    else
    static if (is(Unqual!T == char))
        enum pythonBufferFormat = "c";
    else
    static if (is(Unqual!T == char*))
        enum pythonBufferFormat = "z";
    else
    static if (is(Unqual!T == void*))
        enum pythonBufferFormat = "P";
    else
    static if (is(Unqual!T == bool))
        enum pythonBufferFormat = "?";
    else
    static if (is(Unqual!T == wchar*))
        enum pythonBufferFormat = "Z";
    else
    static if (is(Unqual!T == wchar))
        enum pythonBufferFormat = "u";
    else
    {
        static if (is(cpp_long))
        {
            static if (is(Unqual!T == cpp_long))
                enum pythonBufferFormat = "l";
            else
                enum pythonBufferFormat = null;
        }
        else
        static if (is(cpp_ulong))
        {
            static if (is(Unqual!T == cpp_ulong))
                enum pythonBufferFormat = "L";
            else
                enum pythonBufferFormat = null;
        }
        else
        static if (is(c_long_double))
        {
            static if (is(Unqual!T == c_long_double))
                enum pythonBufferFormat = "g";
            else
                enum pythonBufferFormat = null;
        }
        else
            enum pythonBufferFormat = null;
    }
}
