/++
Copyright: See Phobos Copyright
License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: $(HTTP erdani.com, Andrei Alexandrescu), Ilya Yaroshenko
+/
module mir.internal.memory;

enum uint platformAlignment = double.alignof > real.alignof ? double.alignof : real.alignof;

@nogc nothrow pragma(inline, true):

@safe pure
package bool isGoodDynamicAlignment()(uint x)
{
    return (x & -x) > (x - 1) && x >= (void*).sizeof;
}

version (Posix)
private extern(C) int posix_memalign(void**, size_t, size_t);

version (Windows)
{
    // DMD Win 32 bit, DigitalMars C standard library misses the _aligned_xxx
    // functions family (snn.lib)
    version(CRuntime_DigitalMars)
    {
        // Helper to cast the infos written before the aligned pointer
        // this header keeps track of the size (required to realloc) and of
        // the base ptr (required to free).
        private struct AlignInfo()
        {
            void* basePtr;
            size_t size;

            @nogc nothrow pragma(inline, true)
            static AlignInfo* opCall()(void* ptr)
            {
                return cast(AlignInfo*) (ptr - AlignInfo.sizeof);
            }
        }

       
        private void* _aligned_malloc()(size_t size, size_t alignment)
        {
            import core.stdc.stdlib : malloc;
            size_t offset = alignment + size_t.sizeof * 2 - 1;

            // unaligned chunk
            void* basePtr = malloc(size + offset);
            if (!basePtr) return null;

            // get aligned location within the chunk
            void* alignedPtr = cast(void**)((cast(size_t)(basePtr) + offset)
                & ~(alignment - 1));

            // write the header before the aligned pointer
            AlignInfo* head = AlignInfo!()(alignedPtr);
            head.basePtr = basePtr;
            head.size = size;

            return alignedPtr;
        }

       
        private void* _aligned_realloc()(void* ptr, size_t size, size_t alignment)
        {
            import core.stdc.stdlib : free;
            import core.stdc.string : memcpy;

            if (!ptr) return _aligned_malloc(size, alignment);

            // gets the header from the exising pointer
            AlignInfo* head = AlignInfo(ptr);

            // gets a new aligned pointer
            void* alignedPtr = _aligned_malloc(size, alignment);
            if (!alignedPtr)
            {
                //to https://msdn.microsoft.com/en-us/library/ms235462.aspx
                //see Return value: in this case the original block is unchanged
                return null;
            }

            // copy exising data
            memcpy(alignedPtr, ptr, head.size);
            free(head.basePtr);

            return alignedPtr;
        }

       
        private void _aligned_free()(void *ptr)
        {
            import core.stdc.stdlib : free;
            if (!ptr) return;
            AlignInfo* head = AlignInfo(ptr);
            free(head.basePtr);
        }

    }
    // DMD Win 64 bit, uses microsoft standard C library which implements them
    else
    {
        private extern(C) void* _aligned_realloc(void *, size_t, size_t);
    }
}

/**
Uses $(HTTP man7.org/linux/man-pages/man3/posix_memalign.3.html,
$(D posix_memalign)) on Posix and
$(HTTP msdn.microsoft.com/en-us/library/8z34s9c6(v=vs.80).aspx,
$(D __aligned_malloc)) on Windows.
*/
version(Posix)
@trusted
void* alignedAllocate()(size_t bytes, uint a)
{
    import core.stdc.errno : ENOMEM, EINVAL;
    assert(a.isGoodDynamicAlignment);
    void* result;
    auto code = posix_memalign(&result, a, bytes);
    if (code == ENOMEM)
        return null;

    else if (code == EINVAL)
    {
        assert(0, "AlignedMallocator.alignment is not a power of two "
            ~"multiple of (void*).sizeof, according to posix_memalign!");
    }
    else if (code != 0)
        assert (0, "posix_memalign returned an unknown code!");

    else
        return result;
}
else version(Windows)
@trusted
void* alignedAllocate()(size_t bytes, uint a)
{
    return _aligned_malloc(bytes, a);
}
else static assert(0);

/**
Calls $(D free(b.ptr)) on Posix and
$(HTTP msdn.microsoft.com/en-US/library/17b5h8td(v=vs.80).aspx,
$(D __aligned_free(b.ptr))) on Windows.
*/
version (Posix)
{
    public import core.stdc.stdlib : alignedFree = free;
}
else
version (Windows)
@system
void alignedFree()(void* b)
{
    _aligned_free(b);
}
else static assert(0);

/**
On Posix, uses $(D alignedAllocate) and copies data around because there is
no realloc for aligned memory. On Windows, calls
$(HTTP msdn.microsoft.com/en-US/library/y69db7sx(v=vs.80).aspx,
$(D __aligned_realloc(b.ptr, newSize, a))).
*/
version (Windows)
@system
void alignedReallocate()(ref void* b, size_t s, uint a)
{
    if (!s)
    {
        alignedFree(b);
        b = null;
        return;
    }
    auto p = cast(ubyte*) _aligned_realloc(b, s, a);
    if (!p) return;
    b = p;
}

///
unittest
{
    auto buffer = alignedAllocate(1024 * 1024 * 4, 128);
    alignedFree(buffer);
    //...
}

version(CRuntime_DigitalMars)
unittest
{
    static size_t addr()(ref void* ptr) { return cast(size_t) ptr; }

    void* m;

    m = _aligned_malloc(16, 0x10);
    if (m)
    {
        assert((m.addr & 0xF) == 0);
        _aligned_free(m);
    }

    m = _aligned_malloc(16, 0x100);
    if (m)
    {
        assert((m.addr & 0xFF) == 0);
        _aligned_free(m);
    }

    m = _aligned_malloc(16, 0x1000);
    if (m)
    {
        assert((m.addr & 0xFFF) == 0);
        _aligned_free(m);
    }

    m = _aligned_malloc(16, 0x10);
    if (m)
    {
        assert((cast(size_t)m & 0xF) == 0);
        m = _aligned_realloc(m, 32, 0x10000);
        if (m) assert((m.addr & 0xFFFF) == 0);
        _aligned_free(m);
    }

    m = _aligned_malloc(8, 0x10);
    if (m)
    {
        *cast(ulong*) m = 0X01234567_89ABCDEF;
        m = _aligned_realloc(m, 0x800, 0x1000);
        if (m) assert(*cast(ulong*) m == 0X01234567_89ABCDEF);
        _aligned_free(m);
    }
}
