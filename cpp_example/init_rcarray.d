module init_rcarray;

import mir.ndslice;
import mir.rcarray;

extern(C++, Space) 
{
    void initWithIota(ref RCArray!double a)
    {
        foreach(i, ref e; a)
            e = i;
    }

    void reverseRcSlice(ref Slice!(RCI!double) a)
    {
        import mir.utility: swap;
        foreach(i; 0 .. a.length / 2)
            swap(a[i], a[$ - 1 - i]);
    }

    void reverseRcSlice(ref Slice!(RCI!int) a)
    {
        import mir.utility: swap;
        foreach(i; 0 .. a.length / 2)
            swap(a[i], a[$ - 1 - i]);
    }
}
