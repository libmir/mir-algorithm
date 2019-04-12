module init_rcarray;

import mir.ndslice;
import mir.rcarray;
import mir.shared_ptr;

// force template instatiations
alias RCArrayDouble = RCArray!double;
alias RCArrayInt = RCArray!int;

extern(C++)
struct S { double d = 0; this(double e) { d = e;}  }
extern(C++)
struct C { double k = 0; S s;  }
alias SPtr = SharedPtr!S;
alias CPtr = SharedPtr!C;

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
