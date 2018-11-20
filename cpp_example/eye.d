module eye;

import mir.ndslice;

extern(C++, Space)
{
    Slice!(double*, 2) eye(size_t n) nothrow @nogc
    {
        auto ret = stdcUninitSlice!double(n, n);
        ret[] = 0;
        ret.diagonal[] = 1;
        return ret;
    }

    void printMatrix(mir_slice!(double*, 2) matrix)
    {
        import core.stdc.stdio;

        foreach(row; matrix)
        {
            foreach(e; row)
                printf("%f ", e);
            printf("\n");
        }
    }
}


// Space::printMatrix(mir_slice<double*, 2ul, (mir_slice_kind)2>)
// Space::printMatrix(mir_slice<double*, 2ull, (mir_slice_kind)2>)
// Space::reverseRcSlice(mir_slice<mir_rci<double>, 1ull, (mir_slice_kind)2>&)

//Space::printMatrix(mir_slice<double*, 2ul, (mir_slice_kind)2>)


pragma(msg, printMatrix.mangleof);