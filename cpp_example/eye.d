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

    void printMatrix(Slice!(double*, 2) matrix)
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
