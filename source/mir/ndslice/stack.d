
module mir.ndslice.stack;

import std.traits;

import mir.ndslice.internal;

@fastmath:

struct Stack(Slices...)
    if (Slices.lengths > 1)
{
    private Slices slices;

    private bool empty(size_t dimension)() @property
        if (dimension)
    {

    }

    ///
    void each(alias fun, size_t dimension = 0)()
    {
        static if (dimension)
            foreach(i, ref slice; slices)
                for (auto t = slice; !t.empty!dimension; t.popFront!dimension)
                    t.front!dimension.each!fun;
        else
            foreach (i, ref slice; slices)
                slice.each!fun;
    }
}

struct Transposition(Slice, size_t dimension)
    if (dimension)
{
    private Slice slice;

    ///
    void each(alias fun)()
    {
        static if (is(Slice : Stack!(Slices), Slices...))
            alias slices = slice.slices;
        else
            alias slices = AliasSeq!slice;
        foreach(i, ref slice; slices)
            for (auto t = slice; !slice.empty!dimension; slice.popFront!dimension )
            {}
    }
}
