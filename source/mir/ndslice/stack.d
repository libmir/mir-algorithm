
module mir.ndslice.stack;

import std.traits;

import mir.ndslice.internal;

@fastmath:

struct Stack(Tensors...)
    if (Tensors.lengths > 1)
{
    private Tensors tensor;

    private bool empty(size_t dimension)() @property
        if (dimension)
    {

    }

    ///
    void each(alias fun, size_t dim = 0)()
    {
        static if (dim == 0)
            foreach (i, ref tensor; tensors)
                tensor.each!fun;
        else
            foreach(i, ref tensor; tensors)
                for (auto t = tensor; !t.empty!dimension; t.popFront!dimension)
                    t.front!dimension.each!fun;
    }
}

struct Transposition(Tensor, size_t dimension)
    if (dimension)
{
    private Tensor tensor;

    ///
    void each(alias fun)()
    {
        static if (is(Tensor : Stack!(Tensors), Tensors...))
            alias tensors = tensor.tensors;
        else
            alias tensors = AliasSeq!tensor;
        foreach(i, ref tensor; tensors)
            for (auto t = tensor; !tensor.empty!dimension; tensor.popFront!dimension )
            {}
    }
}