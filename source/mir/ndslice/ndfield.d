/++
This is a submodule of $(MREF mir,ndslice).

NdField is a type with `opIndex(size_t[N] index...)` primitive.
An ndslice can be created on top of a ndField using $(SUBREF slice, slicedNdField).

$(BOOKTABLE $(H2 NdFields),
$(TR $(TH NdField Name) $(TH Used By))
$(T2 Cartesian, $(SUBREF topology, cartesian))
$(T2 Kronecker, $(SUBREF topology, kronecker))
)

See_also: $(SUBREF concatenation, concatenation).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.ndslice.ndfield;

import mir.internal.utility;
import mir.ndslice.internal;
import mir.ndslice.slice;
import mir.primitives;
import std.meta;

private template _indexes(NdFields...)
{
    static if (NdFields.length == 0)
        enum _indexes = "";
    else
    {
        alias Next = NdFields[0 .. $ - 1];
        enum i = Next.length;
        enum _indexes = ._indexes!Next ~
    "_fields[" ~ i.stringof ~ "][" ~ _indexes_range!([staticMap!(DimensionCount, Next)].sum, DimensionCount!(NdFields[$ - 1])) ~ "], ";
    }
}

private template _indexes_range(size_t begin, size_t count)
{
    static if (count == 0)
        enum _indexes_range = "";
    else
    {
        enum next = count - 1;
        enum elem = begin + next;
        enum _indexes_range = ._indexes_range!(begin, next) ~ "indexes[" ~ elem.stringof ~ "], ";
    }
}

///
struct Cartesian(NdFields...)
 if (NdFields.length > 1)
{
    ///
    NdFields _fields;

    package enum size_t M(size_t f) = [staticMap!(DimensionCount, NdFields[0..f])].sum;
    package enum size_t N = M!(NdFields.length);

    ///
    size_t length(size_t d = 0)() @property
    {
        foreach(f, ref field; _fields)
            static if (M!(f + 1) > d)
                return field.length!(d - M!f);
    }

    ///
    size_t[N] shape()() @property
    {
        typeof(return) ret = void;
        foreach(f, ref field; _fields)
        {
            static if (hasShape!(NdFields[f]))
            {
                auto s = field.shape;
                foreach(j; Iota!(s.length))
                    ret[M!f + j] = s[j];
            }
            else
            {
                ret[M!f] = field.length;
            }
        }
        return ret;
    }

    ///
    size_t elementsCount()() @property
    {
        size_t ret = 1;
        foreach (ref field; _fields)
            ret *= field.elementsCount;
        ret;
    }

    ///
    auto opIndex()(size_t[N] indexes...)
    {
        import mir.functional : tuple;
        return mixin("tuple(" ~ _indexes!(NdFields) ~ ")");
    }
}

private template _kr_indexes(size_t n)
{
    static if (n == 0)
        enum _kr_indexes = "";
    else
    {
        enum i = n - 1;
        enum _kr_indexes = ._kr_indexes!i ~ "_fields[" ~ i.stringof ~ "][ind[" ~ i.stringof ~ "]], ";
    }
}

///
struct Kronecker(alias fun, NdFields...)
    if (NdFields.length > 1 && allSatisfy!(templateOr!(hasShape, hasLength), NdFields[1 .. $]))
{
    ///
    NdFields _fields;

    private enum N = DimensionCount!(NdFields[$-1]);

    ///
    size_t length(size_t d = 0)() @property
    {
        static if (d == 0)
        {
            size_t ret = _fields[0].length;
            foreach(ref field; _fields[1 .. $])
                ret *= field.length;
        }
        else
        {
            size_t ret = _fields[0].length!d;
            foreach(ref field; _fields[1 .. $])
                ret *= field.length!d;
        }
        return ret;
    }

    
    ///
    size_t[N] shape()() @property
    {
        static if (N > 1)
        {
            size_t[N] ret = _fields[0].shape;
            foreach(ref field; _fields[1 .. $])
            {
                auto s = field.shape;
                foreach(i; Iota!N)
                    ret[i] *= s[i];
            }
            return ret;
        }
        else
        {
            size_t[1] ret = void;
            ret[0] = _fields[0].length;
            foreach(ref field; _fields[1 .. $])
                ret[0] *= field.length;
            return ret;
        }
    }

    ///
    size_t elementsCount()() @property
    {
        size_t ret = 1;
        foreach (ref field; _fields)
            ret *= field.elementsCount;
        ret;
    }

    ///
    auto ref opIndex()(size_t[N] indexes...)
    {   
        static if (N > 1)
            size_t[N][NdFields.length] ind = void;
        else
            size_t[NdFields.length] ind = void;
        foreach_reverse (f, ref field; _fields)
        {
            static if (f)
            {
                static if (hasShape!(NdFields[f]))
                {
                    auto s = field.shape;
                }
                else
                {
                    size_t[1] s = void;
                    s[0] = field.length;
                }
                static if (N > 1)
                {
                    foreach(i; Iota!N)
                    {
                        ind[f][i] = indexes[i] % s[i];
                        indexes[i] /= s[i];
                    }
                }
                else
                {
                    ind[f] = indexes[0] % s[0];
                    indexes[0] /= s[0];
                }
            }
            else
            {
                static if (N > 1)
                {
                    foreach(i; Iota!N)
                        ind[f][i] = indexes[i];
                }
                else
                {
                    ind[f] = indexes[0];
                }
            }
        }
        return mixin("fun(" ~ _kr_indexes!(ind.length) ~ ")");
    }
}
