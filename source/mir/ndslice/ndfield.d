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

import mir.qualifier;
import mir.internal.utility;
import mir.ndslice.internal;
import mir.ndslice.slice;
import mir.primitives;
import std.meta;

private template _indices(NdFields...)
{
    static if (NdFields.length == 0)
        enum _indices = "";
    else
    {
        alias Next = NdFields[0 .. $ - 1];
        enum i = Next.length;
        enum _indices = ._indices!Next ~
    "_fields[" ~ i.stringof ~ "][" ~ _indices_range!([staticMap!(DimensionCount, Next)].sum, DimensionCount!(NdFields[$ - 1])) ~ "], ";
    }
}

private template _indices_range(size_t begin, size_t count)
{
    static if (count == 0)
        enum _indices_range = "";
    else
    {
        enum next = count - 1;
        enum elem = begin + next;
        enum _indices_range = ._indices_range!(begin, next) ~ "indices[" ~ elem.stringof ~ "], ";
    }
}

///
struct Cartesian(NdFields...)
    if (NdFields.length > 1)
{
    ///
    NdFields _fields;

    package(mir) enum size_t M(size_t f) = [staticMap!(DimensionCount, NdFields[0..f])].sum;
    package(mir) enum size_t N = M!(NdFields.length);

    ///
    auto lightConst()() const @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        return mixin("Cartesian!(staticMap!(LightConstOf, NdFields))(%(_fields[%s].lightConst,%)].lightConst)".format(_fields.length.iota));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        return mixin("Cartesian!(staticMap!(LightImmutableOf, NdFields))(%(_fields[%s].lightImmutable,%)].lightImmutable)".format(_fields.length.iota));
    }

    ///
    size_t length(size_t d = 0)() @safe scope const @property
    {
        foreach(f, NdField; NdFields)
            static if (M!f <= d && M!(f + 1) > d)
            {
                enum d = d - M!f;
                static if (d)
                    return _fields[f].length!(d - M!f);
                else
                    return _fields[f].length;
            }
    }

    ///
    size_t[N] shape()() @safe scope const @property
    {
        typeof(return) ret;
        foreach(f, NdField; NdFields)
        {
            static if (hasShape!NdField)
            {
                auto s = _fields[f].shape;
                foreach(j; Iota!(s.length))
                    ret[M!f + j] = s[j];
            }
            else
            {
                ret[M!f] = _fields[f].length;
            }
        }
        return ret;
    }

    ///
    size_t elementCount()() @safe scope const @property
    {
        size_t ret = 1;
        foreach (f, NdField; NdFields)
            ret *= _fields[f].elementCount;
        return ret;
    }

    ///
    auto opIndex(size_t[N] indices...)
    {
        import mir.functional : refTuple;
        return mixin("refTuple(" ~ _indices!(NdFields) ~ ")");
    }
}

private template _kr_indices(size_t n)
{
    static if (n == 0)
        enum _kr_indices = "";
    else
    {
        enum i = n - 1;
        enum _kr_indices = ._kr_indices!i ~ "_fields[" ~ i.stringof ~ "][ind[" ~ i.stringof ~ "]], ";
    }
}

///
struct Kronecker(alias fun, NdFields...)
    if (NdFields.length > 1 && allSatisfy!(templateOr!(hasShape, hasLength), NdFields[1 .. $]))
{
    ///
    NdFields _fields;

    ///
    auto lightConst()() const @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        return mixin("Kronecker!(fun, staticMap!(LightConstOf, NdFields))(%(_fields[%s].lightConst,%)].lightConst)".format(_fields.length.iota));
    }

    ///
    auto lightImmutable()() immutable @property
    {
        import std.format;
        import mir.ndslice.topology: iota;
        return mixin("Kronecker!(fun, staticMap!(LightImmutableOf, NdFields))(%(_fields[%s].lightImmutable,%)].lightImmutable)".format(_fields.length.iota));
    }

    private enum N = DimensionCount!(NdFields[$-1]);

    ///
    size_t length(size_t d = 0)() scope const @property
    {
        static if (d == 0)
        {
            size_t ret = 1;
            foreach (f, NdField; NdFields)
                ret *= _fields[f].length;
        }
        else
        {
            size_t ret = 1;
            foreach (f, NdField; NdFields)
                ret *= _fields[f].length!d;
        }
        return ret;
    }

    
    ///
    size_t[N] shape()() scope const @property
    {
        static if (N > 1)
        {
            size_t[N] ret = 1;
            foreach (f, NdField; NdFields)
            {
                auto s = _fields[f].shape;
                foreach(i; Iota!N)
                    ret[i] *= s[i];
            }
            return ret;
        }
        else
        {
            size_t[1] ret = 1;
            foreach (f, NdField; NdFields)
                ret[0] *= _fields[f].length;
            return ret;
        }
    }

    ///
    size_t elementCount()() scope const @property
    {
        size_t ret = 1;
        foreach (f, NdField; NdFields)
            ret *= _fields[f].elementCount;
        ret;
    }

    ///
    auto ref opIndex()(size_t[N] indices...)
    {   
        static if (N > 1)
            size_t[N][NdFields.length] ind;
        else
            size_t[NdFields.length] ind;
        foreach_reverse (f, NdField; NdFields)
        {
            static if (f)
            {
                static if (hasShape!(NdFields[f]))
                {
                    auto s = _fields[f].shape;
                }
                else
                {
                    size_t[1] s;
                    s[0] = _fields[f].length;
                }
                static if (N > 1)
                {
                    foreach(i; Iota!N)
                    {
                        ind[f][i] = indices[i] % s[i];
                        indices[i] /= s[i];
                    }
                }
                else
                {
                    ind[f] = indices[0] % s[0];
                    indices[0] /= s[0];
                }
            }
            else
            {
                static if (N > 1)
                {
                    foreach(i; Iota!N)
                        ind[f][i] = indices[i];
                }
                else
                {
                    ind[f] = indices[0];
                }
            }
        }
        return mixin("fun(" ~ _kr_indices!(ind.length) ~ ")");
    }
}
