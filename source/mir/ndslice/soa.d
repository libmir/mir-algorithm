/++
This is a submodule of $(MREF mir, ndslice).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2019-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko

$(BOOKTABLE $(H2 Definitions),
)

Macros:
SUBREF = $(REF_ALTTEXT $(TT $2), $2, mir, ndslice, $1)$(NBSP)
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
STD = $(TD $(SMALL $0))
+/
module mir.ndslice.soa;

import mir.ndslice;
import mir.internal.utility : Iota;
import mir.math.common : optmath;
import mir.ndslice.concatenation;
import mir.ndslice.field;
import mir.ndslice.internal;
import mir.ndslice.iterator;
import mir.ndslice.traits: isIterator;
import mir.primitives;
import mir.qualifier;
import mir.utility;
import std.meta;
import std.traits;
import mir.rc.array;

///
struct mir_soa_record(Iterator)
    if (isIterator!Iterator)
{
    ///
    private Iterator _iterator;

    // @property _value_
    static if (isByRefIterator!Iterator)
    {
        ref inout(typeof(Iterator.init[0])) _value() @property inout scope return
        {
            return *_iterator;
        }
    }
    else
    {
        auto ref _value() @property return
        {
            return *_iterator;
        }

        static if (isMutableIterator!Iterator)
        {
            auto ref _value(V)(auto ref V value) @property return
            {
                return *_iterator = value;
            }
        }
    }

    alias _value this;
}

/// ditto
alias SoaRecord = mir_soa_record;

///
struct mir_soa_iterator(Iterators...)
    if (allSatrisfy!(isIterator, Iterators) && Iterators.length)
{
    staticMap!(mir_soa_record, Iterators) expand;
    alias expand this;
}

///
struct mir_soa_named_iterator(string[] names, Iterators...)
    if (allSatrisfy!(isIterator, Iterators) && Iterators.length && names.length == Iterators.length)
{
    staticMap!(mir_soa_record, Iterators) expand;
    alias expand this;

    ///
    static foreach(i, Iterator; Iterators)
    {
        static if (isByRefIterator!Iterator)
        {
            mixin (`ref ` ~ name ~ `() @property scope return { return *_iterator; }`);
        }
        else
        {
            mixin (`auto ref ` ~ name ~ `() @property scope return { return *_iterator; }`);

            static if (isMutableIterator!Iterator)
            {
                mixin (`auto ref ` ~ name ~ `(V)(auto ref V value) @property scope return { return *_iterator = value; }`);
            }
        }
    }
}

/// ditto
alias SoaIterator = mir_soa_iterator;



struct S
{
    int* param;
}

struct A
{
    int[] ar;

    ref int foo() @safe @property return
    {
        return ar[0];
    }
}

void rr(int a, int b)
{

}

auto foo(A sl) @safe
{
    auto sl2 = A(new int[](10));
    // rr(sl2);
    return sl2.foo;
}
