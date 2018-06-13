///
module mir.internal.utility;

import std.traits: Unqual, isFloatingPoint;
private alias AliasSeq(T...) = T;

///
alias Iota(size_t j) = Iota!(0, j);

///
template Iota(size_t i, size_t j)
{
    static assert(i <= j, "Iota: i should be less than or equal to j");
    static if (i == j)
        alias Iota = AliasSeq!();
    else
        alias Iota = AliasSeq!(i, Iota!(i + 1, j));
}

///
template realType(C)
    if (isFloatingPoint!C || isComplex!C)
{
    static if (isComplex!C)
        alias realType = typeof(Unqual!C.init.re);
    else
        alias realType = Unqual!C;
}

///
template isComplex(C)
{
    enum bool isComplex
     = is(Unqual!C == creal)
    || is(Unqual!C == cdouble)
    || is(Unqual!C == cfloat);
}
