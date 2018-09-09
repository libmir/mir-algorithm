///
module mir.internal.utility;

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
    if (__traits(isFloating, C) || isComplex!C)
{
    import std.traits: Unqual;
    static if (isComplex!C)
        alias realType = typeof(Unqual!C.init.re);
    else
        alias realType = Unqual!C;
}

///
enum isComplex(C : creal) = true;
/// ditto
enum isComplex(C : cdouble) = true;
/// ditto
enum isComplex(C : cfloat) = true;
/// ditto
enum isComplex(C) = false;

///
enum isFloatingPoint(C : real) = true;
/// ditto
enum isFloatingPoint(C : double) = true;
/// ditto
enum isFloatingPoint(C : float) = true;
/// ditto
enum isFloatingPoint(C) = false;
