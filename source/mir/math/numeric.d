/++
This module contains simple numeric algorithms.

License: $(LINK2 http://boost.org/LICENSE_1_0.txt, Boost License 1.0).

Authors: Ilya Yaroshenko

Copyright: 2015-, Ilya Yaroshenko; 2017 Symmetry Investments Group and Kaleidic Associates Advisory Limited.

Sponsors: This work has been sponsored by $(SUBREF http://symmetryinvestments.com, Symmetry Investments) and Kaleidic Associates.
+/
module mir.math.numeric;

import mir.math.common;
import mir.primitives;

import std.traits;

///
struct Prod(T)
	if (isFloatingPoint!T)
{
	///
	long exp = 1;
	///
	T x = 0.5f;

	///
	void put()(T e)
	{
        int lexp;
        import std.math: frexp;
        x *= frexp(e, lexp);
        exp += lexp;
        if (x.fabs < 0.5f)
        {
            x += x;
            exp--;
        }
	}

    ///
    T value()() @property
    {
        if (exp > int.max)
            exp = int.max;
        else
        if (exp < int.min)
            exp = int.min;
        import std.math: ldexp;
        return ldexp(x, cast(int)exp);
    }
}

/++
Compute the product of the input range $(D r) using separate exponent accumulation.
+/
Unqual!(DeepElementType!Range) prod(Range)(Range r, ref long exp)
	if (isFloatingPoint!(DeepElementType!Range))
{
    import mir.algorithm.iteration: each;
    Prod!(typeof(return)) prod;
    r.each!(e => prod.put(e));
    exp = prod.exp;
    return prod.x;
}

/// ditto
Unqual!(DeepElementType!Range) prod(Range)(Range r)
	if (isFloatingPoint!(DeepElementType!Range))
{

    long exp;
    auto x = .prod(r, exp);
    return Prod!(typeof(return))(exp, x).value;
}

/// Arrays and Ranges
version(mir_test)
unittest
{
	enum l = 2.0 ^^ (double.max_exp - 1);
	enum s = 2.0 ^^ -(double.max_exp - 1);
	auto r = [l, l, l, s, s, s, 0.8 * 2.0 ^^ 10];
	long e;
	assert(r.prod(e) == 0.8);
	assert(e == 10);
	assert(r.prod == 0.8 * 2.0 ^^ 10);
}

/// Ndslices
version(mir_test)
unittest
{
    import mir.math.numeric: prod;
    import mir.ndslice.slice: sliced;
    import mir.algorithm.iteration: reduce;

	enum l = 2.0 ^^ (double.max_exp - 1);
	enum s = 2.0 ^^ -(double.max_exp - 1);
    auto c = 0.8;
    auto u = c * 2.0 ^^ 10;
	auto r = [l, l, l,
              s, s, s,
              u, u, u].sliced(3, 3);
	long e;
	assert(r.prod(e) == reduce!"a * b"(1.0, [c, c, c]));
	assert(e == 30);
	assert(r.prod == reduce!"a * b"(1.0, [u, u, u]));
}

/++
Compute the sum of binary logarithms of the input range $(D r).
The error of this method is much smaller than with a naive sum of log2.
+/
Unqual!(DeepElementType!Range) sumOfLog2s(Range)(Range r)
	if (isFloatingPoint!(DeepElementType!Range))
{
    long exp = 0;
    auto x = .prod(r, exp);
    return exp + log2(x);
}

///
version(mir_test)
@safe unittest
{
    import std.math : isNaN;

    assert(sumOfLog2s(new double[0]) == 0);
    assert(sumOfLog2s([0.0L]) == -real.infinity);
    assert(sumOfLog2s([-0.0L]) == -real.infinity);
    assert(sumOfLog2s([2.0L]) == 1);
    assert(sumOfLog2s([-2.0L]).isNaN());
    assert(sumOfLog2s([real.nan]).isNaN());
    assert(sumOfLog2s([-real.nan]).isNaN());
    assert(sumOfLog2s([real.infinity]) == real.infinity);
    assert(sumOfLog2s([-real.infinity]).isNaN());
    assert(sumOfLog2s([ 0.25, 0.25, 0.25, 0.125 ]) == -9);
}
