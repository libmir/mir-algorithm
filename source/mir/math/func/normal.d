/**
License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
*/
/**
 * Error Functions and Normal Distribution.
 *
 * Copyright: Based on the CEPHES math library, which is
 *            Copyright (C) 1994 Stephen L. Moshier (moshier@world.std.com).
 * Authors:   Stephen L. Moshier, ported to D by Don Clugston and David Nadlinger. Adopted to Mir by Ilya Yaroshenko.
 */
/**
 * Macros:
 *  NAN = $(RED NAN)
 *  INTEGRAL = &#8747;
 *  POWER = $1<sup>$2</sup>
 *      <caption>Special Values</caption>
 *      $0</table>
 */

module mir.math.func.normal;

import std.traits: isFloatingPoint;
import mir.math.common;

@safe pure nothrow @nogc:

///
deprecated("normalProbabilityDensity renamed, use normalPDF instead")
T normalProbabilityDensity(T)(const T z)
 if (isFloatingPoint!T)
{
    import mir.math.common: sqrt, exp;
    return T(SQRT2PIINV) * exp(z * z * -0.5);
}

/// ditto
deprecated("normalProbabilityDensity renamed, use normalPDF instead")
T normalProbabilityDensity(T)(const T x, const T mean, const T stdDev)
if (isFloatingPoint!T)
{
    return normalProbabilityDensity((x - mean) / stdDev) / stdDev;
}

///
T normalPDF(T)(const T z)
 if (isFloatingPoint!T)
{
    import mir.math.common: sqrt, exp;
    return T(SQRT2PIINV) * exp(z * z * -0.5);
}

/// ditto
T normalPDF(T)(const T x, const T mean, const T stdDev)
if (isFloatingPoint!T)
{
    return normalPDF((x - mean) / stdDev) / stdDev;
}

/++
Computes the normal distribution function.
The normal (or Gaussian, or bell-shaped) distribution is
defined as:
normalDist(x) = 1/$(SQRT) &pi; $(INTEGRAL -$(INFINITY), x) exp( - $(POWER t, 2)/2) dt
    = 0.5 + 0.5 * erf(x/sqrt(2))
    = 0.5 * erfc(- x/sqrt(2))
To maintain accuracy at high values of x, use
normalDistribution(x) = 1 - normalDistribution(-x).
Accuracy:
Within a few bits of machine resolution over the entire
range.
References:
$(LINK http://www.netlib.org/cephes/ldoubdoc.html),
G. Marsaglia, "Evaluating the Normal Distribution",
Journal of Statistical Software <b>11</b>, (July 2004).
+/
deprecated("normalDistribution renamed, use normalCDF instead")
T normalDistribution(T)(const T a)
    if (isFloatingPoint!T)
{
    pragma(inline, false);
    import mir.math.constant: SQRT1_2;

    T x = a * T(SQRT1_2);
    T z = fabs(x);

    if (z < 1)
    {
        return 0.5f + 0.5f * erf(x);
    }
    else
    {
        T y = 0.5f * erfce(z);
        /* Multiply by exp(-x^2 / 2)  */
        z = expx2(a, -1);
        y = y * sqrt(z);
        if (x > 0)
            y = 1 - y;
        return y;
    }
}

/// ditto
deprecated("normalDistribution renamed, use normalCDF instead")
T normalDistribution(T)(const T x, const T mean, const T stdDev)
    if (isFloatingPoint!T)
{
    return normalDistribution((x - mean) / stdDev);
}

version(mir_test_deprecated)
@safe unittest
{
    assert(fabs(normalDistribution(1.0L) - (0.841344746068543))< 0.0000000000000005);
}

/++
Computes the normal distribution cumulative distribution function (CDF).
The normal (or Gaussian, or bell-shaped) distribution is
defined as:
normalDist(x) = 1/$(SQRT) &pi; $(INTEGRAL -$(INFINITY), x) exp( - $(POWER t, 2)/2) dt
    = 0.5 + 0.5 * erf(x/sqrt(2))
    = 0.5 * erfc(- x/sqrt(2))
To maintain accuracy at high values of x, use
normalCDF(x) = 1 - normalCDF(-x).
Accuracy:
Within a few bits of machine resolution over the entire
range.
References:
$(LINK http://www.netlib.org/cephes/ldoubdoc.html),
G. Marsaglia, "Evaluating the Normal Distribution",
Journal of Statistical Software <b>11</b>, (July 2004).
+/
T normalCDF(T)(const T a)
    if (isFloatingPoint!T)
{
    pragma(inline, false);
    import mir.math.constant: SQRT1_2;

    T x = a * T(SQRT1_2);
    T z = fabs(x);

    if (z < 1)
    {
        return 0.5f + 0.5f * erf(x);
    }
    else
    {
        T y = 0.5f * erfce(z);
        /* Multiply by exp(-x^2 / 2)  */
        z = expx2(a, -1);
        y = y * sqrt(z);
        if (x > 0)
            y = 1 - y;
        return y;
    }
}

/// ditto
T normalCDF(T)(const T x, const T mean, const T stdDev)
    if (isFloatingPoint!T)
{
    return normalCDF((x - mean) / stdDev);
}

version(mir_test)
@safe unittest
{
    assert(fabs(normalCDF(1.0L) - (0.841344746068543))< 0.0000000000000005);
}

///
deprecated("normalDistributionInverse renamed, use normalInvCDF instead")
T normalDistributionInverse(T)(const T p)
in {
  assert(p >= 0 && p <= 1, "Domain error");
}
do
{
    pragma(inline, false);
    if (p <= 0 || p >= 1)
    {
        if (p == 0)
            return -T.infinity;
        if ( p == 1 )
            return T.infinity;
        return T.nan; // domain error
    }
    int code = 1;
    T y = p;
    if ( y > (1 - T(EXP_2)) )
    {
        y = 1 - y;
        code = 0;
    }

    T x, z, y2, x0, x1;

    if ( y > T(EXP_2) )
    {
        y = y - 0.5L;
        y2 = y * y;
        x = y + y * (y2 * rationalPoly!(P0, Q0)(y2));
        return x * double(SQRT2PI);
    }

    x = sqrt( -2 * log(y) );
    x0 = x - log(x)/x;
    z = 1/x;
    if ( x < 8 )
    {
        x1 = z * rationalPoly!(P1, Q1)(z);
    }
    else if ( x < 32 )
    {
        x1 = z * rationalPoly!(P2, Q2)(z);
    }
    else
    {
        x1 = z * rationalPoly!(P3, Q3)(z);
    }
    x = x0 - x1;
    if ( code != 0 )
    {
        x = -x;
    }
    return x;
}

/// ditto
deprecated("normalDistributionInverse renamed, use normalInvCDF instead")
T normalDistributionInverse(T)(const T p, const T mean, const T stdDev)
    if (isFloatingPoint!T)
{
    return normalDistributionInverse(p) * stdDev + mean;
}

///
version(mir_test_deprecated)
@safe unittest
{
    import std.math: feqrel;
    // TODO: Use verified test points.
    // The values below are from Excel 2003.
    assert(fabs(normalDistributionInverse(0.001) - (-3.09023230616779))< 0.00000000000005);
    assert(fabs(normalDistributionInverse(1e-50) - (-14.9333375347885))< 0.00000000000005);
    assert(feqrel(normalDistributionInverse(0.999L), -normalDistributionInverse(0.001L)) > real.mant_dig-6);

    // Excel 2003 gets all the following values wrong!
    assert(normalDistributionInverse(0.0) == -real.infinity);
    assert(normalDistributionInverse(1.0) == real.infinity);
    assert(normalDistributionInverse(0.5) == 0);
    // (Excel 2003 returns norminv(p) = -30 for all p < 1e-200).
    // The value tested here is the one the function returned in Jan 2006.
    real unknown1 = normalDistributionInverse(1e-250L);
    assert( fabs(unknown1 -(-33.79958617269L) ) < 0.00000005);
}

///
T normalInvCDF(T)(const T p)
in {
  assert(p >= 0 && p <= 1, "Domain error");
}
do
{
    pragma(inline, false);
    if (p <= 0 || p >= 1)
    {
        if (p == 0)
            return -T.infinity;
        if ( p == 1 )
            return T.infinity;
        return T.nan; // domain error
    }
    int code = 1;
    T y = p;
    if ( y > (1 - T(EXP_2)) )
    {
        y = 1 - y;
        code = 0;
    }

    T x, z, y2, x0, x1;

    if ( y > T(EXP_2) )
    {
        y = y - 0.5L;
        y2 = y * y;
        x = y + y * (y2 * rationalPoly!(P0, Q0)(y2));
        return x * double(SQRT2PI);
    }

    x = sqrt( -2 * log(y) );
    x0 = x - log(x)/x;
    z = 1/x;
    if ( x < 8 )
    {
        x1 = z * rationalPoly!(P1, Q1)(z);
    }
    else if ( x < 32 )
    {
        x1 = z * rationalPoly!(P2, Q2)(z);
    }
    else
    {
        x1 = z * rationalPoly!(P3, Q3)(z);
    }
    x = x0 - x1;
    if ( code != 0 )
    {
        x = -x;
    }
    return x;
}

/// ditto
T normalInvCDF(T)(const T p, const T mean, const T stdDev)
    if (isFloatingPoint!T)
{
    return normalInvCDF(p) * stdDev + mean;
}

///
version(mir_test)
@safe unittest
{
    import std.math: feqrel;
    // TODO: Use verified test points.
    // The values below are from Excel 2003.
    assert(fabs(normalInvCDF(0.001) - (-3.09023230616779))< 0.00000000000005);
    assert(fabs(normalInvCDF(1e-50) - (-14.9333375347885))< 0.00000000000005);
    assert(feqrel(normalInvCDF(0.999L), -normalInvCDF(0.001L)) > real.mant_dig-6);

    // Excel 2003 gets all the following values wrong!
    assert(normalInvCDF(0.0) == -real.infinity);
    assert(normalInvCDF(1.0) == real.infinity);
    assert(normalInvCDF(0.5) == 0);
    // (Excel 2003 returns norminv(p) = -30 for all p < 1e-200).
    // The value tested here is the one the function returned in Jan 2006.
    real unknown1 = normalInvCDF(1e-250L);
    assert( fabs(unknown1 -(-33.79958617269L) ) < 0.00000005);
}

///
enum real SQRT2PI = 2.50662827463100050241576528481104525L; // sqrt(2pi)
///
enum real SQRT2PIINV = 1 / SQRT2PI; // 1 / sqrt(2pi)

private:

enum real EXP_2  = 0.135335283236612691893999494972484403L; /* exp(-2) */

///
enum T MAXLOG(T) = log(T.max);
///
enum T MINLOG(T) = log(T.min_normal * T.epsilon); // log(smallest denormal);

/**
 *  Exponential of squared argument
 *
 * Computes y = exp(x*x) while suppressing error amplification
 * that would ordinarily arise from the inexactness of the
 * exponential argument x*x.
 *
 * If sign < 0, the result is inverted; i.e., y = exp(-x*x) .
 *
 * ACCURACY:
 *                      Relative error:
 * arithmetic      domain        # trials      peak         rms
 *   IEEE     -106.566, 106.566    10^5       1.6e-19     4.4e-20
 */
T expx2(T)(const T x_, int sign)
{
    /*
    Cephes Math Library Release 2.9:  June, 2000
    Copyright 2000 by Stephen L. Moshier
    */
    const T M = 32_768.0;
    const T MINV = 3.0517578125e-5L;

    T x = fabs(x_);
    if (sign < 0)
        x = -x;

  /* Represent x as an exact multiple of M plus a residual.
     M is a power of 2 chosen so that exp(m * m) does not overflow
     or underflow and so that |x - m| is small.  */
    T m = MINV * floor(M * x + 0.5f);
    T f = x - m;

    /* x^2 = m^2 + 2mf + f^2 */
    T u = m * m;
    T u1 = 2 * m * f  +  f * f;

    if (sign < 0)
    {
        u = -u;
        u1 = -u1;
    }

    if (u + u1 > MAXLOG!T)
        return T.infinity;

    /* u is exact, u1 is small.  */
    return exp(u) * exp(u1);
}

/**
   Exponentially scaled erfc function
   exp(x^2) erfc(x)
   valid for x > 1.
   Use with ndtrl and expx2l.  */

T erfce(T)(const T x)
{
    T y = 1 / x;

    if (x < 8)
    {
        return rationalPoly!(P, Q)(y);
    }
    else
    {
        return y * rationalPoly!(R, S)(y * y);
    }
}

private T rationalPoly(alias numerator, alias denominator, T)(const T x) pure nothrow
{
    return x.poly!numerator / x.poly!denominator;
}

private T poly(alias vec, T)(const T x)
{
    import mir.internal.utility: Iota;
    T y = T(vec[$ - 1]);
    foreach_reverse(i; Iota!(vec.length - 1))
    {
        y *= x;
        y += T(vec[i]);
    }
    return y;
}

/* erfc(x) = exp(-x^2) P(1/x)/Q(1/x)
   1/8 <= 1/x <= 1
   Peak relative error 5.8e-21  */
immutable real[10] P = [ -0x1.30dfa809b3cc6676p-17, 0x1.38637cd0913c0288p+18,
   0x1.2f015e047b4476bp+22, 0x1.24726f46aa9ab08p+25, 0x1.64b13c6395dc9c26p+27,
   0x1.294c93046ad55b5p+29, 0x1.5962a82f92576dap+30, 0x1.11a709299faba04ap+31,
   0x1.11028065b087be46p+31, 0x1.0d8ef40735b097ep+30
];

immutable real[11] Q = [ 0x1.14d8e2a72dec49f4p+19, 0x1.0c880ff467626e1p+23,
   0x1.04417ef060b58996p+26, 0x1.404e61ba86df4ebap+28, 0x1.0f81887bc82b873ap+30,
   0x1.4552a5e39fb49322p+31, 0x1.11779a0ceb2a01cep+32, 0x1.3544dd691b5b1d5cp+32,
   0x1.a91781f12251f02ep+31, 0x1.0d8ef3da605a1c86p+30, 1.0
];

/* erfc(x) = exp(-x^2) 1/x R(1/x^2) / S(1/x^2)
    1/128 <= 1/x < 1/8
    Peak relative error 1.9e-21  */
immutable real[5] R = [ 0x1.b9f6d8b78e22459ep-6, 0x1.1b84686b0a4ea43ap-1,
    0x1.b8f6aebe96000c2ap+1, 0x1.cb1dbedac27c8ec2p+2, 0x1.cf885f8f572a4c14p+1
];

immutable real[6] S = [
    0x1.87ae3cae5f65eb5ep-5, 0x1.01616f266f306d08p+0, 0x1.a4abe0411eed6c22p+2,
    0x1.eac9ce3da600abaap+3, 0x1.5752a9ac2faebbccp+3, 1.0
];

/* erf(x)  = x P(x^2)/Q(x^2)
    0 <= x <= 1
    Peak relative error 7.6e-23  */
immutable real[7] T = [ 0x1.0da01654d757888cp+20, 0x1.2eb7497bc8b4f4acp+17,
    0x1.79078c19530f72a8p+15, 0x1.4eaf2126c0b2c23p+11, 0x1.1f2ea81c9d272a2ep+8,
    0x1.59ca6e2d866e625p+2, 0x1.c188e0b67435faf4p-4
];

immutable real[7] U = [ 0x1.dde6025c395ae34ep+19, 0x1.c4bc8b6235df35aap+18,
    0x1.8465900e88b6903ap+16, 0x1.855877093959ffdp+13, 0x1.e5c44395625ee358p+9,
    0x1.6a0fed103f1c68a6p+5, 1.0
];

F erf(F)(const F x)
 if(isFloatingPoint!F)
{
    if (x == 0)
        return x; // deal with negative zero
    if (x == -F.infinity)
        return -1;
    if (x == F.infinity)
        return 1;
    immutable ax = fabs(x);
    if (ax > 1)
        return 1 - erfc(x);

    return x * rationalPoly!(T, U)(x * x);
}

/**
 *  Complementary error function
 *
 * erfc(x) = 1 - erf(x), and has high relative accuracy for
 * values of x far from zero. (For values near zero, use erf(x)).
 *
 *  1 - erf(x) =  2/ $(SQRT)(&pi;)
 *     $(INTEGRAL x, $(INFINITY)) exp( - $(POWER t, 2)) dt
 *
 *
 * For small x, erfc(x) = 1 - erf(x); otherwise rational
 * approximations are computed.
 *
 * A special function expx2(x) is used to suppress error amplification
 * in computing exp(-x^2).
 */
T erfc(T)(const T a)
{
    if (a == T.infinity)
        return 0;
    if (a == -T.infinity)
        return 2;

    immutable x = (a < 0) ? -a : a;

    if (x < 1)
        return 1 - erf(a);

    if (-a * a < -MAXLOG!T)
    {
        // underflow
        if (a < 0) return 2;
        else return 0;
    }

    T y;
    immutable z = expx2(a, -1);

    y = 1 / x;
    if (x < 8)
        y = z * rationalPoly!(P, Q)(y);
    else
        y = z * y * rationalPoly!(R, S)(y * y);

    if (a < 0)
        y = 2 - y;

    if (y == 0)
    {
        // underflow
        if (a < 0) return 2;
        else return 0;
    }

    return y;
}

static immutable real[8] P0 =
[ -0x1.758f4d969484bfdcp-7, 0x1.53cee17a59259dd2p-3,
-0x1.ea01e4400a9427a2p-1,  0x1.61f7504a0105341ap+1, -0x1.09475a594d0399f6p+2,
0x1.7c59e7a0df99e3e2p+1, -0x1.87a81da52edcdf14p-1,  0x1.1fb149fd3f83600cp-7
];

static immutable real[8] Q0 =
[ -0x1.64b92ae791e64bb2p-7, 0x1.7585c7d597298286p-3,
-0x1.40011be4f7591ce6p+0, 0x1.1fc067d8430a425ep+2, -0x1.21008ffb1e7ccdf2p+3,
0x1.3d1581cf9bc12fccp+3, -0x1.53723a89fd8f083cp+2, 1.0
];

static immutable real[10] P1 =
[ 0x1.20ceea49ea142f12p-13, 0x1.cbe8a7267aea80bp-7,
0x1.79fea765aa787c48p-2, 0x1.d1f59faa1f4c4864p+1, 0x1.1c22e426a013bb96p+4,
0x1.a8675a0c51ef3202p+5, 0x1.75782c4f83614164p+6, 0x1.7a2f3d90948f1666p+6,
0x1.5cd116ee4c088c3ap+5, 0x1.1361e3eb6e3cc20ap+2
];

static immutable real[10] Q1 =
[ 0x1.3a4ce1406cea98fap-13, 0x1.f45332623335cda2p-7,
0x1.98f28bbd4b98db1p-2, 0x1.ec3b24f9c698091cp+1, 0x1.1cc56ecda7cf58e4p+4,
0x1.92c6f7376bf8c058p+5, 0x1.4154c25aa47519b4p+6, 0x1.1b321d3b927849eap+6,
0x1.403a5f5a4ce7b202p+4, 1.0
];

static immutable real[8] P2 =
[ 0x1.8c124a850116a6d8p-21, 0x1.534abda3c2fb90bap-13,
0x1.29a055ec93a4718cp-7, 0x1.6468e98aad6dd474p-3, 0x1.3dab2ef4c67a601cp+0,
0x1.e1fb3a1e70c67464p+1, 0x1.b6cce8035ff57b02p+2, 0x1.9f4c9e749ff35f62p+1
];

static immutable real[8] Q2 =
[ 0x1.af03f4fc0655e006p-21, 0x1.713192048d11fb2p-13,
0x1.4357e5bbf5fef536p-7, 0x1.7fdac8749985d43cp-3, 0x1.4a080c813a2d8e84p+0,
0x1.c3a4b423cdb41bdap+1, 0x1.8160694e24b5557ap+2, 1.0
];

static immutable real[8] P3 =
[ -0x1.55da447ae3806168p-34, -0x1.145635641f8778a6p-24,
-0x1.abf46d6b48040128p-17, -0x1.7da550945da790fcp-11, -0x1.aa0b2a31157775fap-8,
0x1.b11d97522eed26bcp-3, 0x1.1106d22f9ae89238p+1, 0x1.029a358e1e630f64p+1
];

static immutable real[8] Q3 =
[ -0x1.74022dd5523e6f84p-34, -0x1.2cb60d61e29ee836p-24,
-0x1.d19e6ec03a85e556p-17, -0x1.9ea2a7b4422f6502p-11, -0x1.c54b1e852f107162p-8,
0x1.e05268dd3c07989ep-3, 0x1.239c6aff14afbf82p+1, 1.0
];
