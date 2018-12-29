/++
Ranges.

See_also: $(MREF mir,_primitives).

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors:   Ilya Yaroshenko, Phobos Team (findRoot)
+/
module mir.numeric;

import mir.internal.utility: isFloatingPoint;
import mir.math.common;
import mir.math.ieee;

import std.typecons: Tuple, tuple;
import std.traits: Unqual, ReturnType;

/**  Find a real root of a real function f(x) via bracketing.
 *
 * Given a function `f` and a range `[a .. b]` such that `f(a)`
 * and `f(b)` have opposite signs or at least one of them equals ±0,
 * returns the value of `x` in
 * the range which is closest to a root of `f(x)`.  If `f(x)`
 * has more than one root in the range, one will be chosen
 * arbitrarily.  If `f(x)` returns NaN, NaN will be returned;
 * otherwise, this algorithm is guaranteed to succeed.
 *
 * Uses an algorithm based on TOMS748, which uses inverse cubic
 * interpolation whenever possible, otherwise reverting to parabolic
 * or secant interpolation. Compared to TOMS748, this implementation
 * improves worst-case performance by a factor of more than 100, and
 * typical performance by a factor of 2. For 80-bit reals, most
 * problems require 8 to 15 calls to `f(x)` to achieve full machine
 * precision. The worst-case performance (pathological cases) is
 * approximately twice the number of bits.
 *
 * References: "On Enclosing Simple Roots of Nonlinear Equations",
 * G. Alefeld, F.A. Potra, Yixun Shi, Mathematics of Computation 61,
 * pp733-744 (1993).  Fortran code available from $(HTTP
 * www.netlib.org,www.netlib.org) as algorithm TOMS478.
 *
 */
@optmath
T findRoot(T, DF, DT)(scope DF f, in T a, in T b,
    scope DT tolerance) //= (T a, T b) => false)
if (
    isFloatingPoint!T &&
    is(typeof(tolerance(T.init, T.init)): bool) &&
    is(typeof(f(T.init)) == R, R) && isFloatingPoint!R
    )
{
    immutable fa = f(a);
    if (fa == 0)
        return a;
    immutable fb = f(b);
    if (fb == 0)
        return b;
    immutable r = findRoot(f, a, b, fa, fb, tolerance);
    // Return the first value if it is smaller or NaN
    return !(fabs(r[2]) > fabs(r[3])) ? r[0]: r[1];
}

///ditto
T findRoot(T, DF)(scope DF f, in T a, in T b)
{
    return findRoot(f, a, b, (T a, T b) => false);
}

/** Find root of a real function f(x) by bracketing, allowing the
 * termination condition to be specified.
 *
 * Params:
 *
 * f = Function to be analyzed
 *
 * ax = Left bound of initial range of `f` known to contain the
 * root.
 *
 * bx = Right bound of initial range of `f` known to contain the
 * root.
 *
 * fax = Value of `f(ax)`.
 *
 * fbx = Value of `f(bx)`. `fax` and `fbx` should have opposite signs.
 * (`f(ax)` and `f(bx)` are commonly known in advance.)
 *
 *
 * tolerance = Defines an early termination condition. Receives the
 *             current upper and lower bounds on the root. The
 *             delegate must return `true` when these bounds are
 *             acceptable. If this function always returns `false`,
 *             full machine precision will be achieved.
 *
 * Returns:
 *
 * A tuple consisting of two ranges. The first two elements are the
 * range (in `x`) of the root, while the second pair of elements
 * are the corresponding function values at those points. If an exact
 * root was found, both of the first two elements will contain the
 * root, and the second pair of elements will be 0.
 */
@optmath
Tuple!(T, T, R, R) findRoot(T, R, DF, DT)(scope DF f, in T ax, in T bx, in R fax, in R fbx,
    scope DT tolerance) // = (T a, T b) => false)
if (
    isFloatingPoint!T &&
    is(typeof(tolerance(T.init, T.init)): bool) &&
    is(typeof(f(T.init)) == R) && isFloatingPoint!R
    )
in
{
    assert(ax == ax && bx == bx, "Limits must not be NaN");
    assert(signbit(fax) != signbit(fbx), "Parameters must bracket the root.");
}
do
{
    // Author: Don Clugston. This code is (heavily) modified from TOMS748
    // (www.netlib.org).  The changes to improve the worst-cast performance are
    // entirely original.

    T a, b, d;  // [a .. b] is our current bracket. d is the third best guess.
    R fa, fb, fd; // Values of f at a, b, d.
    bool done = false; // Has a root been found?

    // Allow ax and bx to be provided in reverse order
    if (ax <= bx)
    {
        a = ax; fa = fax;
        b = bx; fb = fbx;
    }
    else
    {
        a = bx; fa = fbx;
        b = ax; fb = fax;
    }

    // Test the function at point c; update brackets accordingly
    void bracket(T c)
    {
        R fc = f(c);
        if (fc == 0 || fc != fc) // Exact solution, or NaN
        {
            a = c;
            fa = fc;
            d = c;
            fd = fc;
            done = true;
            return;
        }

        // Determine new enclosing interval
        if (signbit(fa) != signbit(fc))
        {
            d = b;
            fd = fb;
            b = c;
            fb = fc;
        }
        else
        {
            d = a;
            fd = fa;
            a = c;
            fa = fc;
        }
    }

   /* Perform a secant interpolation. If the result would lie on a or b, or if
     a and b differ so wildly in magnitude that the result would be meaningless,
     perform a bisection instead.
    */
    static T secant_interpolate(T a, T b, R fa, R fb)
    {
        if (( ((a - b) == a) && b != 0) || (a != 0 && ((b - a) == b)))
        {
            // Catastrophic cancellation
            if (a == 0)
                a = copysign(T(0), b);
            else if (b == 0)
                b = copysign(T(0), a);
            else if (signbit(a) != signbit(b))
                return 0;
            T c = ieeeMean(a, b);
            return c;
        }
        // avoid overflow
        if (b - a > T.max)
            return b * 0.5f + a * 0.5f;
        if (fb - fa > R.max)
            return a - (b - a) * 0.5f;
        T c = a - (fa / (fb - fa)) * (b - a);
        if (c == a || c == b)
            return (a + b) * 0.5f;
        return c;
    }

    /* Uses 'numsteps' newton steps to approximate the zero in [a .. b] of the
       quadratic polynomial interpolating f(x) at a, b, and d.
       Returns:
         The approximate zero in [a .. b] of the quadratic polynomial.
    */
    T newtonQuadratic(int numsteps)
    {
        // Find the coefficients of the quadratic polynomial.
        immutable T a0 = fa;
        immutable T a1 = (fb - fa)/(b - a);
        immutable T a2 = ((fd - fb)/(d - b) - a1)/(d - a);

        // Determine the starting point of newton steps.
        T c = a2.signbit != fa.signbit ? a : b;

        // start the safeguarded newton steps.
        foreach (int i; 0 .. numsteps)
        {
            immutable T pc = a0 + (a1 + a2 * (c - b))*(c - a);
            immutable T pdc = a1 + a2*((2 * c) - (a + b));
            if (pdc == 0)
                return a - a0 / a1;
            else
                c = c - pc / pdc;
        }
        return c;
    }

    // On the first iteration we take a secant step:
    if (fa == 0 || fa != fa)
    {
        done = true;
        b = a;
        fb = fa;
    }
    else if (fb == 0 || fb != fb)
    {
        done = true;
        a = b;
        fa = fb;
    }
    else
    {
        bracket(secant_interpolate(a, b, fa, fb));
    }

    // Starting with the second iteration, higher-order interpolation can
    // be used.
    int itnum = 1;   // Iteration number
    int baditer = 1; // Num bisections to take if an iteration is bad.
    T c, e;  // e is our fourth best guess
    R fe;

whileloop:
    while (!done && (b != nextUp(a)) && !tolerance(a, b))
    {
        T a0 = a, b0 = b; // record the brackets

        // Do two higher-order (cubic or parabolic) interpolation steps.
        foreach (int QQ; 0 .. 2)
        {
            // Cubic inverse interpolation requires that
            // all four function values fa, fb, fd, and fe are distinct;
            // otherwise use quadratic interpolation.
            bool distinct = (fa != fb) && (fa != fd) && (fa != fe)
                         && (fb != fd) && (fb != fe) && (fd != fe);
            // The first time, cubic interpolation is impossible.
            if (itnum<2) distinct = false;
            bool ok = distinct;
            if (distinct)
            {
                // Cubic inverse interpolation of f(x) at a, b, d, and e
                immutable q11 = (d - e) * fd / (fe - fd);
                immutable q21 = (b - d) * fb / (fd - fb);
                immutable q31 = (a - b) * fa / (fb - fa);
                immutable d21 = (b - d) * fd / (fd - fb);
                immutable d31 = (a - b) * fb / (fb - fa);

                immutable q22 = (d21 - q11) * fb / (fe - fb);
                immutable q32 = (d31 - q21) * fa / (fd - fa);
                immutable d32 = (d31 - q21) * fd / (fd - fa);
                immutable q33 = (d32 - q22) * fa / (fe - fa);
                c = a + (q31 + q32 + q33);
                if (c != c || (c <= a) || (c >= b))
                {
                    // DAC: If the interpolation predicts a or b, it's
                    // probable that it's the actual root. Only allow this if
                    // we're already close to the root.
                    if (c == a && a - b != a)
                    {
                        c = nextUp(a);
                    }
                    else if (c == b && a - b != -b)
                    {
                        c = nextDown(b);
                    }
                    else
                    {
                        ok = false;
                    }
                }
            }
            if (!ok)
            {
                // DAC: Alefeld doesn't explain why the number of newton steps
                // should vary.
                c = newtonQuadratic(distinct ? 3: 2);
                if (c != c || (c <= a) || (c >= b))
                {
                    // Failure, try a secant step:
                    c = secant_interpolate(a, b, fa, fb);
                }
            }
            ++itnum;
            e = d;
            fe = fd;
            bracket(c);
            if (done || ( b == nextUp(a)) || tolerance(a, b))
                break whileloop;
            if (itnum == 2)
                continue whileloop;
        }

        // Now we take a double-length secant step:
        T u;
        R fu;
        if (fabs(fa) < fabs(fb))
        {
            u = a;
            fu = fa;
        }
        else
        {
            u = b;
            fu = fb;
        }
        c = u - 2 * (fu / (fb - fa)) * (b - a);

        // DAC: If the secant predicts a value equal to an endpoint, it's
        // probably false.
        if (c == a || c == b || c != c || fabs(c - u) > (b - a) * 0.5f)
        {
            if ((a-b) == a || (b-a) == b)
            {
                if ((a>0 && b<0) || (a<0 && b>0))
                    c = 0;
                else
                {
                    T p1 = void, p2 = void;
                    if (a == 0)
                    {
                        p1 = copysign(T(0), b);
                        p2 = b;
                    }
                    else if (b == 0)
                    {
                        p1 = copysign(T(0), a);
                        p2 = a;
                    }
                    else
                    {
                        p1 = a;
                        p2 = b;
                    }
                    c = ieeeMean(a, b);
                }
            }
            else
            {
                c = a + (b - a) * 0.5f;
            }
        }
        e = d;
        fe = fd;
        bracket(c);
        if (done || (b == nextUp(a)) || tolerance(a, b))
            break;

        // IMPROVE THE WORST-CASE PERFORMANCE
        // We must ensure that the bounds reduce by a factor of 2
        // in binary space! every iteration. If we haven't achieved this
        // yet, or if we don't yet know what the exponent is,
        // perform a binary chop.

        if ((a == 0 || b == 0 ||
            (fabs(a) >= T(0.5) * fabs(b) && fabs(b) >= T(0.5) * fabs(a)))
            &&  (b - a) < T(0.25) * (b0 - a0))
        {
            baditer = 1;
            continue;
        }

        // DAC: If this happens on consecutive iterations, we probably have a
        // pathological function. Perform a number of bisections equal to the
        // total number of consecutive bad iterations.

        if ((b - a) < T(0.25) * (b0 - a0))
            baditer = 1;
        foreach (int QQ; 0 .. baditer)
        {
            e = d;
            fe = fd;

            T w;
            if ((a>0 && b<0) || (a<0 && b>0))
                w = 0;
            else
            {
                T usea = a;
                T useb = b;
                if (a == 0)
                    usea = copysign(T(0), b);
                else if (b == 0)
                    useb = copysign(T(0), a);
                w = ieeeMean(usea, useb);
            }
            bracket(w);
        }
        ++baditer;
    }
    return Tuple!(T, T, R, R)(a, b, fa, fb);
}

///ditto
Tuple!(T, T, R, R) findRoot(T, R, DF)(scope DF f, in T ax, in T bx, in R fax, in R fbx)
{
    return findRoot(f, ax, bx, fax, fbx, (T a, T b) => false);
}

///ditto
T findRoot(T, R)(scope R delegate(T) f, in T a, in T b,
    scope bool delegate(T lo, T hi) tolerance = (T a, T b) => false)
{
    return findRoot!(T, R delegate(T), bool delegate(T lo, T hi))(f, a, b, tolerance);
}

version(mir_test) @safe nothrow unittest
{
    int numProblems = 0;
    int numCalls;

    void testFindRoot(real delegate(real) @nogc @safe nothrow pure f , real x1, real x2) @nogc @safe nothrow pure
    {
        //numCalls=0;
        //++numProblems;
        assert(x1 == x1 && x2 == x2);
        assert(signbit(x1) != signbit(x2));
        auto result = findRoot(f, x1, x2, f(x1), f(x2),
          (real lo, real hi) { return false; });

        auto flo = f(result[0]);
        auto fhi = f(result[1]);
        if (flo != 0)
        {
            assert(flo.signbit != fhi.signbit);
        }
    }

    // Test functions
    real cubicfn(real x) @nogc @safe nothrow pure
    {
        //++numCalls;
        if (x>float.max)
            x = float.max;
        if (x<-double.max)
            x = -double.max;
        // This has a single real root at -59.286543284815
        return 0.386*x*x*x + 23*x*x + 15.7*x + 525.2;
    }
    // Test a function with more than one root.
    real multisine(real x) { ++numCalls; return sin(x); }
    //testFindRoot( &multisine, 6, 90);
    //testFindRoot(&cubicfn, -100, 100);
    //testFindRoot( &cubicfn, -double.max, real.max);


/* Tests from the paper:
 * "On Enclosing Simple Roots of Nonlinear Equations", G. Alefeld, F.A. Potra,
 *   Yixun Shi, Mathematics of Computation 61, pp733-744 (1993).
 */
    // Parameters common to many alefeld tests.
    int n;
    real ale_a, ale_b;

    int powercalls = 0;

    real power(real x)
    {
        ++powercalls;
        ++numCalls;
        return pow(x, n) + double.min_normal;
    }
    int [] power_nvals = [3, 5, 7, 9, 19, 25];
    // Alefeld paper states that pow(x,n) is a very poor case, where bisection
    // outperforms his method, and gives total numcalls =
    // 921 for bisection (2.4 calls per bit), 1830 for Alefeld (4.76/bit),
    /* 0.5f624 for brent (6.8/bit)
    // ... but that is for double, not real80.
    // This poor performance seems mainly due to catastrophic cancellation,
    // which is avoided here by the use of ieeeMean().
    // I get: 231 (0.48/bit).
    // IE this is 10X faster in Alefeld's worst case
    numProblems=0;
    foreach (k; power_nvals)
    {
        n = k;
        //testFindRoot(&power, -1, 10);
    }

    int powerProblems = numProblems;

    // Tests from Alefeld paper

    int [9] alefeldSums;
    real alefeld0(real x)
    {
        ++alefeldSums[0];
        ++numCalls;
        real q =  sin(x) - x/2;
        for (int i=1; i<20; ++i)
            q+=(2*i-5.0)*(2*i-5.0)/((x-i*i)*(x-i*i)*(x-i*i));
        return q;
    }
    real alefeld1(real x)
    {
        ++numCalls;
        ++alefeldSums[1];
        return ale_a*x + exp(ale_b * x);
    }
    real alefeld2(real x)
    {
        ++numCalls;
        ++alefeldSums[2];
        return pow(x, n) - ale_a;
    }
    real alefeld3(real x)
    {
        ++numCalls;
        ++alefeldSums[3];
        return (1.0 +pow(1.0L-n, 2))*x - pow(1.0L-n*x, 2);
    }
    real alefeld4(real x)
    {
        ++numCalls;
        ++alefeldSums[4];
        return x*x - pow(1-x, n);
    }
    real alefeld5(real x)
    {
        ++numCalls;
        ++alefeldSums[5];
        return (1+pow(1.0L-n, 4))*x - pow(1.0L-n*x, 4);
    }
    real alefeld6(real x)
    {
        ++numCalls;
        ++alefeldSums[6];
        return exp(-n*x)*(x-1.01L) + pow(x, n);
    }
    real alefeld7(real x)
    {
        ++numCalls;
        ++alefeldSums[7];
        return (n*x-1)/((n-1)*x);
    }

    numProblems=0;
    //testFindRoot(&alefeld0, PI_2, PI);
    for (n=1; n <= 10; ++n)
    {
        //testFindRoot(&alefeld0, n*n+1e-9L, (n+1)*(n+1)-1e-9L);
    }
    ale_a = -40; ale_b = -1;
    //testFindRoot(&alefeld1, -9, 31);
    ale_a = -100; ale_b = -2;
    //testFindRoot(&alefeld1, -9, 31);
    ale_a = -200; ale_b = -3;
    //testFindRoot(&alefeld1, -9, 31);
    int [] nvals_3 = [1, 2, 5, 10, 15, 20];
    int [] nvals_5 = [1, 2, 4, 5, 8, 15, 20];
    int [] nvals_6 = [1, 5, 10, 15, 20];
    int [] nvals_7 = [2, 5, 15, 20];

    for (int i=4; i<12; i+=2)
    {
       n = i;
       ale_a = 0.2;
       //testFindRoot(&alefeld2, 0, 5);
       ale_a=1;
       //testFindRoot(&alefeld2, 0.95, 4.05);
       //testFindRoot(&alefeld2, 0, 1.5);
    }
    foreach (i; nvals_3)
    {
        n=i;
        //testFindRoot(&alefeld3, 0, 1);
    }
    foreach (i; nvals_3)
    {
        n=i;
        //testFindRoot(&alefeld4, 0, 1);
    }
    foreach (i; nvals_5)
    {
        n=i;
        //testFindRoot(&alefeld5, 0, 1);
    }
    foreach (i; nvals_6)
    {
        n=i;
        //testFindRoot(&alefeld6, 0, 1);
    }
    foreach (i; nvals_7)
    {
        n=i;
        //testFindRoot(&alefeld7, 0.01L, 1);
    }
    real worstcase(real x)
    {
        ++numCalls;
        return x<0.3*real.max? -0.999e-3: 1.0;
    }
    //testFindRoot(&worstcase, -real.max, real.max);

    // just check that the double + float cases compile
    //findRoot((double x){ return 0.0; }, -double.max, double.max);
    //findRoot((float x){ return 0.0f; }, -float.max, float.max);

/*
   int grandtotal=0;
   foreach (calls; alefeldSums)
   {
       grandtotal+=calls;
   }
   grandtotal-=2*numProblems;
   printf("\nALEFELD TOTAL = %d avg = %f (alefeld avg=19.3 for double)\n",
   grandtotal, (1.0*grandtotal)/numProblems);
   powercalls -= 2*powerProblems;
   printf("POWER TOTAL = %d avg = %f ", powercalls,
        (1.0*powercalls)/powerProblems);
*/
    //Issue 14231
    auto xp = findRoot((float x) => x, 0f, 1f);
    auto xn = findRoot((float x) => x, -1f, -0f);
}

//regression control
version(mir_test) @system unittest
{
    // @system due to the case in the 2nd line
    static assert(__traits(compiles, findRoot((float x)=>cast(real) x, float.init, float.init)));
    static assert(__traits(compiles, findRoot!real((x)=>cast(double) x, real.init, real.init)));
    static assert(__traits(compiles, findRoot((real x)=>cast(double) x, real.init, real.init)));
}

/++
Find a real minimum of a real function `f(x)` via bracketing.
Given a function `f` and a range `(ax .. bx)`,
returns the value of `x` in the range which is closest to a minimum of `f(x)`.
`f` is never evaluted at the endpoints of `ax` and `bx`.
If `f(x)` has more than one minimum in the range, one will be chosen arbitrarily.
If `f(x)` returns NaN or -Infinity, `(x, f(x), NaN)` will be returned;
otherwise, this algorithm is guaranteed to succeed.
Params:
    f = Function to be analyzed
    ax = Left bound of initial range of f known to contain the minimum.
    bx = Right bound of initial range of f known to contain the minimum.
    relTolerance = Relative tolerance.
    absTolerance = Absolute tolerance.
Preconditions:
    `ax` and `bx` shall be finite reals. $(BR)
    `relTolerance` shall be normal positive real. $(BR)
    `absTolerance` shall be normal positive real no less then `T.epsilon*2`.
Returns:
    A tuple consisting of `x`, `y = f(x)` and `error = 3 * (absTolerance * fabs(x) + relTolerance)`.
    The method used is a combination of golden section search and
successive parabolic interpolation. Convergence is never much slower
than that for a Fibonacci search.
References:
    "Algorithms for Minimization without Derivatives", Richard Brent, Prentice-Hall, Inc. (1973)
See_Also: $(LREF findRoot), $(REF isNormal, std,math)
+/
@optmath
Tuple!(T, "x", Unqual!(ReturnType!DF), "y", T, "error")
findLocalMin(T, DF)(
        scope DF f,
        in T ax,
        in T bx,
        in T relTolerance = sqrt(T.epsilon),
        in T absTolerance = sqrt(T.epsilon),
        )
if (isFloatingPoint!T
    && __traits(compiles, {T _ = DF.init(T.init);}))
in
{
    assert(ax.fabs < T.infinity, "ax is not finite");
    assert(bx.fabs < T.infinity, "bx is not finite");
    assert(relTolerance.fabs >= T.min_normal && relTolerance.fabs < T.infinity, "relTolerance is not normal floating point number");
    assert(absTolerance.fabs >= T.min_normal && absTolerance.fabs < T.infinity, "absTolerance is not normal floating point number");
    assert(relTolerance >= 0, "absTolerance is not positive");
    assert(absTolerance >= T.epsilon*2, "absTolerance is not greater then `2*T.epsilon`");
}
out (result)
{
    assert(result.x.fabs < T.infinity);
}
do
{
    alias R = typeof(ReturnType!DF(0) + T(0));
    // c is the squared inverse of the golden ratio
    // (3 - sqrt(5))/2
    // Value obtained from Wolfram Alpha.
    enum T c = 0x0.61c8864680b583ea0c633f9fa31237p+0L;
    enum T cm1 = 0x0.9e3779b97f4a7c15f39cc0605cedc8p+0L;
    R tolerance;
    T a = ax > bx ? bx: ax;
    T b = ax > bx ? ax: bx;
    // sequence of declarations suitable for SIMD instructions
    T  v = a * cm1 + b * c;
    assert(v.fabs < T.infinity);
    R fv = f(v);
    if (fv != fv || fv == -T.infinity)
    {
        return typeof(return)(v, fv, T.init);
    }
    T  w = v;
    R fw = fv;
    T  x = v;
    R fx = fv;
    size_t i;
    for (R d = 0, e = 0;;)
    {
        i++;
        T m = (a + b) * 0.5f;
        // This fix is not part of the original algorithm
        if (!((m.fabs < T.infinity))) // fix infinity loop. Issue can be reproduced in R.
        {
            // force disabled fused FMA math
            static auto half(T x)
            {
                pragma(inline, false);
                return x * 0.5f;
            }
            m = half(a) + half(b);
        }
        tolerance = absTolerance * fabs(x) + relTolerance;
        immutable t2 = tolerance * 2;
        // check stopping criterion
        if (!(fabs(x - m) > t2 - (b - a) * 0.5f))
        {
            break;
        }
        R p = 0;
        R q = 0;
        R r = 0;
        // fit parabola
        if (fabs(e) > tolerance)
        {
            immutable  xw =  x -  w;
            immutable fxw = fx - fw;
            immutable  xv =  x -  v;
            immutable fxv = fx - fv;
            immutable xwfxv = xw * fxv;
            immutable xvfxw = xv * fxw;
            p = xv * xvfxw - xw * xwfxv;
            q = (xvfxw - xwfxv) * 2;
            if (q > 0)
                p = -p;
            else
                q = -q;
            r = e;
            e = d;
        }
        T u;
        // a parabolic-interpolation step
        if (fabs(p) < fabs(q * r * 0.5f) && p > q * (a - x) && p < q * (b - x))
        {
            d = p / q;
            u = x + d;
            // f must not be evaluated too close to a or b
            if (u - a < t2 || b - u < t2)
                d = x < m ? tolerance: -tolerance;
        }
        // a golden-section step
        else
        {
            e = (x < m ? b: a) - x;
            d = c * e;
        }
        // f must not be evaluated too close to x
        u = x + (fabs(d) >= tolerance ? d: d > 0 ? tolerance: -tolerance);
        immutable fu = f(u);
        if (fu != fu || fu == -T.infinity)
        {
            return typeof(return)(u, fu, T.init);
        }
        //  update  a, b, v, w, and x
        if (fu <= fx)
        {
            (u < x ? b: a) = x;
            v = w; fv = fw;
            w = x; fw = fx;
            x = u; fx = fu;
        }
        else
        {
            (u < x ? a: b) = u;
            if (fu <= fw || w == x)
            {
                v = w; fv = fw;
                w = u; fw = fu;
            }
            else if (fu <= fv || v == x || v == w)
            { // do not remove this braces
                v = u; fv = fu;
            }
        }
    }
    return typeof(return)(x, fx, tolerance * 3);
}

///
version(mir_test) @safe unittest
{
    import mir.math.common: approxEqual;

    auto ret = findLocalMin((double x) => (x-4)^^2, -1e7, 1e7);
    assert(ret.x.approxEqual(4.0));
    assert(ret.y.approxEqual(0.0));
}

version(mir_test) @safe unittest
{
    import mir.math.common: approxEqual;
    import std.meta: AliasSeq;
    alias isNaN = x => x != x;
    static foreach (T; AliasSeq!(double, float, real))
    {
        {
            auto ret = findLocalMin!T((T x) => (x-4)^^2, T.min_normal, 1e7);
            assert(ret.x.approxEqual(T(4)));
            assert(ret.y.approxEqual(T(0)));
        }
        {
            auto ret = findLocalMin!T((T x) => fabs(x-1), -T.max/4, T.max/4, T.min_normal, 2*T.epsilon);
            assert(approxEqual(ret.x, T(1)));
            assert(approxEqual(ret.y, T(0)));
            assert(ret.error <= 10 * T.epsilon);
        }
        {
            auto ret = findLocalMin!T((T x) => T.init, 0, 1, T.min_normal, 2*T.epsilon);
            assert(!isNaN(ret.x));
            assert(isNaN(ret.y));
            assert(isNaN(ret.error));
        }
        {
            auto ret = findLocalMin!T((T x) => log(x), 0, 1, T.min_normal, 2*T.epsilon);
            assert(ret.error < 3.00001 * ((2*T.epsilon)*fabs(ret.x)+ T.min_normal));
            assert(ret.x >= 0 && ret.x <= ret.error);
        }
        {
            auto ret = findLocalMin!T((T x) => log(x), 0, T.max, T.min_normal, 2*T.epsilon);
            assert(ret.y < -18);
            assert(ret.error < 5e-08);
            assert(ret.x >= 0 && ret.x <= ret.error);
        }
        {
            auto ret = findLocalMin!T((T x) => -fabs(x), -1, 1, T.min_normal, 2*T.epsilon);
            assert(ret.x.fabs.approxEqual(T(1)));
            assert(ret.y.fabs.approxEqual(T(1)));
            assert(ret.error.approxEqual(T(0)));
        }
    }
}
