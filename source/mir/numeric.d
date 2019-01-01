/++
Base numeric algorithms.

Reworked part of `std.numeric`.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors:   Ilya Yaroshenko (API, findLocalMin), Don Clugston (findRoot)
+/
module mir.numeric;

import mir.internal.utility: isFloatingPoint;
import mir.math.common;
import mir.math.ieee;

version(D_Exceptions)
{
    private static immutable findRoot_badBounds = new Exception("findRoot/findLocalMin: f(ax) and f(bx) must have opposite signs to bracket the root.");
    private static immutable findRoot_nanX = new Exception("findRoot/findLocalMin: ax or bx is NaN.");
    private static immutable findRoot_nanY = new Exception("findRoot/findLocalMin: f(x) returned NaN.");
}

/++
+/
enum FindRootStatus
{
    /// Success
    success,
    ///
    badBounds,
    /// 
    nanX,
    ///
    nanY,
}

/++
+/
struct FindRootResult(T)
{
    /// Left bound
    T ax = 0;
    /// Rifht bound
    T bx = 0;
    /// `f(ax)` or `f(ax).fabs.fmin(T.max / 2).copysign(f(ax))`.
    T ay = 0;
    /// `f(bx)` or `f(bx).fabs.fmin(T.max / 2).copysign(f(bx))`.
    T by = 0;

@safe pure @nogc scope const @property:

    /++
    Returns: self
    Required_versions:`D_Exceptions`
    Throws: `Exception` if $(LREF FindRootResult.status) isn't $(LREF FindRootStatus.success).
    +/
    version(D_Exceptions)
    ref validate() return
    {
        with(FindRootStatus) final switch(status)
        {
            case success: return this;
            case badBounds: throw findRoot_badBounds;
            case nanX: throw findRoot_nanX;
            case nanY: throw findRoot_nanY;
        }
    }

nothrow:

    /++
    Returns: $(LREF FindRootStatus)
    +/
    FindRootStatus status()
    {
        with(FindRootStatus) return
            ax != ax || bx != bx ? nanX :
            ay != ay || by != by ? nanY :
            ay.signbit == by.signbit && ay != 0 && by != 0 ? badBounds :
            success;
    }

    /++
    A bound that corresponds to the minimal absolute function value.

    Returns: `!(ay.fabs > by.fabs) ? ax : bx`
    +/
    T x()
    {
        return !(ay.fabs > by.fabs) ? ax : bx;
    }

    /++
    The minimal of absolute function values.

    Returns: `!(ay.fabs > by.fabs) ? ay : by`
    +/
    T y()
    {
        return !(ay.fabs > by.fabs) ? ay : by;
    }
}

/++
Find root of a real function f(x) by bracketing, allowing the
termination condition to be specified.

Given a function `f` and a range `[a .. b]` such that `f(a)`
and `f(b)` have opposite signs or at least one of them equals ±0,
returns the value of `x` in
the range which is closest to a root of `f(x)`.  If `f(x)`
has more than one root in the range, one will be chosen
arbitrarily.  If `f(x)` returns NaN, NaN will be returned;
otherwise, this algorithm is guaranteed to succeed.

Uses an algorithm based on TOMS748, which uses inverse cubic
interpolation whenever possible, otherwise reverting to parabolic
or secant interpolation. Compared to TOMS748, this implementation
improves worst-case performance by a factor of more than 100, and
typical performance by a factor of 2. For 80-bit reals, most
problems require 8 to 15 calls to `f(x)` to achieve full machine
precision. The worst-case performance (pathological cases) is
approximately twice the number of bits.

References: "On Enclosing Simple Roots of Nonlinear Equations",
G. Alefeld, F.A. Potra, Yixun Shi, Mathematics of Computation 61,
pp733-744 (1993).  Fortran code available from $(HTTP
www.netlib.org,www.netlib.org) as algorithm TOMS478.

Params:
f = Function to be analyzed. `f(ax)` and `f(bx)` should have opposite signs.
tolerance = tolerance = Defines an early termination condition. Receives the
            current upper and lower bounds on the root. The
            delegate must return `true` when these bounds are
            acceptable. If this function always returns `false` or
            it is null, full machine precision will be achieved.
ax = Left bound of initial range of `f` known to contain the root.
bx = Right bound of initial range of `f` known to contain the root.
fax = Value of `f(ax)` (optional).
fbx = Value of `f(bx)` (optional).

Returns: $(LREF FindRootResult)
+/
@fmamath
FindRootResult!T findRoot(alias f, alias tolerance = null, T)(
    const T ax,
    const T bx,
    const T fax = -T.nan,
    const T fbx = +T.nan)
    if (
        isFloatingPoint!T && __traits(compiles, T(f(T.init))) &&
        (
            is(typeof(tolerance) == typeof(null)) || 
            __traits(compiles, {auto _ = bool(tolerance(T.init, T.init));}
        )
    ))
{
    if (false) // break attributes
    {
        T y = f(T(123));
        static if (!is(typeof(tolerance) == typeof(null)))
            bool b = tolerance(T(123), T(123));
    }
    scope funInst = delegate(T x) {
        return T(f(x));
    };

    scope fun = funInst.trustedAllAttr;

    scope bool delegate(T, T) @safe pure nothrow @nogc tol;
    static if (!is(typeof(tolerance) == typeof(null)))
    {
        scope tolInst = delegate(T a, T b) {
            return bool(tolerance(a, b));
        };
        tol = tolInst.trustedAllAttr;
    }
    return findRootImpl(ax, bx, fax, fbx, fun, tol);
}

///
version(mir_test) @safe @nogc unittest
{
    import mir.math.common: log, exp;


    auto logRoot = findRoot!log(0, double.infinity).validate.x;
    assert(logRoot == 1);

    auto shift = 1;
    auto expm1Root = findRoot!(x => exp(x) - shift)
        (-double.infinity, double.infinity).validate.x;
    assert(expm1Root == 0);

    auto approxLogRoot = findRoot!(log, (a, b) => fabs(a - b) < 1e-5)(0, double.infinity).validate.x;
    assert(fabs(approxLogRoot - 1) < 1e-5);
}

@fmamath
private FindRootResult!float findRootImpl(
    float ax,
    float bx,
    float fax,
    float fbx,
    scope const float delegate(float) @safe pure nothrow @nogc f,
    scope const bool delegate(float, float) @safe pure nothrow @nogc tolerance = null, //can be null
) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findRootImplGen!float(ax, bx, fax, fbx, f, tolerance);
}

@fmamath
private FindRootResult!double findRootImpl(
    double ax,
    double bx,
    double fax,
    double fbx,
    scope const double delegate(double) @safe pure nothrow @nogc f,
    scope const bool delegate(double, double) @safe pure nothrow @nogc tolerance = null, //can be null
) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findRootImplGen!double(ax, bx, fax, fbx, f, tolerance);
}

@fmamath
private FindRootResult!real findRootImpl(
    real ax,
    real bx,
    real fax,
    real fbx,
    scope const real delegate(real) @safe pure nothrow @nogc f,
    scope const bool delegate(real, real) @safe pure nothrow @nogc tolerance = null, //can be null
) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findRootImplGen!real(ax, bx, fax, fbx, f, tolerance);
}

@fmamath
private FindRootResult!T findRootImplGen(T)(
    const T ax,
    const T bx,
    const T fax,
    const T fbx,
    scope const T delegate(T) @safe pure nothrow @nogc f,
    scope const bool delegate(T, T) @safe pure nothrow @nogc tolerance, //can be null
)
    if (isFloatingPoint!T)
{
    version(LDC) pragma(inline, true);
    // Author: Don Clugston. This code is (heavily) modified from TOMS748
    // (www.netlib.org).  The changes to improve the worst-cast performance are
    // entirely original.
    // Author 2: Ilya Yaroshenko (API improvements, infinity and huge numbers handing, compiled code size reduction)

    T a, b, d;  // [a .. b] is our current bracket. d is the third best guess.
    T fa, fb, fd; // Values of f at a, b, d.
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

    bool exit()
    {
        pragma(inline, false);
        return done || b == nextUp(a) || tolerance !is null && tolerance(a, b);
    }

    // Test the function at point c; update brackets accordingly
    void bracket(T c)
    {
        pragma(inline, false);
        T fc = f(c);
        if (fc == 0 || fc != fc) // Exact solution, or NaN
        {
            a = c;
            fa = fc;
            d = c;
            fd = fc;
            done = true;
            return;
        }

        fc = fc.fabs.fmin(T.max / 2).copysign(fc);

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
    static T secantInterpolate(T a, T b, T fa, T fb)
    {
        pragma(inline, false);
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
        if (b - a == T.infinity)
            return b + a;
        T c = a - (fa / (fb - fa)) * (b - a);
        if (c == a || c == b || c != c)
            return a.half + b.half;
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
        const T a0 = fa;
        const T a1 = (fb - fa)/(b - a);
        const T a2 = ((fd - fb)/(d - b) - a1)/(d - a);

        // Determine the starting point of newton steps.
        T c = a2.signbit != fa.signbit ? a : b;

        // start the safeguarded newton steps.
        foreach (int i; 0 .. numsteps)
        {
            const T pc = a0 + (a1 + a2 * (c - b))*(c - a);
            const T pdc = a1 + a2*((2 * c) - (a + b));
            if (pdc == 0)
                return a - a0 / a1;
            else
                c = c - pc / pdc;
        }
        return c;
    }

    // Starting with the second iteration, higher-order interpolation can
    // be used.
    int itnum = 1;   // Iteration number
    int baditer = 1; // Num bisections to take if an iteration is bad.
    T c, e;  // e is our fourth best guess
    T fe;

    if (a != a || b != b)
    {
        done = true;
        goto whileloop;
    }

    if (a == -T.infinity)
    {
        a = -T.max;
        fa = T.nan;
    }

    if (fa != fa)
        fa = f(a);

    // On the first iteration we take a secant step:
    if (fa == 0 || fa != fa)
    {
        done = true;
        b = a;
        fb = fa;
        goto whileloop;
    }

    if (b == +T.infinity)
    {
        b = +T.max;
        fb = T.nan;
    }

    if (fb != fb)
        fb = f(b);

    if (fb == 0 || fb != fb)
    {
        done = true;
        a = b;
        fa = fb;
        goto whileloop;
    }

    if (fa.signbit == fb.signbit)
    {
        done = true;
        goto whileloop;
    }

    fa = fa.fabs.fmin(T.max / 2).copysign(fa);
    fb = fb.fabs.fmin(T.max / 2).copysign(fb);
    bracket(secantInterpolate(a, b, fa, fb));

whileloop:
    while (!exit)
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
                const q11 = (d - e) * fd / (fe - fd);
                const q21 = (b - d) * fb / (fd - fb);
                const q31 = (a - b) * fa / (fb - fa);
                const d21 = (b - d) * fd / (fd - fb);
                const d31 = (a - b) * fb / (fb - fa);

                const q22 = (d21 - q11) * fb / (fe - fb);
                const q32 = (d31 - q21) * fa / (fd - fa);
                const d32 = (d31 - q21) * fd / (fd - fa);
                const q33 = (d32 - q22) * fa / (fe - fa);
                c = a + (q31 + q32 + q33);
                if (c != c || (c <= a) || (c >= b))
                {
                    // DAC: If the interpolation predicts a or b, it's
                    // probable that it's the actual root. Only allow this if
                    // we're already close to the root.
                    if (c == a && (a - b != a || a - b != -b))
                    {
                        auto down = !(a - b != a);
                        if (down)
                            c = -c;
                        c = c.nextUp;
                        if (down)
                            c = -c;
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
                c = newtonQuadratic(2 + distinct);
                if (c != c || (c <= a) || (c >= b))
                {
                    // Failure, try a secant step:
                    c = secantInterpolate(a, b, fa, fb);
                }
            }
            ++itnum;
            e = d;
            fe = fd;
            bracket(c);
            if (exit)
                break whileloop;
            if (itnum == 2)
                continue whileloop;
        }

        // Now we take a double-length secant step:
        T u;
        T fu;
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
        if (exit)
            break;

        // IMPROVE THE WORST-CASE PERFORMANCE
        // We must ensure that the bounds reduce by a factor of 2
        // in binary space! every iteration. If we haven't achieved this
        // yet, or if we don't yet know what the exponent is,
        // perform a binary chop.

        if ((a == 0 || b == 0 ||
            (fabs(a) >= 0.5f * fabs(b) && fabs(b) >= 0.5f * fabs(a)))
            &&  (b - a) < 0.25f * (b0 - a0))
        {
            baditer = 1;
            continue;
        }

        // DAC: If this happens on consecutive iterations, we probably have a
        // pathological function. Perform a number of bisections equal to the
        // total number of consecutive bad iterations.

        if ((b - a) < 0.25f * (b0 - a0))
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
    return typeof(return)(a, b, fa, fb);
}

version(mir_test) @safe unittest
{
    import mir.math.constant;

    int numProblems = 0;
    int numCalls;

    void testFindRoot(real delegate(real) @nogc @safe nothrow pure f , real x1, real x2) //@nogc @safe nothrow pure
    {
        //numCalls=0;
        //++numProblems;
        assert(x1 == x1 && x2 == x2);
        assert(f(x1).signbit != f(x2).signbit);
        auto result = findRoot!f(x1, x2, f(x1), f(x2)).validate;

        auto flo = f(result.ax);
        auto fhi = f(result.bx);
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
    testFindRoot( &multisine, 6, 90);
    testFindRoot(&cubicfn, -100, 100);
    testFindRoot( &cubicfn, -double.max, real.max);


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
    // 0.5f624 for brent (6.8/bit)
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
    testFindRoot(&alefeld0, PI_2, PI);
    for (n=1; n <= 10; ++n)
    {
        testFindRoot(&alefeld0, n*n+1e-9L, (n+1)*(n+1)-1e-9L);
    }
    ale_a = -40; ale_b = -1;
    testFindRoot(&alefeld1, -9, 31);
    ale_a = -100; ale_b = -2;
    testFindRoot(&alefeld1, -9, 31);
    ale_a = -200; ale_b = -3;
    testFindRoot(&alefeld1, -9, 31);
    int [] nvals_3 = [1, 2, 5, 10, 15, 20];
    int [] nvals_5 = [1, 2, 4, 5, 8, 15, 20];
    int [] nvals_6 = [1, 5, 10, 15, 20];
    int [] nvals_7 = [2, 5, 15, 20];

    for (int i=4; i<12; i+=2)
    {
       n = i;
       ale_a = 0.2;
       testFindRoot(&alefeld2, 0, 5);
       ale_a=1;
       testFindRoot(&alefeld2, 0.95, 4.05);
       testFindRoot(&alefeld2, 0, 1.5);
    }
    foreach (i; nvals_3)
    {
        n=i;
        testFindRoot(&alefeld3, 0, 1);
    }
    foreach (i; nvals_3)
    {
        n=i;
        testFindRoot(&alefeld4, 0, 1);
    }
    foreach (i; nvals_5)
    {
        n=i;
        testFindRoot(&alefeld5, 0, 1);
    }
    foreach (i; nvals_6)
    {
        n=i;
        testFindRoot(&alefeld6, 0, 1);
    }
    foreach (i; nvals_7)
    {
        n=i;
        testFindRoot(&alefeld7, 0.01L, 1);
    }
    real worstcase(real x)
    {
        ++numCalls;
        return x<0.3*real.max? -0.999e-3: 1.0;
    }
    testFindRoot(&worstcase, -real.max, real.max);

    // just check that the double + float cases compile
    findRoot!(x => 0)(-double.max, double.max);
    findRoot!(x => -0.0)(-float.max, float.max);
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
    auto xp = findRoot!(x => x)(0f, 1f);
    auto xn = findRoot!(x => x)(-1f, -0f);
}

/++
+/
struct FindLocalMinResult(T)
{
    ///
    T x = 0;
    ///
    T y = 0;
    ///
    T error = 0;

@safe pure @nogc scope const @property:

    /++
    Returns: self
    Required_versions:`D_Exceptions`
    Throws: `Exception` if $(LREF FindRootResult.status) isn't $(LREF FindRootStatus.success).
    +/
    version(D_Exceptions)
    ref validate() return
    {
        with(FindRootStatus) final switch(status)
        {
            case success: return this;
            case badBounds: throw findRoot_badBounds;
            case nanX: throw findRoot_nanX;
            case nanY: throw findRoot_nanY;
        }
    }

nothrow:

    /++
    Returns: $(LREF FindRootStatus)
    +/
    FindRootStatus status()
    {
        with(FindRootStatus) return
            x != x ? nanX :
            y != y ? nanY :
            success;
    }
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
    A $(LREF FindLocalMinResult) consisting of `x`, `y = f(x)` and `error = 3 * (absTolerance * fabs(x) + relTolerance)`.
    The method used is a combination of golden section search and
successive parabolic interpolation. Convergence is never much slower
than that for a Fibonacci search.
References:
    "Algorithms for Minimization without Derivatives", Richard Brent, Prentice-Hall, Inc. (1973)
See_Also: $(LREF findRoot), $(REF isNormal, std,math)
+/
FindLocalMinResult!T findLocalMin(alias f, T)(
    const T ax,
    const T bx,
    const T relTolerance = sqrt(T.epsilon),
    const T absTolerance = sqrt(T.epsilon))
    if (isFloatingPoint!T && __traits(compiles, T(f(T.init))))
{
    if (false) // break attributes
    {
        T y = f(T(123));
    }
    scope funInst = delegate(T x) {
        return T(f(x));
    };
    scope fun = funInst.trustedAllAttr;

    return findLocalMinImpl(ax, bx, relTolerance, absTolerance, fun);
}

@fmamath
private FindLocalMinResult!float findLocalMinImpl(
    const float ax,
    const float bx,
    const float relTolerance,
    const float absTolerance,
    scope const float delegate(float) @safe pure nothrow @nogc f,
    ) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findLocalMinImplGen!float(ax, bx, relTolerance, absTolerance, f);
}

@fmamath
private FindLocalMinResult!double findLocalMinImpl(
    const double ax,
    const double bx,
    const double relTolerance,
    const double absTolerance,
    scope const double delegate(double) @safe pure nothrow @nogc f,
    ) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findLocalMinImplGen!double(ax, bx, relTolerance, absTolerance, f);
}

@fmamath
private FindLocalMinResult!real findLocalMinImpl(
    const real ax,
    const real bx,
    const real relTolerance,
    const real absTolerance,
    scope const real delegate(real) @safe pure nothrow @nogc f,
    ) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findLocalMinImplGen!real(ax, bx, relTolerance, absTolerance, f);
}

@fmamath
private FindLocalMinResult!T findLocalMinImplGen(T)(
    const T ax,
    const T bx,
    const T relTolerance,
    const T absTolerance,
    scope const T delegate(T) @safe pure nothrow @nogc f,
    )
    if (isFloatingPoint!T && __traits(compiles, {T _ = f(T.init);}))
in
{
    assert(relTolerance.fabs >= T.min_normal && relTolerance.fabs < T.infinity, "relTolerance is not normal floating point number");
    assert(absTolerance.fabs >= T.min_normal && absTolerance.fabs < T.infinity, "absTolerance is not normal floating point number");
    assert(relTolerance >= 0, "absTolerance is not positive");
    assert(absTolerance >= T.epsilon*2, "absTolerance is not greater then `2*T.epsilon`");
}
do
{
    version(LDC) pragma(inline, true);
    // c is the squared inverse of the golden ratio
    // (3 - sqrt(5))/2
    // Value obtained from Wolfram Alpha.
    enum T c   = 0x0.61c8864680b583ea0c633f9fa31237p+0L;
    enum T cm1 = 0x0.9e3779b97f4a7c15f39cc0605cedc8p+0L;
    T tolerance;
    T a = ax > bx ? bx : ax;
    T b = ax > bx ? ax : bx;
    if (a < -T.max)
        a = -T.max;
    if (b > +T.max)
        b = +T.max;
    // sequence of declarations suitable for SIMD instructions
    T  v = a * cm1 + b * c;
    assert(v.fabs < T.infinity);
    T fv = v == v ? f(v) : v;
    if (fv != fv || fv == -T.infinity)
    {
        return typeof(return)(v, fv, T.init);
    }
    T  w = v;
    T fw = fv;
    T  x = v;
    T fx = fv;
    size_t i;
    for (T d = 0, e = 0;;)
    {
        i++;
        T m = (a + b) * 0.5f;
        // This fix is not part of the original algorithm
        if (!((m.fabs < T.infinity))) // fix infinity loop. Issue can be reproduced in R.
        {
            m = a.half + b.half;
        }
        tolerance = absTolerance * fabs(x) + relTolerance;
        const t2 = tolerance * 2;
        // check stopping criterion
        if (!(fabs(x - m) > t2 - (b - a) * 0.5f))
        {
            break;
        }
        T p = 0;
        T q = 0;
        T r = 0;
        // fit parabola
        if (fabs(e) > tolerance)
        {
            const  xw =  x -  w;
            const fxw = fx - fw;
            const  xv =  x -  v;
            const fxv = fx - fv;
            const xwfxv = xw * fxv;
            const xvfxw = xv * fxw;
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
            e = (x < m ? b : a) - x;
            d = c * e;
        }
        // f must not be evaluated too close to x
        u = x + (fabs(d) >= tolerance ? d: d > 0 ? tolerance: -tolerance);
        const fu = f(u);
        if (fu != fu || fu == -T.infinity)
        {
            return typeof(return)(u, fu, T.init);
        }
        //  update  a, b, v, w, and x
        if (fu <= fx)
        {
            (u < x ? b : a) = x;
            v = w; fv = fw;
            w = x; fw = fx;
            x = u; fx = fu;
        }
        else
        {
            (u < x ? a : b) = u;
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
version(mir_test) @safe @nogc unittest
{
    import mir.math.common: approxEqual;

    double shift = 4;

    auto ret = findLocalMin!(x => (x-shift)^^2)(-1e7, 1e7).validate;
    assert(ret.x.approxEqual(shift));
    assert(ret.y.approxEqual(0.0));
}

///
version(mir_test) @safe unittest
{
    import mir.math.common: approxEqual;
    alias AliasSeq(T...) = T;
    static foreach (T; AliasSeq!(double, float, real))
    {
        {
            auto ret = findLocalMin!(x => (x-4)^^2)(T.min_normal, T(1e7)).validate;
            assert(ret.x.approxEqual(T(4)));
            assert(ret.y.approxEqual(T(0)));
        }
        {
            auto ret = findLocalMin!(x => fabs(x-1))(-T.max/4, T.max/4, T.min_normal, 2*T.epsilon).validate;
            assert(approxEqual(ret.x, T(1)));
            assert(approxEqual(ret.y, T(0)));
            assert(ret.error <= 10 * T.epsilon);
        }
        {
            auto ret = findLocalMin!(x => T.init)(0, 1, T.min_normal, 2*T.epsilon);
            assert(ret.status ==  FindRootStatus.nanY);
        }
        {
            auto ret = findLocalMin!log( 0, 1, T.min_normal, 2*T.epsilon).validate;
            assert(ret.error < 3.00001 * ((2*T.epsilon)*fabs(ret.x)+ T.min_normal));
            assert(ret.x >= 0 && ret.x <= ret.error);
        }
        {
            auto ret = findLocalMin!log(0, T.max, T.min_normal, 2*T.epsilon).validate;
            assert(ret.y < -18);
            assert(ret.error < 5e-08);
            assert(ret.x >= 0 && ret.x <= ret.error);
        }
        {
            auto ret = findLocalMin!(x => -fabs(x))(-1, 1, T.min_normal, 2*T.epsilon).validate;
            assert(ret.x.fabs.approxEqual(T(1)));
            assert(ret.y.fabs.approxEqual(T(1)));
            assert(ret.error.approxEqual(T(0)));
        }
    }
}

// force disabled FMA math
private static auto half(T)(const T x)
{
    pragma(inline, false);
    return x * 0.5f;
}

private auto trustedAllAttr(T)(T t) @trusted
{
    import std.traits;
    enum attrs = (functionAttributes!T & ~FunctionAttribute.system) 
        | FunctionAttribute.pure_
        | FunctionAttribute.safe
        | FunctionAttribute.nogc
        | FunctionAttribute.nothrow_;
    return cast(SetFunctionAttributes!(T, functionLinkage!T, attrs)) t;
}
