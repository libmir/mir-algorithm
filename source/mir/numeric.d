/++
Base numeric algorithms.

Reworked part of `std.numeric`.

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko (API, findLocalMin, findRoot extension), Don Clugston (findRoot), Lars Tandle Kyllingstad (diff)
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
enum mir_find_root_status
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

/// ditto
alias FindRootStatus = mir_find_root_status;

/++
+/
struct mir_find_root_result(T)
{
    /// Left bound
    T ax = 0;
    /// Rifht bound
    T bx = 0;
    /// `f(ax)` or `f(ax).fabs.fmin(T.max / 2).copysign(f(ax))`.
    T ay = 0;
    /// `f(bx)` or `f(bx).fabs.fmin(T.max / 2).copysign(f(bx))`.
    T by = 0;
    /// Amount of target function calls.
    uint iterations;

@safe pure @nogc scope const @property:

    /++
    Returns: self
    Required_versions:`D_Exceptions`
    Throws: `Exception` if $(LREF FindRootResult.status) isn't $(LREF mir_find_root_status.success).
    +/
    version(D_Exceptions)
    ref validate() inout return
    {
        with(FindRootStatus) final switch(status)
        {
            case success: return this;
            case badBounds: throw findRoot_badBounds;
            case nanX: throw findRoot_nanX;
            case nanY: throw findRoot_nanY;
        }
    }

extern(C++) nothrow:

    /++
    Returns: $(LREF mir_find_root_status)
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

/// ditto
alias FindRootResult = mir_find_root_result;

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
f = Function to be analyzed. `f(ax)` and `f(bx)` should have opposite signs, or `lowerBound` and/or `upperBound`
    should be defined to perform initial interval extension.
tolerance = Defines an early termination condition. Receives the
            current upper and lower bounds on the root. The
            delegate must return `true` when these bounds are
            acceptable. If this function always returns `false` or
            it is null, full machine precision will be achieved.
ax = Left inner bound of initial range of `f` known to contain the root.
bx = Right inner bound of initial range of `f` known to contain the root. Can be equal to `ax`.
fax = Value of `f(ax)` (optional).
fbx = Value of `f(bx)` (optional).
lowerBound = Lower outer bound for interval extension (optional)
upperBound = Upper outer bound for interval extension (optional)
maxIterations = Appr. maximum allowed number of function calls (inluciding function calls for grid).
steps = Number of nodes in the left side and right side regular grids (optional). If it equals to `0` (default),
        then the algorithm uses `ieeeMean` for searching. The algorithm performs searching if
        `sgn(fax)` equals to `sgn(fbx)` and at least one outer bound allows to extend the inner initial range.

Returns: $(LREF FindRootResult)
+/
@fmamath
FindRootResult!T findRoot(alias f, alias tolerance = null, T)(
    const T ax,
    const T bx,
    const T fax = T.nan,
    const T fbx = T.nan,
    const T lowerBound = T.nan,
    const T upperBound = T.nan,
    uint maxIterations = T.sizeof * 16,
    uint steps = 0,
    )
    if (
        isFloatingPoint!T && __traits(compiles, T(f(T.init))) &&
        (
            is(typeof(tolerance) == typeof(null)) || 
            __traits(compiles, {auto _ = bool(tolerance(T.init, T.init));}
        )
    ))
{
    if (false) // break attributes
        T y = f(T(1));
    scope funInst = delegate(T x) {
        return T(f(x));
    };
    scope fun = funInst.trustedAllAttr;

    static if (is(typeof(tolerance) == typeof(null)))
    {
        alias tol = tolerance;
    }
    else
    {
        if (false) // break attributes
            bool b = tolerance(T(1), T(1));
        scope tolInst = delegate(T a, T b) { return bool(tolerance(a, b)); };
        scope tol = tolInst.trustedAllAttr;
    }
    return findRootImpl(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, steps, fun, tol);
}

///
// @nogc
version(mir_test) @safe unittest
{
    import mir.math.common: log, exp, fabs;

    auto logRoot = findRoot!log(0, double.infinity).validate.x;
    assert(logRoot == 1);

    auto shift = 1;
    auto expm1Root = findRoot!(x => exp(x) - shift)
        (-double.infinity, double.infinity).validate.x;
    assert(expm1Root == 0);

    auto approxLogRoot = findRoot!(log, (a, b) => fabs(a - b) < 1e-5)(0, double.infinity).validate.x;
    assert(fabs(approxLogRoot - 1) < 1e-5);
}

/// With adaptive bounds
version(mir_test) @safe unittest
{
    import mir.math.common: log, exp, fabs;

    auto logRoot = findRoot!log(
            10, 10, // assume we have one initial point
            double.nan, double.nan, // fa, fb aren't provided by user
            -double.infinity, double.infinity, // all space is available for the bounds extension.
        ).validate.x;
    assert(logRoot == 1);

    auto shift = 1;
    alias expm1Fun = (double x) => exp(x) - shift;
    auto expm1RootRet = findRoot!expm1Fun
        (
            11, 10, // reversed order for interval is always OK
            expm1Fun(11), expm1Fun(10), // the order must be the same as bounds
            0, double.infinity, // space for the bounds extension.
        ).validate;
    assert(expm1Fun(expm1RootRet.x) == 0);

    auto approxLogRoot = findRoot!(log, (a, b) => fabs(a - b) < 1e-5)(
            -1e10, +1e10,
            double.nan, double.nan,
            0, double.infinity,
        ).validate.x;
    assert(fabs(approxLogRoot - 1) < 1e-5);
}

/// ditto
unittest
{
    import core.stdc.tgmath: atan;
    import mir.math;
    import std.meta: AliasSeq;

    const double[2][3] boundaries = [
        [0.4, 0.6],
        [1.4, 1.6],
        [0.1, 2.1]];
    
    enum root = 1.0;

    foreach(fun; AliasSeq!(
        (double x) => x ^^ 2 - root,
        (double x) => root - x ^^ 2,
        (double x) => atan(x - root),
    ))
    {
        foreach(ref bounds; boundaries)
        {
            auto result = findRoot!fun(
                bounds[0], bounds[1],
                double.nan, double.nan, // f(a) and f(b) not provided
                -double.max, double.max, // user provided outer bounds
            );
            assert(result.validate.x == root);
        }
    }

    foreach(ref bounds; boundaries)
    {
        auto result = findRoot!(x => sin(x - root))(
            bounds[0], bounds[1],
            double.nan, double.nan, // f(a) and f(b) not provided
            -10, 10, // user provided outer bounds
            100, // max iterations,
            10, // steps for grid
        );
        assert(result.validate.x == root);
    }
    // single initial point, grid, positive direction
    auto result = findRoot!((double x ) => sin(x - root))(
        0.1, 0.1, // initial point, a = b
        double.nan, double.nan, // f(a) = f(b) not provided
        -100.0, 100.0, // user provided outer bounds
        150, // max iterations,
        100, // number of steps for grid
    );
    assert(result.validate.x == root);

    // single initial point, grid, negative direction
    result = findRoot!((double x ) => sin(x - root))(
        0.1, 0.1, // initial point a = b
        double.nan, double.nan, // f(a) = f(b) not provided
        100.0, -100.0, // user provided outer bounds, reversed order
        150, // max iterations,
        100, // number of steps for grid
    );
    assert(result.validate.x == double(root - PI)); // Left side root!
}

/++
With adaptive bounds and single initial point.
Reverse outer bound order controls first step direction
in case of `f(a) == f(b)`.
+/
unittest
{
	enum root = 1.0;

    // roots are +/- `root`
    alias fun = (double x) => x * x - root;

	double lowerBound = -10.0;
	double upperBound = 10.0;

    assert(
        findRoot!fun(
            0, 0, // initial interval
            double.nan, double.nan,
            lowerBound, upperBound,
            // positive direction has higher priority
        ).validate.x == root
    );

    assert(
        findRoot!fun(
            0, 0, // initial interval
            double.nan, double.nan,
            upperBound, lowerBound,
            // reversed order
        ).validate.x == -root // other root
    );
}

/// $(LREF findRoot) implementations.
export @fmamath FindRootResult!float findRootImpl(
    float ax,
    float bx,
    float fax,
    float fbx,
    float lowerBound,
    float upperBound,
    uint maxIterations,
    uint steps,
    scope float delegate(float) @safe pure nothrow @nogc f,
    scope bool delegate(float, float) @safe pure nothrow @nogc tolerance, //can be null
) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findRootImplGen!float(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, steps, f, tolerance);
}

/// ditto
export @fmamath FindRootResult!double findRootImpl(
    double ax,
    double bx,
    double fax,
    double fbx,
    double lowerBound,
    double upperBound,
    uint maxIterations,
    uint steps,
    scope double delegate(double) @safe pure nothrow @nogc f,
    scope bool delegate(double, double) @safe pure nothrow @nogc tolerance, //can be null
) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findRootImplGen!double(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, steps, f, tolerance);
}

/// ditto
export @fmamath FindRootResult!real findRootImpl(
    real ax,
    real bx,
    real fax,
    real fbx,
    real lowerBound,
    real upperBound,
    uint maxIterations,
    uint steps,
    scope real delegate(real) @safe pure nothrow @nogc f,
    scope bool delegate(real, real) @safe pure nothrow @nogc tolerance, //can be null
) @safe pure nothrow @nogc
{
    pragma(inline, false);
    return findRootImplGen!real(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, steps, f, tolerance);
}

private @fmamath FindRootResult!T findRootImplGen(T)(
    T a,
    T b,
    T fa,
    T fb,
    T lb,
    T ub,
    uint maxIterations,
    uint steps,
    scope const T delegate(T) @safe pure nothrow @nogc f,
    scope const bool delegate(T, T) @safe pure nothrow @nogc tolerance, //can be null
) @safe pure nothrow @nogc
    if (isFloatingPoint!T)
{
    version(LDC) pragma(inline, true);
    // Author: Don Clugston. This code is (heavily) modified from TOMS748
    // (www.netlib.org).  The changes to improve the worst-cast performance are
    // entirely original.
    
    // Author: Ilya Yaroshenko (Bounds extension logic,
    // API improvements, infinity and huge numbers handing, compiled code size reduction)

    T d;  // [a .. b] is our current bracket. d is the third best guess.
    T fd; // Value of f at d.
    bool done = false; // Has a root been found?
    uint iterations;

    static void swap(ref T a, ref T b)
    {
        T t = a; a = b; b = t;
    }

    bool exit()
    {
        pragma(inline, false);
        return done
            || iterations >= maxIterations
            || b == nextUp(a)
            || tolerance !is null && tolerance(a, b);
    }

    // Test the function at point c; update brackets accordingly
    void bracket(T c)
    {
        pragma(inline, false);
        T fc = f(c);
        iterations++;
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
        if (a - b == a && b != 0
         || b - a == b && a != 0)
        {
            // Catastrophic cancellation
            return ieeeMean(a, b);
        }
        // avoid overflow
        T m = fa - fb;
        T wa = fa / m;
        T wb = fb / m;
        T c = b * wa - a * wb;
        if (c == a || c == b || c != c || c.fabs == T.infinity)
            c = a.half + b.half;
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
        const T a1 = (fb - fa) / (b - a);
        const T a2 = ((fd - fb) / (d - b) - a1) / (d - a);

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
    bool left;

    // Allow a and b to be provided in reverse order
    if (a > b)
    {
        swap(a, b);
        swap(fa, fb);
    }

    if (a != a || b != b)
    {
        done = true;
        goto whileloop;
    }

    if (lb != lb)
    {
        lb = a;
    }

    if (ub != ub)
    {
        ub = b;
    }

    if (lb > ub)
    {
        swap(lb, ub);
        left = true;
    }

    if (lb == -T.infinity)
    {
        lb = -T.max;
    }

    if (ub == +T.infinity)
    {
        ub = +T.max;
    }

    if (!(lb <= a))
    {
        a = lb;
        fa = T.nan;
    }

    if (!(b <= ub))
    {
        a = lb;
        fa = T.nan;
    }

    if (fa != fa)
    {
        fa = f(a);
        iterations++;
    }

    // On the first iteration we take a secant step:
    if (fa == 0 || fa != fa)
    {
        done = true;
        b = a;
        fb = fa;
        goto whileloop;
    }

    if (fb != fb)
    {
        if (a == b)
        {
            fb = fa;
        }
        else
        {
            fb = f(b);
            iterations++;
        }
    }

    if (fb == 0 || fb != fb)
    {
        done = true;
        a = b;
        fa = fb;
        goto whileloop;
    }

    if (fa.fabs < fb.fabs)
    {
        left = true;
    }
    else
    if (fa.fabs > fb.fabs)
    {
        left = false;
    }

    // extend inner boundaries
    if (fa.signbit == fb.signbit)
    {
        T lx = a;
        T ux = b;
        T ly = fa;
        T uy = fb;
        const sb = fa.signbit;

        import mir.ndslice.topology: linspace;

        typeof(linspace!T([2], [lx, lb])) lgrid, ugrid;
        if (steps)
        {
            lgrid = linspace!T([steps + 1], [lx, lb]);
            lgrid.popFront;
            ugrid = linspace!T([steps + 1], [ux, ub]);
            ugrid.popFront;
        }

        for(T mx;;)
        {
            bool lw = lb < lx;
            bool uw = ux < ub;

            if (!lw && !uw || iterations >= maxIterations)
            {
                done = true;
                goto whileloop;
            }

            if (lw && (!uw || left))
            {
                if (lgrid.empty)
                {
                    mx = ieeeMean(lb, lx);
                    if (mx == lx)
                        mx = lb;
                }
                else
                {
                    mx = lgrid.front;
                    lgrid.popFront;
                    if (mx == lx)
                        continue;
                }
                T my = f(mx);
                iterations++;
                if (my == 0)
                {
                    a = b = mx;
                    fa = fb = my;
                    done = true;
                    goto whileloop;
                }
                if (mx != mx)
                {
                    lb = mx;
                    continue;
                }
                if (my.signbit == sb)
                {
                    lx = mx;
                    ly = my;
                    if (lgrid.empty)
                    {
                        left = ly.fabs < uy.fabs;
                    }
                    continue;
                }
                a = mx;
                fa = my;
                b = lx;
                fb = ly;
                break;
            }
            else
            {
                if (ugrid.empty)
                {
                    mx = ieeeMean(ub, ux);
                    if (mx == ux)
                        mx = ub;
                }
                else
                {
                    mx = ugrid.front;
                    ugrid.popFront;
                    if (mx == ux)
                        continue;
                }
                T my = f(mx);
                iterations++;
                if (my == 0)
                {
                    a = b = mx;
                    fa = fb = my;
                    done = true;
                    goto whileloop;
                }
                if (mx != mx)
                {
                    ub = mx;
                    continue;
                }
                if (my.signbit == sb)
                {
                    ux = mx;
                    uy = my;
                    if (ugrid.empty)
                    {
                        left = !(ly.fabs > uy.fabs);
                    }
                    continue;
                }
                b = mx;
                fb = my;
                a = ux;
                fa = uy;
                break;
            }
        }
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
            if ((a - b) == a || (b - a) == b)
            {
                c = ieeeMean(a, b);
            }
            else
            {
                c = a.half + b.half;
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

        if ((a == 0
          || b == 0
          || fabs(a) >= 0.5f * fabs(b)
          && fabs(b) >= 0.5f * fabs(a))
          && b - a < 0.25f * (b0 - a0))
        {
            baditer = 1;
            continue;
        }

        // DAC: If this happens on consecutive iterations, we probably have a
        // pathological function. Perform a number of bisections equal to the
        // total number of consecutive bad iterations.

        if (b - a < 0.25f * (b0 - a0))
            baditer = 1;
        foreach (int QQ; 0 .. baditer)
        {
            e = d;
            fe = fd;
            bracket(ieeeMean(a, b));
        }
        ++baditer;
    }
    return typeof(return)(a, b, fa, fb, iterations);
}

version(mir_test) @safe unittest
{
    import mir.math.constant;

    int numProblems = 0;
    int numCalls;

    void testFindRoot(real delegate(real) @nogc @safe nothrow pure f , real x1, real x2, int line = __LINE__) //@nogc @safe nothrow pure
    {
        //numCalls=0;
        //++numProblems;
        assert(x1 == x1 && x2 == x2);
        auto result = findRoot!f(x1, x2).validate;

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
        if (x<-float.max)
            x = -float.max;
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
    // Alefeld paper states that pow(x, n) is a very poor case, where bisection
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
            q+=(2*i-5.0)*(2*i-5.0) / ((x-i*i)*(x-i*i)*(x-i*i));
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
        return (n*x-1) / ((n-1)*x);
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
    Throws: `Exception` if $(LREF FindRootResult.status) isn't $(LREF mir_find_root_status.success).
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

extern(C++) nothrow:

    /++
    Returns: $(LREF mir_find_root_status)
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
        if (!(m.fabs < T.infinity)) // fix infinity loop. Issue can be reproduced in R.
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
//@nogc
version(mir_test) @safe unittest
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
    import mir.math.common: approxEqual, log, fabs;
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

/++
Calculate the derivative of a function.
This function uses Ridders' method of extrapolating the results
of finite difference formulas for consecutively smaller step sizes,
with an improved stopping criterion described in the Numerical Recipes
books by Press et al.

This method gives a much higher degree of accuracy in the answer
compared to a single finite difference calculation, but requires
more function evaluations; typically 6 to 12. The maximum number
of function evaluations is $(D 24).

Params:
    f = The function of which to take the derivative.
    x = The point at which to take the derivative.
    h = A "characteristic scale" over which the function changes.
    factor = Stepsize is decreased by factor at each iteration.
    safe = Return when error is SAFE worse than the best so far.

References:
$(UL
    $(LI
        C. J. F. Ridders,
        $(I Accurate computation of F'(x) and F'(x)F''(x)).
        Advances in Engineering Software, vol. 4 (1982), issue 2, p. 75.)
    $(LI
        W. H. Press, S. A. Teukolsky, W. T. Vetterling, and B. P. Flannery,
        $(I Numerical Recipes in C++) (2nd ed.).
        Cambridge University Press, 2003.)
)
+/
@fmamath
DiffResult!T diff(alias f, T)(const T x, const T h, const T factor = T(2).sqrt, const T safe = 2)
{
    if (false) // break attributes
        T y = f(T(1));
    scope funInst = delegate(T x) {
        return T(f(x));
    };
    scope fun = funInst.trustedAllAttr;
    return diffImpl(fun, x, h, factor, safe);
}

///ditto
DiffResult!T diffImpl(T)
    (scope const T delegate(T) @safe pure nothrow @nogc f, const T x, const T h, const T factor = T(2).sqrt, const T safe = 2)
    @trusted pure nothrow @nogc
in {
    assert(h < T.max);
    assert(h > T.min_normal);
}
do {
    // Set up Romberg tableau.
    import mir.ndslice.slice: sliced;
    pragma(inline, false);

    enum tableauSize = 16;
    T[tableauSize ^^ 2] workspace = void;
    auto tab = workspace[].sliced(tableauSize, tableauSize);

    // From the NR book: Stop when the difference between consecutive
    // approximations is bigger than SAFE*error, where error is an
    // estimate of the absolute error in the current (best) approximation.

    // First approximation: A_0
    T result = void;
    T error = T.max;
    T hh = h;

    tab[0,0] = (f(x + h) - f(x - h))  / (2 * h);
    foreach (n; 1 .. tableauSize)
    {
        // Decrease h.
        hh /= factor;

        // Compute A_n
        tab[0, n] = (f(x + hh) - f(x - hh)) / (2 * hh);

        T facm = 1;
        foreach (m; 1 .. n + 1)
        {
            facm *= factor ^^ 2;

            // Compute B_(n-1), C_(n-2), ...
            T upLeft  = tab[m - 1, n - 1];
            T up      = tab[m - 1, n];
            T current = (facm * up - upLeft) / (facm - 1);
            tab[m, n] = current;

            // Calculate and check error.
            T currentError = fmax(fabs(current - upLeft), fabs(current - up));
            if (currentError <= error)
            {
                result = current;
                error = currentError;
            }
        }

        if (fabs(tab[n, n] - tab[n - 1, n - 1]) >= safe * error)
            break;
    }

    return typeof(return)(result, error);
}

///
unittest
{
    import mir.math.common;

    auto f(double x) { return exp(x) / (sin(x) - x ^^ 2); }
    auto d(double x) { return -(exp(x) * ((x - 2) * x - sin(x) + cos(x)))/(x^^2 - sin(x))^^2; }
    auto r = diff!f(1.0, 0.01);
    assert (approxEqual(r.value, d(1)));
}

/++
+/
struct DiffResult(T)
    if (__traits(isFloating, T))
{
    ///
    T value = 0;
    ///
    T error = 0;
}

/++
Integrates function on the interval `[a, b]` using adaptive Gauss-Lobatto algorithm.

References:
    W. Gander and W. Gautschi. Adaptive Quadrature — Revisited

Params:
    f = function to integrate. `f` should be valid on interval `[a, b]` including the bounds.
    a = finite left interval bound
    b = finite right interval bound
    tolerance = (optional) relative tolerance should be greater or equal to `T.epsilon`

Returns:
    Integral value
+/
T integrate(alias f, T)(const T a, const T b, const T tolerance = T.epsilon)
    if (__traits(isFloating, T))
{
    if (false) // break attributes
        T y = f(T(1));
    scope funInst = delegate(T x) {
        return T(f(x));
    };
    scope fun = funInst.trustedAllAttr;
    return integrateImpl(fun, a, b, tolerance);
}

/// ditto
@optmath
T integrateImpl(T)(
    scope const T delegate(T) @safe pure nothrow @nogc f,
    const T a,
    const T b,
    const T tolerance = T.epsilon,
) @safe pure nothrow @nogc
    if (__traits(isFloating, T))
in {
    assert(-T.infinity < a);
    assert(b < +T.infinity);
    assert(a < b);
    assert(tolerance >= T.epsilon);
}
do {
    pragma(inline, false);
    enum T alpha = 0.816496580927726032732428024901963797322;
    enum T beta = 0.447213595499957939281834733746255247088;
    enum T x1 = 0.94288241569947971905635175843185720232;
    enum T x2 = 0.64185334234978130978123554132903188394;
    enum T x3 = 0.23638319966214988028222377349205292599;
    enum T A = 0.015827191973480183087169986733305510591;
    enum T B = 0.094273840218850045531282505077108171960;
    enum T C = 0.19507198733658539625363597980210298680;
    enum T D = 0.18882157396018245442000533937297167125;
    enum T E = 0.19977340522685852679206802206648840246;
    enum T F = 0.22492646533333952701601768799639508076;
    enum T G = 0.24261107190140773379964095790325635233;
    enum T A1 = 77 / 1470.0L;
    enum T B1 = 432 / 1470.0L;
    enum T C1 = 625 / 1470.0L;
    enum T D1 = 672 / 1470.0L;
    enum T A2 = 1 / 6.0L;
    enum T B2 = 5 / 6.0L;

    T m = (a + b) * 0.5f;
    // This fix is not part of the original algorithm
    if (!(m.fabs < T.infinity))
    {
        m = a.half + b.half;
    }
    T h = (b - a) * 0.5f;
    // This fix is not part of the original algorithm
    if (!(h.fabs < T.infinity))
    {
        h = b.half - a.half;
    }
    T fa = f(a);
    T fb = f(b);
    T[7] y = [
        fa + fb,
        f(m - x1 * h) + f(m + x1 * h),
        f(m - alpha * h) + f(m + alpha * h),
        f(m - x2 * h) + f(m + x2 * h),
        f(m - beta * h) + f(m + beta * h),
        f(m - x3 * h) + f(m + x3 * h),
        f(m),
    ];
    T i2 = h * (
        + A2 * y[0]
        + B2 * y[4]
    );
    T i1 = h * (
        + A1 * y[0]
        + B1 * y[2]
        + C1 * y[4]
        + D1 * y[6]
    );
    T si = h * (
        + A * y[0]
        + B * y[1]
        + C * y[2]
        + D * y[3]
        + E * y[4]
        + F * y[5]
        + G * y[6]
    );
    T erri1 = fabs(i1 - si);
    T erri2 = fabs(i2 - si);
    T R = erri1 / erri2;
    T tol = tolerance;
    if (tol < T.epsilon)
        tol = T.epsilon;
    if (0 < R && R < 1)
        tol /= R;
    si *= tol / T.epsilon;
    if (si == 0)
        si = b - a;
    
    if (!(si.fabs < T.infinity))
        return T.nan;

    T step(const T a, const T b, const T fa, const T fb)
    {
        T m = (a + b) * 0.5f;
        // This fix is not part of the original algorithm
        if (!(m.fabs < T.infinity))
        {
            m = a.half + b.half;
        }
        T h = (b - a) * 0.5f;
        if (!(h.fabs < T.infinity))
        {
            h = b.half - a.half;
        }
        T[5] x = [
            m - alpha * h,
            m - beta * h,
            m,
            m + beta * h,
            m + alpha * h,
        ];
        T[5] y = [
            f(x[0]),
            f(x[1]),
            f(x[2]),
            f(x[3]),
            f(x[4]),
        ];
        T i2 = h * (
            + A2 * (fa + fb)
            + B2 * (y[1] + y[3])
        );
        T i1 = h * (
            + A1 * (fa + fb)
            + B1 * (y[0] + y[4])
            + C1 * (y[1] + y[3])
            + D1 * y[2]
        );
        if (!(i1.fabs < T.infinity) || (si + (i1 - i2) == si) || !(a < x[0]) || !(x[4] < b))
        {
            return i1;
        }
        return
             +(step(   a, x[0],   fa, y[0])
             + step(x[0], x[1], y[0], y[1]))
             +(step(x[1], x[2], y[1], y[2])
             + step(x[2], x[3], y[2], y[3]))
             +(step(x[3], x[4], y[3], y[4])
             + step(x[4],    b, y[4],   fb));
    }

    return step(a, b, fa, fb);
}

///
unittest
{
    import mir.math.common;
    import mir.math.constant;

    alias cosh = x => 0.5 * (exp(x) + exp(-x));
    enum Pi = double(PI);

    assert(integrate!exp(0.0, 1.0).approxEqual(double(E - 1)));
    assert(integrate!(x => x >= 3)(0.0, 10.0).approxEqual(7.0));
    assert(integrate!sqrt(0.0, 1.0).approxEqual(2.0 / 3));
    assert(integrate!(x => 23.0 / 25 * cosh(x) - cos(x))(-1.0, 1.0).approxEqual(0.479428226688801667));
    assert(integrate!(x => 1 / (x ^^ 4 + x ^^ 2 + 0.9))(-1.0, 1.0).approxEqual(1.5822329637294));
    assert(integrate!(x => sqrt(x ^^ 3))(0.0, 1.0).approxEqual(0.4));
    assert(integrate!(x => x ? 1 / sqrt(x) : 0)(0.0, 1.0).approxEqual(2));
    assert(integrate!(x => 1 / (1 + x ^^ 4))(0.0, 1.0).approxEqual(0.866972987339911));
    assert(integrate!(x => 2 / (2 + sin(10 * Pi * x)))(0.0, 1.0).approxEqual(1.1547005383793));
    assert(integrate!(x => 1 / (1 + x))(0.0, 1.0).approxEqual(0.6931471805599));
    assert(integrate!(x => 1 / (1 + exp(x)))(0.0, 1.0).approxEqual(0.3798854930417));
    assert(integrate!(x => exp(x) - 1 ? x / (exp(x) - 1) : 0)(0.0, 1.0).approxEqual(0.777504634112248));
    assert(integrate!(x => sin(100 * Pi * x) / (Pi * x))(0.1, 1.0).approxEqual(0.0090986375391668));
    assert(integrate!(x => sqrt(50.0) * exp(-50 * Pi * x ^^ 2))(0.0, 10.0).approxEqual(0.5));
    assert(integrate!(x => 25 * exp(-25 * x))(0.0, 10.0).approxEqual(1.0));
    assert(integrate!(x => 50 / Pi * (2500 * x ^^ 2 + 1))(0.0, 10.0).approxEqual(1.3263071079268e+7));
    assert(integrate!(x => 50 * (sin(50 * Pi * x) / (50 * Pi * x)) ^^ 2)(0.01, 1.0).approxEqual(0.11213930374164));
    assert(integrate!(x => cos(cos(x) + 3 * sin(x) + 2 * cos(2 * x) + 3 * sin(2 * x) + 3 * cos(3 * x)))(0.0, Pi).approxEqual(0.83867634269443));
    assert(integrate!(x => x > 1e-15 ? log(x) : 0)(0.0, 1.0).approxEqual(-1));
    assert(integrate!(x => 1 / (x ^^ 2 + 1.005))(-1.0, 1.0).approxEqual(1.5643964440690));
    assert(integrate!(x => 1 / cosh(20 * (x - 0.2)) + 1 / cosh(400 * (x - 0.04)) + 1 / cosh(8000 * (x - 0.008)))(0.0, 1.0).approxEqual(0.16349495585710));
    assert(integrate!(x => 4 * Pi ^^ 2 * x * sin(20 * Pi * x) * cos(2 * Pi * x))(0.0, 1.0).approxEqual(-0.6346651825434));
    assert(integrate!(x => 1 / (1 + (230 * x - 30) ^^ 2))(0.0, 1.0).approxEqual(0.013492485649468));
}
