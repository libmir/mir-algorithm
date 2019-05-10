/++
This module contans extern C wrappers for $(MREF mir, numeric).
+/
module mir.c.numeric;

import mir.numeric: findRootImpl, mir_find_root_result;

private alias CFunction(T) = extern(C++) T function(scope const(void)* ctx, T) @safe pure nothrow @nogc;

private alias CTolerance(T) = extern(C++) bool function(scope const(void)* ctx, T, T) @safe pure nothrow @nogc;

export extern(C++) @safe pure nothrow @nogc:

/// Wrapper for $(REF_ALTTEXT $(TT findRoot), findRoot, mir, numeric)$(NBSP)
mir_find_root_result!float mir_find_root(
    float ax,
    float bx,
    float fax,
    float fbx,
    float lowerBound,
    float upperBound,
    uint maxIterations,
    scope CFunction!float f,
    scope const(void)* f_ctx,
    scope CTolerance!float tolerance,
    scope const(void)* tolerance_ctx,
)
{
    pragma(inline, false);
    if (tolerance is null)
        return findRootImpl(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, (float x) => f(f_ctx, x), null);
    else
        return findRootImpl(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, (float x) => f(f_ctx, x), (float a, float b) => tolerance(tolerance_ctx, a, b) != 0);
}

/// ditto
mir_find_root_result!double mir_find_root(
    double ax,
    double bx,
    double fax,
    double fbx,
    double lowerBound,
    double upperBound,
    uint maxIterations,
    scope CFunction!double f,
    scope const(void)* f_ctx,
    scope CTolerance!double tolerance,
    scope const(void)* tolerance_ctx,
)
{
    pragma(inline, false);
    if (tolerance is null)
        return findRootImpl(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, (double x) => f(f_ctx, x), null);
    else
        return findRootImpl(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, (double x) => f(f_ctx, x), (double a, double b) => tolerance(tolerance_ctx, a, b) != 0);
}

/// ditto
mir_find_root_result!real mir_find_root(
    real ax,
    real bx,
    real fax,
    real fbx,
    real lowerBound,
    real upperBound,
    uint maxIterations,
    scope CFunction!real f,
    scope const(void)* f_ctx,
    scope CTolerance!real tolerance,
    scope const(void)* tolerance_ctx,
)
{
    pragma(inline, false);
    if (tolerance is null)
        return findRootImpl(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, (real x) => f(f_ctx, x), null);
    else
        return findRootImpl(ax, bx, fax, fbx, lowerBound, upperBound, maxIterations, (real x) => f(f_ctx, x), (real a, real b) => tolerance(tolerance_ctx, a, b) != 0);
}
