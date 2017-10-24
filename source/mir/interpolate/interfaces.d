module mir.interpolaiton.interfaces;

import std.traits;

// Rectilinear grid - default
// Regular grid - linspace
// Cartesian grid - iota

version(none):

template NdInterpolation(size_t N)
{
    interface NdInterpolation(F)
    {

    }
}

template NdInterpolationRectilinear(size_t N)
{
    interface NdInterpolationRectilinear(F)
    {
        
    }
}

interface Interpolation(T)
{
    import mir.ndslice.slice;

@system pure nothrow @nogc:

    ///
    T opCall(size_t interval, T x);
    ///
    T[2] withDerivative(size_t interval, T x);
    ///
    T[3] withTwoDerivatives(size_t interval, T x);

@safe:

    ///
    size_t interval(T x);

    ///
    auto opIndex(SliceKind kind, size_t[] packs, Iterator)(Slice!(kind, packs, Iterator) slice)
    {
        import mir.ndslice.topology: indexed;
        return this.indexed(slice);
    }

    ///
    auto opIndex()(T x)
    {
        return opCall(x);
    }

    ///
    T opCall(T x);
    ///
    T[2] withDerivative(T x);
    ///
    T[3] withTwoDerivatives(T x);

    ///
    ContiguousVector!(const(T)) points() @property;
    ///
    ContiguousVector!(const(T)) values() @property;
    ///
    ContiguousVector!(const(T)) slopes() @property;
}


///
interface InterpolationFabric(T)
{
    import mir.ndslice.slice;

@safe pure nothrow:
    Interpolation!T createInterpolation(ContiguousVector!(const(T)) points, ContiguousVector!(const(T)) values);
}

unittest
{
    alias S = Interpolation!double;
}

final class InterpolationWrapper(Implementation, T = Unqual!(ForeachType!(typeof(Implementation.init.values)))) : Interpolation!T
{
    import mir.ndslice.slice;

    private Implementation _implementation;

    ///
    this(Implementation implementation)
    {
        _implementation = implementation;
    }

override:

    T opCall(size_t interval, T x) { return _implementation(interval, x); };
    T[2] withDerivative(size_t interval, T x) { return _implementation.withDerivative(interval, x); };
    T[3] withTwoDerivatives(size_t interval, T x) { return _implementation.withTwoDerivatives(interval, x); };

    size_t interval(T x) { return _implementation.interval(x); };

    T opCall(T x) { return _implementation(x); };
    T[2] withDerivative(T x) { return _implementation.withDerivative(x); };
    T[3] withTwoDerivatives(T x) { return _implementation.withTwoDerivatives(x); };

    ContiguousVector!(const(T)) points() @property { return _implementation.points; }
    ContiguousVector!(const(T)) values() @property { return _implementation.values; }
    
    ContiguousVector!(const(T)) slopes() @property {
        static if (__traits(hasMember, _implementation, "slopes"))
            return _implementation.slopes;
        else
            return typeof(return).init;
    }
}

final class ZeroSplineFabric(T) : InterpolationFabric!T
{
    import mir.ndslice.slice;
    import mir.interpolate.constant;

    ///
    alias Implementation = ZeroSpline!(false, const(T)*);

    ///
    override InterpolationWrapper!Implementation createInterpolation(ContiguousVector!(const(T)) points, ContiguousVector!(const(T)) values)
    {
        return new InterpolationWrapper!Implementation(zeroSpline(points, values));
    }
}

final class LinearSplineFabric(T) : InterpolationFabric!T
{
    import mir.ndslice.slice;
    import mir.interpolate.linear;

    ///
    alias Implementation = LinearSpline!(false, const(T)*);

    ///
    override InterpolationWrapper!Implementation createInterpolation(ContiguousVector!(const(T)) points, ContiguousVector!(const(T)) values)
    {
        return new InterpolationWrapper!Implementation(linearSpline(points, values));
    }
}

final class CubicSplineFabric(T) : InterpolationFabric!T
{
    import mir.ndslice.slice;
    import mir.interpolate.cubic;

    ///
    alias Implementation = CubicSpline!(false, const(T)*);

    ///
    override InterpolationWrapper!Implementation createInterpolation(ContiguousVector!(const(T)) points, ContiguousVector!(const(T)) values)
    {
        return new typeof(return)(cubicSpline(points, values));
    }
}

///
version(mir_test)
@safe unittest
{
    import mir.ndslice;
    import std.math: approxEqual;

    auto x = [0, 1, 2, 3, 5.00274, 7.00274, 10.0055, 20.0137, 30.0192];
    auto y = [0.0011, 0.0011, 0.0030, 0.0064, 0.0144, 0.0207, 0.0261, 0.0329, 0.0356,];
    auto xs = [1, 2, 3, 4.00274, 5.00274, 6.00274, 7.00274, 8.00548, 9.00548, 10.0055, 11.0055, 12.0082, 13.0082, 14.0082, 15.0082, 16.011, 17.011, 18.011, 19.011, 20.0137, 21.0137, 22.0137, 23.0137, 24.0164, 25.0164, 26.0164, 27.0164, 28.0192, 29.0192, 30.0192].sliced;

    auto interpolation = new LinearSplineFabric!double().createInterpolation(x.sliced, y.sliced);

    auto data = [0.0011, 0.0030, 0.0064, 0.0104, 0.0144, 0.0176, 0.0207, 0.0225, 0.0243, 0.0261, 0.0268, 0.0274, 0.0281, 0.0288, 0.0295, 0.0302, 0.0309, 0.0316, 0.0322, 0.0329, 0.0332, 0.0335, 0.0337, 0.0340, 0.0342, 0.0345, 0.0348, 0.0350, 0.0353, 0.0356];

    assert(approxEqual(interpolation[xs], data, 1e-4, 1e-4));
}

alias S = ZeroSplineFabric!double;
alias D = LinearSplineFabric!double;
alias C = CubicSplineFabric!double;
