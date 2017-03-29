/++
Common floating point math functions.

This module has generic LLVM-oriented API compatable with all D compilers.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
+/
module mir.math.common;

public import mir.internal.utility: fastmath;

version(D_Ddoc)
{
    ///
    T sqrt(T)(in T x);
    ///
    T sin(T)(in T x);
    ///
    T cos(T)(in T x);
    ///
    T pow(T)(in T x, in T power);
    ///
    T powi(T)(in T x, int power);
    ///
    T exp(T)(in T x);
    ///
    T log(T)(in T x);
    ///
    T fabs(T)(in T x);
    ///
    T floor(T)(in T x);
    ///
    T exp2(T)(in T x);
    ///
    T log10(T)(in T x);
    ///
    T log2(T)(in T x);
    ///
    T ceil(T)(in T x);
    ///
    T trunc(T)(in T x);
    ///
    T rint(T)(in T x);
    ///
    T nearbyint(T)(in T x);
    ///
    T copysign(T)(in T mag, in T sgn);
    ///
    T round(T)(in T x);
    ///
    T fmuladd(T)(in T a, in T b, in T c);
    ///
    T fmin(T)(in T x, in T y);
    ///
    T fmax(T)(in T x, in T y);
}
else
version(LDC)
{
    import ldc.intrinsics;
    alias sqrt = llvm_sqrt;
    alias sin = llvm_sin;
    alias cos = llvm_cos;
    alias pow = llvm_pow;
    alias powi = llvm_powi;
    alias exp = llvm_exp;
    alias log = llvm_log;
    alias fabs = llvm_fabs;
    alias floor = llvm_floor;
    alias exp2 = llvm_exp2;
    alias log10 = llvm_log10;
    alias log2 = llvm_log2;
    alias ceil = llvm_ceil;
    alias trunc = llvm_trunc;
    alias rint = llvm_rint;
    alias nearbyint = llvm_nearbyint;
    alias copysign = llvm_copysign;
    alias round = llvm_round;
    alias fmuladd = llvm_fmuladd;
    alias fmin = llvm_minnum;
    alias fmax = llvm_maxnum;
}
else
{
    static import std.math;
    import std.traits: isFloatingPoint;
    T sqrt(T)(in T x) if (isFloatingPoint!T) { return std.math.sqrt(x); }
    T sin(T)(in T x) if (isFloatingPoint!T) { return std.math.sin(x); }
    T cos(T)(in T x) if (isFloatingPoint!T) { return std.math.cos(x); }
    T pow(T)(in T x, in T power) if (isFloatingPoint!T) { return std.math.pow(x, power); }
    T powi(T)(in T x, int power) if (isFloatingPoint!T) { return std.math.pow(x, power); }
    T exp(T)(in T x) if (isFloatingPoint!T) { return std.math.exp(x); }
    T log(T)(in T x) if (isFloatingPoint!T) { return std.math.log(x); }
    T fabs(T)(in T x) if (isFloatingPoint!T) { return std.math.fabs(x); }
    T floor(T)(in T x) if (isFloatingPoint!T) { return std.math.floor(x); }
    T exp2(T)(in T x) if (isFloatingPoint!T) { return std.math.exp2(x); }
    T log10(T)(in T x) if (isFloatingPoint!T) { return std.math.log10(x); }
    T log2(T)(in T x) if (isFloatingPoint!T) { return std.math.log2(x); }
    T ceil(T)(in T x) if (isFloatingPoint!T) { return std.math.ceil(x); }
    T trunc(T)(in T x) if (isFloatingPoint!T) { return std.math.trunc(x); }
    T rint(T)(in T x) if (isFloatingPoint!T) { return std.math.rint(x); }
    T nearbyint(T)(in T x) if (isFloatingPoint!T) { return std.math.nearbyint(x); }
    T copysign(T)(in T mag, in T sgn) if (isFloatingPoint!T) { return std.math.copysign(mag, sgn); }
    T round(T)(in T x) if (isFloatingPoint!T) { return std.math.round(x); }
    T fmuladd(T)(in T a, in T b, in T c) if (isFloatingPoint!T) { return a * b + c; }
    unittest { assert(fmuladd!double(2, 3, 4) == 2 * 3 + 4); }
    T fmin(T)(in T x, in T y) if (isFloatingPoint!T) { return std.math.fmin(x, y); }
    T fmax(T)(in T x, in T y) if (isFloatingPoint!T) { return std.math.fmax(x, y); }
}
