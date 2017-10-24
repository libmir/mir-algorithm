/++
Common floating point math functions.

This module has generic LLVM-oriented API compatable with all D compilers.

License:   $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Copyright: Copyright © 2016-, Ilya Yaroshenko
Authors:   Ilya Yaroshenko
+/
module mir.math.common;

version(LDC)
{
    static import ldc.attributes;

    /++
    Functions attribute, an alias for `AliasSeq!(llvmFastMathFlag("contract"));`.
        
    $(UL
    $(LI 1. Allow floating-point contraction (e.g. fusing a multiply followed by an addition into a fused multiply-and-add). )
    )

    Note: Can be used with all compilers.
    +/
    alias fmamath = AliasSeq!(ldc.attributes.llvmFastMathFlag("contract"));

    /++
    Functions attribute, an alias for `AliasSeq!(llvmAttr("unsafe-fp-math", "false"), llvmFastMathFlag("fast"))`.
    
    It is similar to $(LREF fastmath), but does not allow unsafe-fp-math.
    This flag does NOT force LDC to use the reciprocal of an argument rather than perform division.

    This flag is defualt for string lambdas.

    Note: Can be used with all compilers.
    +/
    alias optmath = AliasSeq!(ldc.attributes.llvmFastMathFlag("fast"));

    /++
    Functions attribute, an alias for `ldc.attributes.fastmath = AliasSeq!(llvmAttr("unsafe-fp-math", "true"), llvmFastMathFlag("fast"))` .
    
    $(UL

    $(LI 1. Enable optimizations that make unsafe assumptions about IEEE math (e.g. that addition is associative) or may not work for all input ranges.
    These optimizations allow the code generator to make use of some instructions which would otherwise not be usable (such as fsin on X86). )

    $(LI 2. Allow optimizations to assume the arguments and result are not NaN.
        Such optimizations are required to retain defined behavior over NaNs,
        but the value of the result is undefined. )

    $(LI 3. Allow optimizations to assume the arguments and result are not +$(BACKTICK)-inf.
        Such optimizations are required to retain defined behavior over +$(BACKTICK)-Inf,
        but the value of the result is undefined. )

    $(LI 4. Allow optimizations to treat the sign of a zero argument or result as insignificant. )

    $(LI 5. Allow optimizations to use the reciprocal of an argument rather than perform division. )

    $(LI 6. Allow floating-point contraction (e.g. fusing a multiply followed by an addition into a fused multiply-and-add). )

    $(LI 7. Allow algebraically equivalent transformations that may dramatically change results in floating point (e.g. reassociate). )
    )
    
    Note: Can be used with all compilers.
    +/
    alias fastmath = ldc.attributes.fastmath;
}
else
{
    enum { fastmath, fusedmath, optmath };
}

version(LDC)
{
    nothrow @nogc pure @safe:

    pragma(LDC_intrinsic, "llvm.sqrt.f#")
    ///
    T sqrt(T)(in T val);

    pragma(LDC_intrinsic, "llvm.sin.f#")
    ///
    T sin(T)(in T val);

    pragma(LDC_intrinsic, "llvm.cos.f#")
    ///
    T cos(T)(in T val);

    pragma(LDC_intrinsic, "llvm.powi.f#")
    ///
    T powi(T)(in T val, int power);

    pragma(LDC_intrinsic, "llvm.pow.f#")
    ///
    T pow(T)(in T val, in T power);

    pragma(LDC_intrinsic, "llvm.exp.f#")
    ///
    T exp(T)(in T val);

    pragma(LDC_intrinsic, "llvm.log.f#")
    ///
    T log(T)(in T val);

    pragma(LDC_intrinsic, "llvm.fma.f#")
    ///
    T fma(T)(T vala, T valb, T valc);

    pragma(LDC_intrinsic, "llvm.fabs.f#")
    ///
    T fabs(T)(in T val);

    pragma(LDC_intrinsic, "llvm.floor.f#")
    ///
    T floor(T)(in T val);

    pragma(LDC_intrinsic, "llvm.exp2.f#")
    ///
    T exp2(T)(in T val);

    pragma(LDC_intrinsic, "llvm.log10.f#")
    ///
    T log10(T)(in T val);

    pragma(LDC_intrinsic, "llvm.log2.f#")
    ///
    T log2(T)(in T val);

    pragma(LDC_intrinsic, "llvm.ceil.f#")
    ///
    T ceil(T)(in T val);

    pragma(LDC_intrinsic, "llvm.trunc.f#")
    ///
    T trunc(T)(in T val);

    pragma(LDC_intrinsic, "llvm.rint.f#")
    ///
    T rint(T)(in T val);

    pragma(LDC_intrinsic, "llvm.nearbyint.f#")
    ///
    T nearbyint(T)(in T val);

    pragma(LDC_intrinsic, "llvm.copysign.f#")
    ///
    T copysign(T)(in T mag, in T sgn);

    pragma(LDC_intrinsic, "llvm.round.f#")
    ///
    T round(T)(in T val);

    pragma(LDC_intrinsic, "llvm.fmuladd.f#")
    ///
    T fmuladd(T)(in T vala, in T valb, in T valc);

    pragma(LDC_intrinsic, "llvm.minnum.f#")
    ///
    T fmin(T)(in T vala, in T valb);

    pragma(LDC_intrinsic, "llvm.maxnum.f#")
    ///
    T fmax(T)(in T vala, in T valb);
}
else
{
    static import std.math;
    import std.traits: isFloatingPoint;
    ///
    T sqrt(T)(in T x) if (isFloatingPoint!T) { return std.math.sqrt(x); }
    ///
    T sin(T)(in T x) if (isFloatingPoint!T) { return std.math.sin(x); }
    ///
    T cos(T)(in T x) if (isFloatingPoint!T) { return std.math.cos(x); }
    ///
    T pow(T)(in T x, in T power) if (isFloatingPoint!T) { return std.math.pow(x, power); }
    ///
    T powi(T)(in T x, int power) if (isFloatingPoint!T) { return std.math.pow(x, power); }
    ///
    T exp(T)(in T x) if (isFloatingPoint!T) { return std.math.exp(x); }
    ///
    T log(T)(in T x) if (isFloatingPoint!T) { return std.math.log(x); }
    ///
    T fabs(T)(in T x) if (isFloatingPoint!T) { return std.math.fabs(x); }
    ///
    T floor(T)(in T x) if (isFloatingPoint!T) { return std.math.floor(x); }
    ///
    T exp2(T)(in T x) if (isFloatingPoint!T) { return std.math.exp2(x); }
    ///
    T log10(T)(in T x) if (isFloatingPoint!T) { return std.math.log10(x); }
    ///
    T log2(T)(in T x) if (isFloatingPoint!T) { return std.math.log2(x); }
    ///
    T ceil(T)(in T x) if (isFloatingPoint!T) { return std.math.ceil(x); }
    ///
    T trunc(T)(in T x) if (isFloatingPoint!T) { return std.math.trunc(x); }
    ///
    T rint(T)(in T x) if (isFloatingPoint!T) { return std.math.rint(x); }
    ///
    T nearbyint(T)(in T x) if (isFloatingPoint!T) { return std.math.nearbyint(x); }
    ///
    T copysign(T)(in T mag, in T sgn) if (isFloatingPoint!T) { return std.math.copysign(mag, sgn); }
    ///
    T round(T)(in T x) if (isFloatingPoint!T) { return std.math.round(x); }
    ///
    T fmuladd(T)(in T a, in T b, in T c) if (isFloatingPoint!T) { return a * b + c; }
    version(mir_test)
    unittest { assert(fmuladd!double(2, 3, 4) == 2 * 3 + 4); }
    ///
    T fmin(T)(in T x, in T y) if (isFloatingPoint!T) { return std.math.fmin(x, y); }
    ///
    T fmax(T)(in T x, in T y) if (isFloatingPoint!T) { return std.math.fmax(x, y); }
}
