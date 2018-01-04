/++
Generic utilities.

$(BOOKTABLE Cheat Sheet,
$(TR $(TH Function Name) $(TH Description))
$(T2 swap, Swaps two values.)
$(T2 min, Minimum value.)
$(T2 max, Maximum value.)
)

Copyright: Andrei Alexandrescu 2008-2016, Ilya Yaroshenko 2016-.
License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: $(HTTP erdani.com, Andrei Alexandrescu) (original std.* modules), Ilya Yaroshenko
Macros:
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
+/
module mir.utility;

import std.traits;

import mir.math.common: optmath;

version(LDC)
pragma(LDC_inline_ir) R inlineIR(string s, R, P...)(P) @safe pure nothrow @nogc;

@optmath:

public import std.algorithm.mutation: swap;

void swapStars(I1, I2)(auto ref I1 i1, auto ref I2 i2)
{
    static if (__traits(compiles, swap(*i1, *i2)))
    {
        swap(*i1, *i2);
    }
    else
    {
        import mir.functional: unref;
        auto e = unref(*i1);
        i1[0] = *i2;
        i2[0] = e;
    }
}

/++
Iterates the passed arguments and returns the minimum value.
Params: args = The values to select the minimum from. At least two arguments
    must be passed, and they must be comparable with `<`.
Returns: The minimum of the passed-in values.
+/
auto min(T...)(T args)
    if (T.length >= 2)
{
    //Get "a"
    static if (T.length <= 2)
        alias a = args[0];
    else
        auto a = min(args[0 .. ($+1)/2]);
    alias T0 = typeof(a);

    //Get "b"
    static if (T.length <= 3)
        alias b = args[$-1];
    else
        auto b = min(args[($+1)/2 .. $]);
    alias T1 = typeof(b);

    static assert (is(typeof(a < b)), "Invalid arguments: Cannot compare types " ~ T0.stringof ~ " and " ~ T1.stringof ~ ".");

    static if ((isFloatingPoint!T0 && isNumeric!T1) || (isFloatingPoint!T1 && isNumeric!T0))
    {
        import mir.math.common: fmin;
        return fmin(a, b);
    }
    else
    {
        static if (isIntegral!T0 && isIntegral!T1)
            static assert(isSigned!T0 == isSigned!T1, 
                "mir.utility.min is not defined for signed + unsigned pairs because of security reasons."
                ~ "Please unify type or use a Phobos analog.");
        //Do the "min" proper with a and b
        return a < b ? a : b;
    }
}

@safe version(mir_test) unittest
{
    int a = 5;
    short b = 6;
    double c = 2;
    auto d = min(a, b);
    static assert(is(typeof(d) == int));
    assert(d == 5);
    auto e = min(a, b, c);
    static assert(is(typeof(e) == double));
    assert(e == 2);
}

/++
`min` is not defined for arguments of mixed signedness because of security reasons.
Please unify type or use a Phobos analog.
+/
version(mir_test) unittest
{
    int a = -10;
    uint b = 10;
    static assert(!is(typeof(min(a, b))));
}


/++
Iterates the passed arguments and returns the minimum value.
Params: args = The values to select the minimum from. At least two arguments
    must be passed, and they must be comparable with `<`.
Returns: The minimum of the passed-in values.
+/
auto max(T...)(T args)
    if (T.length >= 2)
{
    //Get "a"
    static if (T.length <= 2)
        alias a = args[0];
    else
        auto a = max(args[0 .. ($+1)/2]);
    alias T0 = typeof(a);

    //Get "b"
    static if (T.length <= 3)
        alias b = args[$-1];
    else
        auto b = max(args[($+1)/2 .. $]);
    alias T1 = typeof(b);

    static assert (is(typeof(a < b)), "Invalid arguments: Cannot compare types " ~ T0.stringof ~ " and " ~ T1.stringof ~ ".");

    static if ((isFloatingPoint!T0 && isNumeric!T1) || (isFloatingPoint!T1 && isNumeric!T0))
    {
        import mir.math.common: fmax;
        return fmax(a, b);
    }
    else
    {
        static if (isIntegral!T0 && isIntegral!T1)
            static assert(isSigned!T0 == isSigned!T1, 
                "mir.utility.max is not defined for signed + unsigned pairs because of security reasons."
                ~ "Please unify type or use a Phobos analog.");
        //Do the "max" proper with a and b
        return a > b ? a : b;
    }
}

///
@safe version(mir_test) unittest
{
    int a = 5;
    short b = 6;
    double c = 2;
    auto d = max(a, b);
    static assert(is(typeof(d) == int));
    assert(d == 6);
    auto e = min(a, b, c);
    static assert(is(typeof(e) == double));
    assert(e == 2);
}

/++
`max` is not defined for arguments of mixed signedness because of security reasons.
Please unify type or use a Phobos analog.
+/
version(mir_test) unittest
{
    int a = -10;
    uint b = 10;
    static assert(!is(typeof(max(a, b))));
}

/++
Return type for $(LREF extMul);
+/
struct ExtMulResult(I)
    if (isIntegral!I)
{
    /// Lower I.sizeof * 8 bits
    I low;
    /// Higher I.sizeof * 8 bits
    I high;
}

/++
Extended unsigned multiplications.
Performs U x U multiplication and returns $(LREF ExtMulResult)!U that contains extended result.
Params:
    a = unsigned integer
    b = unsigned integer
Returns:
    128bit result if U is ulong or 256bit result if U is ucent.
Optimization:
    Algorithm is optimized for LDC (LLVM IR, any target) and for DMD (X86_64).
+/
ExtMulResult!U extMul(U)(in U a, in U b) @nogc nothrow pure @safe
    if(isUnsigned!U && U.sizeof >= ulong.sizeof)
{
    static if (is(U == ulong))
        alias H = uint;
    else
        alias H = ulong;

    enum hbc = H.sizeof * 8;

    static if (is(U == ulong) && __traits(compiles, ucent.init))
    {
        auto ret = ucent(a) * b;
        return typeof(return)(cast(ulong) ret, cast(ulong)(ret >>> 64));
    }
    else
    {
        if (!__ctfe)
        {
            static if (size_t.sizeof == 4)
            {
                // https://github.com/ldc-developers/ldc/issues/2391
            }
            else
            version(LDC)
            {
                // LLVM IR by n8sh
                pragma(inline, true);
                static if (is(U == ulong))
                {
                    auto r = inlineIR!(`
                    %a = zext i64 %0 to i128
                    %b = zext i64 %1 to i128
                    %m = mul i128 %a, %b
                    %n = lshr i128 %m, 64
                    %h = trunc i128 %n to i64
                    %l = trunc i128 %m to i64
                    %agg1 = insertvalue [2 x i64] undef, i64 %l, 0
                    %agg2 = insertvalue [2 x i64] %agg1, i64 %h, 1
                    ret [2 x i64] %agg2`, ulong[2])(a, b);
                    return ExtMulResult!U(r[0], r[1]);
                }
                else
                static if (false)
                {
                    auto r = inlineIR!(`
                    %a = zext i128 %0 to i256
                    %b = zext i128 %1 to i256
                    %m = mul i256 %a, %b
                    %n = lshr i256 %m, 128
                    %h = trunc i256 %n to i128
                    %l = trunc i256 %m to i128
                    %agg1 = insertvalue [2 x i128] undef, i128 %l, 0
                    %agg2 = insertvalue [2 x i128] %agg1, i128 %h, 1
                    ret [2 x i128] %agg2`, ucent[2])(a, b);
                    return ExtMulResult!U(r[0], r[1]);
                }
            }
            else
            version(D_InlineAsm_X86_64)
            {
                static if (is(U == ulong))
                {
                    version(Windows)
                    {
                        ulong[2] r = extMul_X86_64(a, b);
                        return ExtMulResult!ulong(r[0], r[1]);
                    }
                    else
                    {
                        return extMul_X86_64(a, b);
                    }
                }
            }
        }

        U al = cast(H)a;
        U ah = a >>> hbc;
        U bl = cast(H)b;
        U bh = b >>> hbc;

        U p0 = al * bl;
        U p1 = al * bh;
        U p2 = ah * bl;
        U p3 = ah * bh;

        H cy = cast(H)(((p0 >>> hbc) + cast(H)p1 + cast(H)p2) >>> hbc);
        U lo = p0 + (p1 << hbc) + (p2 << hbc);
        U hi = p3 + (p1 >>> hbc) + (p2 >>> hbc) + cy;

        return typeof(return)(lo, hi);
    }
}

///
unittest
{
    immutable a = 0x93_8d_28_00_0f_50_a5_56;
    immutable b = 0x54_c3_2f_e8_cc_a5_97_10;
    enum c = extMul(a, b);     // Compile time algorithm
    assert(extMul(a, b) == c); // Fast runtime algorithm
    static assert(c.high == 0x30_da_d1_42_95_4a_50_78);
    static assert(c.low == 0x27_9b_4b_b4_9e_fe_0f_60);
}

version(D_InlineAsm_X86_64)
{
    version(Windows)
    private ulong[2] extMul_X86_64()(ulong a, ulong b)
    {
        asm @safe pure nothrow @nogc
        {
            naked;
            mov RAX, RCX;
            mul RDX;
            ret;
        }
    }
    else
    private ExtMulResult!ulong extMul_X86_64()(ulong a, ulong b)   
    {  
        asm @safe pure nothrow @nogc
        {
            naked;
            mov RAX, RDI;
            mul RSI;
            ret;
        }
    }
}

version(LDC) {} else version(D_InlineAsm_X86_64)
@nogc nothrow pure @safe unittest
{
    immutable a = 0x93_8d_28_00_0f_50_a5_56;
    immutable b = 0x54_c3_2f_e8_cc_a5_97_10;

    version(Windows)
    {
        immutable ulong[2] r = extMul_X86_64(a, b);
        immutable ExtMulResult!ulong c = ExtMulResult!ulong(r[0], r[1]);
    }
    else
    {
        immutable ExtMulResult!ulong c = extMul_X86_64(a, b);       
    }

    assert(c.high == 0x30_da_d1_42_95_4a_50_78);
    assert(c.low == 0x27_9b_4b_b4_9e_fe_0f_60);
}
