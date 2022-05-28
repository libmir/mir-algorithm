/** Fundamental operations for arbitrary-precision arithmetic
 *
 * These functions are for internal use only.
 */
/*          Copyright Don Clugston 2008 - 2010.
 * Distributed under the Boost Software License, Version 1.0.
 *    (See accompanying file LICENSE_1_0.txt or copy at
 *          http://www.boost.org/LICENSE_1_0.txt)
 */
/* References:
   "Modern Computer Arithmetic" (MCA) is the primary reference for all
    algorithms used in this library.
  - R.P. Brent and P. Zimmermann, "Modern Computer Arithmetic",
    Version 0.5.9, (Oct 2010).
  - C. Burkinel and J. Ziegler, "Fast Recursive Division", MPI-I-98-1-022,
    Max-Planck Institute fuer Informatik, (Oct 1998).
  - G. Hanrot, M. Quercia, and P. Zimmermann, "The Middle Product Algorithm, I.",
    INRIA 4664, (Dec 2002).
  - M. Bodrato and A. Zanoni, "What about Toom-Cook Matrices Optimality?",
    http://bodrato.it/papers (2006).
  - A. Fog, "Optimizing subroutines in assembly language",
    www.agner.org/optimize (2008).
  - A. Fog, "The microarchitecture of Intel and AMD CPU's",
    www.agner.org/optimize (2008).
  - A. Fog, "Instruction tables: Lists of instruction latencies, throughputs
    and micro-operation breakdowns for Intel and AMD CPU's.", www.agner.org/optimize (2008).
Idioms:
  Many functions in this module use
  'func(Tulong)(Tulong x) if (is(Tulong == ulong))' rather than 'func(ulong x)'
  in order to disable implicit conversion.
*/
module mir.bignum.phobos_kernel;

version (D_InlineAsm_X86)
{
    static import std.internal.math.biguintx86;
}
version (DMD)
{
    version (D_InlineAsm_X86)
        version = HaveAsmVersion;
}

version (LDC)
{
    version (D_InlineAsm_X86)
        version = HaveAsmVersion;

    version (ARM)
    {
        version (ARM_Thumb) {}
        else
        {
            static import std.internal.math.biguintarm;
            version = LDC_ARM_asm;
            version = HaveAsmVersion;
        }
    }
}
static import std.internal.math.biguintnoasm;

import std.internal.math.biguintnoasm : BigDigit, KARATSUBALIMIT,
    KARATSUBASQUARELIMIT;

package:

// dipatchers to the right low-level primitives. Added to allow BigInt CTFE for
// 32 bit systems (https://issues.dlang.org/show_bug.cgi?id=14767) although it's
// used by the other architectures too.
// See comments below in case it has to be refactored.
version (HaveAsmVersion)
uint multibyteAddSub(char op)(uint[] dest, const(uint)[] src1, const (uint)[] src2, uint carry)
{
    // must be checked before, otherwise D_InlineAsm_X86 is true.
    if (__ctfe)
        return std.internal.math.biguintnoasm.multibyteAddSub!op(dest, src1, src2, carry);
    // Runtime.
    else version (D_InlineAsm_X86)
        return std.internal.math.biguintx86.multibyteAddSub!op(dest, src1, src2, carry);
    else version (LDC_ARM_asm)
        return std.internal.math.biguintarm.multibyteAddSub!op(dest, src1, src2, carry);
    // Runtime if no asm available.
    else
        return std.internal.math.biguintnoasm.multibyteAddSub!op(dest, src1, src2, carry);
}
// Any other architecture
else alias multibyteAddSub = std.internal.math.biguintnoasm.multibyteAddSub;

version (HaveAsmVersion)
uint multibyteIncrementAssign(char op)(uint[] dest, uint carry)
{
    if (__ctfe)
        return std.internal.math.biguintnoasm.multibyteIncrementAssign!op(dest, carry);
    else version (D_InlineAsm_X86)
        return std.internal.math.biguintx86.multibyteIncrementAssign!op(dest, carry);
    else version (LDC_ARM_asm)
        return std.internal.math.biguintarm.multibyteIncrementAssign!op(dest, carry);
    else
        return std.internal.math.biguintnoasm.multibyteIncrementAssign!op(dest, carry);
}
else alias multibyteIncrementAssign = std.internal.math.biguintnoasm.multibyteIncrementAssign;

version (HaveAsmVersion)
uint multibyteShl()(uint[] dest, const(uint)[] src, uint numbits)
{
    if (__ctfe)
        return std.internal.math.biguintnoasm.multibyteShl(dest, src, numbits);
    else version (D_InlineAsm_X86)
        return std.internal.math.biguintx86.multibyteShl(dest, src, numbits);
    else version (LDC_ARM_asm)
        return std.internal.math.biguintarm.multibyteShl(dest, src, numbits);
    else
        return std.internal.math.biguintnoasm.multibyteShl(dest, src, numbits);
}
else alias multibyteShl = std.internal.math.biguintnoasm.multibyteShl;

version (HaveAsmVersion)
void multibyteShr()(uint[] dest, const(uint)[] src, uint numbits)
{
    if (__ctfe)
        std.internal.math.biguintnoasm.multibyteShr(dest, src, numbits);
    else version (D_InlineAsm_X86)
        std.internal.math.biguintx86.multibyteShr(dest, src, numbits);
    else version (LDC_ARM_asm)
        std.internal.math.biguintarm.multibyteShr(dest, src, numbits);
    else
        std.internal.math.biguintnoasm.multibyteShr(dest, src, numbits);
}
else alias multibyteShr = std.internal.math.biguintnoasm.multibyteShr;

version (HaveAsmVersion)
uint multibyteMul()(uint[] dest, const(uint)[] src, uint multiplier, uint carry)
{
    if (__ctfe)
        return std.internal.math.biguintnoasm.multibyteMul(dest, src, multiplier, carry);
    else version (D_InlineAsm_X86)
        return std.internal.math.biguintx86.multibyteMul(dest, src, multiplier, carry);
    else version (LDC_ARM_asm)
        return std.internal.math.biguintarm.multibyteMul(dest, src, multiplier, carry);
    else
        return std.internal.math.biguintnoasm.multibyteMul(dest, src, multiplier, carry);
}
else alias multibyteMul = std.internal.math.biguintnoasm.multibyteMul;

version (HaveAsmVersion)
uint multibyteMulAdd(char op)(uint[] dest, const(uint)[] src, uint multiplier, uint carry)
{
    if (__ctfe)
        return std.internal.math.biguintnoasm.multibyteMulAdd!op(dest, src, multiplier, carry);
    else version (D_InlineAsm_X86)
        return std.internal.math.biguintx86.multibyteMulAdd!op(dest, src, multiplier, carry);
    else version (LDC_ARM_asm)
        return std.internal.math.biguintarm.multibyteMulAdd!op(dest, src, multiplier, carry);
    else
        return std.internal.math.biguintnoasm.multibyteMulAdd!op(dest, src, multiplier, carry);
}
else alias multibyteMulAdd = std.internal.math.biguintnoasm.multibyteMulAdd;

version (HaveAsmVersion)
void multibyteMultiplyAccumulate()(uint[] dest, const(uint)[] left, const(uint)[] right)
{
    if (__ctfe)
        std.internal.math.biguintnoasm.multibyteMultiplyAccumulate(dest, left, right);
    else version (D_InlineAsm_X86)
        std.internal.math.biguintx86.multibyteMultiplyAccumulate(dest, left, right);
    else version (LDC_ARM_asm)
        std.internal.math.biguintarm.multibyteMultiplyAccumulate(dest, left, right);
    else
        std.internal.math.biguintnoasm.multibyteMultiplyAccumulate(dest, left, right);
}
else alias multibyteMultiplyAccumulate = std.internal.math.biguintnoasm.multibyteMultiplyAccumulate;

version (HaveAsmVersion)
uint multibyteDivAssign()(uint[] dest, uint divisor, uint overflow)
{
    if (__ctfe)
        return std.internal.math.biguintnoasm.multibyteDivAssign(dest, divisor, overflow);
    else version (D_InlineAsm_X86)
        return std.internal.math.biguintx86.multibyteDivAssign(dest, divisor, overflow);
    else version (LDC_ARM_asm)
        return std.internal.math.biguintarm.multibyteDivAssign(dest, divisor, overflow);
    else
        return std.internal.math.biguintnoasm.multibyteDivAssign(dest, divisor, overflow);
}
else alias multibyteDivAssign = std.internal.math.biguintnoasm.multibyteDivAssign;

version (HaveAsmVersion)
void multibyteAddDiagonalSquares()(uint[] dest, const(uint)[] src)
{
    if (__ctfe)
        std.internal.math.biguintnoasm.multibyteAddDiagonalSquares(dest, src);
    else version (D_InlineAsm_X86)
        std.internal.math.biguintx86.multibyteAddDiagonalSquares(dest, src);
    else version (LDC_ARM_asm)
        std.internal.math.biguintarm.multibyteAddDiagonalSquares(dest, src);
    else
        std.internal.math.biguintnoasm.multibyteAddDiagonalSquares(dest, src);
}
else alias multibyteAddDiagonalSquares = std.internal.math.biguintnoasm.multibyteAddDiagonalSquares;

version (HaveAsmVersion)
void multibyteTriangleAccumulate()(uint[] dest, const(uint)[] x)
{
    if (__ctfe)
        std.internal.math.biguintnoasm.multibyteTriangleAccumulate(dest, x);
    else version (D_InlineAsm_X86)
        std.internal.math.biguintx86.multibyteTriangleAccumulate(dest, x);
    else version (LDC_ARM_asm)
        std.internal.math.biguintarm.multibyteTriangleAccumulate(dest, x);
    else
        std.internal.math.biguintnoasm.multibyteTriangleAccumulate(dest, x);
}
else alias multibyteTriangleAccumulate = std.internal.math.biguintnoasm.multibyteTriangleAccumulate;

version (HaveAsmVersion)
void multibyteSquare()(BigDigit[] result, const(BigDigit)[] x)
{
    if (__ctfe)
        std.internal.math.biguintnoasm.multibyteSquare(result, x);
    else version (D_InlineAsm_X86)
        std.internal.math.biguintx86.multibyteSquare(result, x);
    else version (LDC_ARM_asm)
        std.internal.math.biguintarm.multibyteSquare(result, x);
    else
        std.internal.math.biguintnoasm.multibyteSquare(result, x);
}
else alias multibyteSquare = std.internal.math.biguintnoasm.multibyteSquare;

// Limits for when to switch between algorithms.
// Half the size of the data cache.
@nogc nothrow pure @safe size_t getCacheLimit()
{
    import core.cpuid : dataCaches;
    return dataCaches[0].size * 1024 / 2;
}
enum size_t FASTDIVLIMIT = 100; // crossover to recursive division


// These constants are used by shift operations
static if (BigDigit.sizeof == int.sizeof)
{
    enum { LG2BIGDIGITBITS = 5, BIGDIGITSHIFTMASK = 31 }
    alias BIGHALFDIGIT = ushort;
}
else static if (BigDigit.sizeof == long.sizeof)
{
    alias BIGHALFDIGIT = uint;
    enum { LG2BIGDIGITBITS = 6, BIGDIGITSHIFTMASK = 63 }
}
else static assert(0, "Unsupported BigDigit size");
