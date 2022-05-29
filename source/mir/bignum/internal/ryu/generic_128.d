// Converted and then optimised from generic_128.h and generic_128.c
// Copyright 2018 Ulf Adams (original code https://github.com/ulfjack/ryu)
// Copyright 2020 Ilya Yaroshenko (2020 D conversion and optimisation)
// License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)

// This is a generic 128-bit implementation of float to shortest conversion
// using the Ryu algorithm. It can handle any IEEE-compatible floating-point
// type up to 128 bits. In order to use this correctly, you must use the
// appropriate *_to_fd128 function for the underlying type - DO NOT CAST your
// input to another floating-point type, doing so will result in incorrect
// output!
//
// For any floating-point type that is not natively defined by the compiler,
// you can use genericBinaryToDecimal to work directly on the underlying bit
// representation.

module mir.bignum.internal.ryu.generic_128;

version(BigEndian)
    static assert (0, "Let us know if you are using Mir on BigEndian target and we will add support for this module.");

debug(ryu) import core.stdc.stdio;

import mir.bignum.decimal: Decimal;
import mir.bignum.fixed: UInt, extendedMulHigh, extendedMul;

@safe pure nothrow @nogc:

// Returns e == 0 ? 1 : ceil(log_2(5^e)); requires 0 <= e <= 32768.
uint pow5bits(const int e)
{
    version(LDC) pragma(inline, true);
    assert(e >= 0);
    assert(e <= 1 << 15);
    return cast(uint) (((e * 163391164108059UL) >> 46) + 1);
}

void mul_128_256_shift(const UInt!128 a, const UInt!256 b, const uint shift, const uint corr, ref UInt!256 result)
{
    version(LDC) pragma(inline, true);
    assert(shift > 0);
    assert(shift < 256);
    result = (extendedMul(a, b) >> shift).toSize!256 + corr;
}

// Computes 5^i in the form required by Ryu, and stores it in the given pointer.
void generic_computePow5(const uint i, ref UInt!256 result)
{
    import mir.bignum.internal.ryu.table;

    version(LDC) pragma(inline, true);
    const uint base = i / POW5_TABLE_SIZE;
    const uint base2 = base * POW5_TABLE_SIZE;
    const mul = UInt!256(GENERIC_POW5_SPLIT[base]);
    if (i == base2)
    {
        result = mul;
    }
    else
    {
        const uint offset = i - base2;
        const m = UInt!128(GENERIC_POW5_TABLE[offset]);
        const uint delta = pow5bits(i) - pow5bits(base2);
        const uint corr = cast(uint) ((POW5_ERRORS[i / 32] >> (2 * (i % 32))) & 3);
        mul_128_256_shift(m, mul, delta, corr, result);
    }
}

version(mir_bignum_test) unittest
{
    // We only test a few entries - we could test the fUL table instead, but should we?
    static immutable uint[10] EXACT_POW5_IDS = [1, 10, 55, 56, 300, 1000, 2345, 3210, 4968 - 3, 4968 - 1];

    static immutable ulong[4][10] EXACT_POW5 = [
        [                   0u,                    0u,                    0u,  90071992547409920u],
        [                   0u,                    0u,                    0u,  83886080000000000u],
        [                   0u, 15708555500268290048u, 14699724349295723422u, 117549435082228750u],
        [                   0u,  5206161169240293376u,  4575641699882439235u,  73468396926392969u],
        [ 2042133660145364371u,  9702060195405861314u,  6467325284806654637u, 107597969523956154u],
        [15128847313296546509u, 11916317791371073891u,   788593023170869613u, 137108429762886488u],
        [10998857860460266920u,   858411415306315808u, 12732466392391605111u, 136471991906002539u],
        [ 5404652432687674341u, 18039986361557197657u,  2228774284272261859u,  94370442653226447u],
        [15313487127299642753u,  9780770376910163681u, 15213531439620567348u,  93317108016191349u],
        [ 7928436552078881485u,   723697829319983520u,   932817143438521969u,  72903990637649492u],
    ];

    for (int i = 0; i < 10; i++)
    {
        UInt!256 result;
        generic_computePow5(EXACT_POW5_IDS[i], result);
        assert(UInt!256(EXACT_POW5[i]) == result);
    }
}

// Computes 5^-i in the form required by Ryu, and stores it in the given pointer.
void generic_computeInvPow5(const uint i, ref UInt!256 result)
{
    import mir.bignum.internal.ryu.table;

    version(LDC) pragma(inline, true);
    const uint base = (i + POW5_TABLE_SIZE - 1) / POW5_TABLE_SIZE;
    const uint base2 = base * POW5_TABLE_SIZE;
    const mul = UInt!256(GENERIC_POW5_INV_SPLIT[base]); // 1/5^base2
    if (i == base2)
    {
        result = mul + 1;
    }
    else
    {
        const uint offset = base2 - i;
        const m = UInt!128(GENERIC_POW5_TABLE[offset]); // 5^offset
        const uint delta = pow5bits(base2) - pow5bits(i);
        const uint corr = cast(uint) ((POW5_INV_ERRORS[i / 32] >> (2 * (i % 32))) & 3) + 1;
        mul_128_256_shift(m, mul, delta, corr, result);
    }
}

version(mir_bignum_test) unittest
{
    static immutable uint[9] EXACT_INV_POW5_IDS = [10, 55, 56, 300, 1000, 2345, 3210, 4897 - 3, 4897 - 1];

    static immutable ulong[4][10] EXACT_INV_POW5 = [
        [13362655651931650467u,  3917988799323120213u,  9037289074543890586u, 123794003928538027u],
        [  983662216614650042u, 15516934687640009097u,  8839031818921249472u,  88342353238919216u],
        [ 1573859546583440066u,  2691002611772552616u,  6763753280790178510u, 141347765182270746u],
        [ 1607391579053635167u,   943946735193622172u, 10726301928680150504u,  96512915280967053u],
        [ 7238603269427345471u, 17319296798264127544u, 14852913523241959878u,  75740009093741608u],
        [ 2734564866961569744u, 13277212449690943834u, 17231454566843360565u,  76093223027199785u],
        [ 5348945211244460332u, 14119936934335594321u, 15647307321253222579u, 110040743956546595u],
        [ 2848579222248330872u, 15087265905644220040u,  4449739884766224405u, 100774177495370196u],
        [ 1432572115632717323u,  9719393440895634811u,  3482057763655621045u, 128990947194073851u],
    ];

    for (int i = 0; i < 9; i++)
    {
        UInt!256 result;
        generic_computeInvPow5(EXACT_INV_POW5_IDS[i], result);
        assert(UInt!256(EXACT_INV_POW5[i]) == result);
    }
}

version(LittleEndian)
    enum fiveReciprocal = UInt!128([0xCCCCCCCCCCCCCCCD, 0xCCCCCCCCCCCCCCCC]);
else
    enum fiveReciprocal = UInt!128([0xCCCCCCCCCCCCCCCC, 0xCCCCCCCCCCCCCCCD]);

enum baseDiv5 = UInt!128([0x3333333333333333, 0x3333333333333333]);

uint divRem5(uint size)(ref UInt!size value)
{
    auto q = div5(value);
    auto r = cast(uint)(value - q * 5);
    value = q;
    return r;
}

uint divRem10(uint size)(ref UInt!size value)
{
    auto q = div10(value);
    auto r = cast(uint)(value - q * 10);
    value = q;
    return r;
}

uint rem5(uint size)(UInt!size value)
{
    return divRem5(value);
}

uint rem10(uint size)(UInt!size value)
{
    return divRem10(value);
}

UInt!size div5(uint size)(UInt!size value)
{
    return extendedMulHigh(value, fiveReciprocal.toSize!size) >> 2;
}

UInt!size div10(uint size)(UInt!size value)
{
    return extendedMulHigh(value, fiveReciprocal.toSize!size) >> 3;
}

// Returns true if value is divisible by 5^p.
bool multipleOfPowerOf5(uint size)(UInt!size value, const uint p)
{
    enum fiveReciprocal = .fiveReciprocal.toSize!size;
    enum baseDiv5 = .baseDiv5.toSize!size;
    version(LDC) pragma(inline, true);
    assert(value);
    for (uint count = 0;; ++count)
    {
        value *= fiveReciprocal;
        if (value > baseDiv5)
            return count >= p;
    }
}

version(mir_bignum_test) unittest
{
    assert(multipleOfPowerOf5(UInt!128(1), 0) == true);
    assert(multipleOfPowerOf5(UInt!128(1), 1) == false);
    assert(multipleOfPowerOf5(UInt!128(5), 1) == true);
    assert(multipleOfPowerOf5(UInt!128(25), 2) == true);
    assert(multipleOfPowerOf5(UInt!128(75), 2) == true);
    assert(multipleOfPowerOf5(UInt!128(50), 2) == true);
    assert(multipleOfPowerOf5(UInt!128(51), 2) == false);
    assert(multipleOfPowerOf5(UInt!128(75), 4) == false);
}

// Returns true if value is divisible by 2^p.
bool multipleOfPowerOf2(uint size)(const UInt!size value, const uint p)
{
    version(LDC) pragma(inline, true);
    return (value & ((UInt!size(1) << p) - 1)) == 0;
}

version(mir_bignum_test) unittest
{
    assert(multipleOfPowerOf5(UInt!128(1), 0) == true);
    assert(multipleOfPowerOf5(UInt!128(1), 1) == false);
    assert(multipleOfPowerOf2(UInt!128(2), 1) == true);
    assert(multipleOfPowerOf2(UInt!128(4), 2) == true);
    assert(multipleOfPowerOf2(UInt!128(8), 2) == true);
    assert(multipleOfPowerOf2(UInt!128(12), 2) == true);
    assert(multipleOfPowerOf2(UInt!128(13), 2) == false);
    assert(multipleOfPowerOf2(UInt!128(8), 4) == false);
}

UInt!size mulShift(uint size)(const UInt!size m, const UInt!256 mul, const uint j)
{
    version(LDC) pragma(inline, true);
    assert(j > 128);
    return (extendedMul(mul, m) >> 128 >> (j - 128)).toSize!size;
}

version(mir_bignum_test) unittest
{
    UInt!256 m = cast(ulong[4])[0, 0, 2, 0];
    assert(mulShift(UInt!128(1), m, 129) == 1u);
    assert(mulShift(UInt!128(12345), m, 129) == 12345u);
}

version(mir_bignum_test) unittest
{
    UInt!256 m = cast(ulong[4])[0, 0, 8, 0];
    UInt!128 f = (UInt!128(123) << 64) | 321;
    assert(mulShift(f, m, 131) == f);
}

// Returns floor(log_10(2^e)).
uint log10Pow2(const int e)
{
    version(LDC) pragma(inline, true);
    // The first value this approximation fails for is 2^1651 which is just greater than 10^297.
    assert(e >= 0);
    assert(e <= 1 << 15);
    return (e * 0x9A209A84FBCFUL) >> 49;
}

version(mir_bignum_test) unittest
{
    assert(log10Pow2(1) == 0u);
    assert(log10Pow2(5) == 1u);
    assert(log10Pow2(1 << 15) == 9864u);
}

// Returns floor(log_10(5^e)).
uint log10Pow5(const int e)
{
    version(LDC) pragma(inline, true);
    // The first value this approximation fails for is 5^2621 which is just greater than 10^1832.
    assert(e >= 0);
    assert(e <= 1 << 15);
    return (e * 0xB2EFB2BD8218UL) >> 48;
}

version(mir_bignum_test) unittest
{
    assert(log10Pow5(1) == 0u);
    assert(log10Pow5(2) == 1u);
    assert(log10Pow5(3) == 2u);
    assert(log10Pow5(1 << 15) == 22903u);
}

debug(ryu)
private char* s(UInt!128 v)
{
    import mir.conv: to;
    return (v.to!string ~ "\0").ptr;
}

// Converts the given binary floating point number to the shortest decimal floating point number
// that still accurately represents it.
Decimal!(T.mant_dig < 64 ? 1 : 2) genericBinaryToDecimal(T)(const T x)
{
    import mir.utility: _expect;
    import mir.math: signbit, fabs;
    enum coefficientSize = T.mant_dig <= 64 ? 64 : 128;
    enum workSize = T.mant_dig < 64 ? 64 : 128;
    enum wordCount = workSize / 64;

    Decimal!wordCount fd;
    if (_expect(x != x, false))
    {
        fd.coefficient = 1u;
        fd.exponent = fd.exponent.max;
    }
    else
    if (_expect(x.fabs == T.infinity, false))
    {
        fd.exponent = fd.exponent.max;
    }
    else
    if (x)
    {
        import mir.bignum.fp: Fp;
        const fp = Fp!coefficientSize(x, false);
        int e2 = cast(int) fp.exponent - 2;
        UInt!workSize m2 = fp.coefficient;

        const bool even = (fp.coefficient & 1) == 0;
        const bool acceptBounds = even;

        debug(ryu) if (!__ctfe)
        {
            printf("-> %s %s * 2^%d\n", (fp.sign ? "-" : "+").ptr, s(m2), e2 + 2);
        }

        // Step 2: Determine the interval of legal decimal representations.
        const UInt!workSize mv = m2 << 2;
        // Implicit bool -> int conversion. True is 1, false is 0.
        const bool mmShift = fp.coefficient != (UInt!coefficientSize(1) << (T.mant_dig - 1));

        // Step 3: Convert to a decimal power base using 128-bit arithmetic.
        UInt!workSize vr, vp, vm;
        int e10;
        bool vmIsTrailingZeros = false;
        bool vrIsTrailingZeros = false;
        if (e2 >= 0)
        {
            // I tried special-casing q == 0, but there was no effect on performance.
            // This expression is slightly faster than max(0, log10Pow2(e2) - 1).
            const uint q = log10Pow2(e2) - (e2 > 3);
            e10 = q;
            const int k = FLOAT_128_POW5_INV_BITCOUNT + pow5bits(q) - 1;
            const int i = -e2 + q + k;
            UInt!256 pow5;
            generic_computeInvPow5(q, pow5);
            vr = mulShift(mv, pow5, i);
            vp = mulShift(mv + 2, pow5, i);
            vm = mulShift(mv - 1 - mmShift, pow5, i);
            debug(ryu) if (!__ctfe)
            {
                printf("%s * 2^%d / 10^%d\n", s(mv), e2, q);
                printf("V+=%s\nV =%s\nV-=%s\n", s(vp), s(vr), s(vm));
            }
            // floor(log_5(2^128)) = 55, this is very conservative
            if (q <= 55)
            {
                // Only one of mp, mv, and mm can be a multiple of 5, if any.
                if (rem5(mv) == 0)
                {
                    vrIsTrailingZeros = multipleOfPowerOf5(mv, q - 1);
                }
                else
                if (acceptBounds)
                {
                    // Same as min(e2 + (~mm & 1), pow5Factor(mm)) >= q
                    // <=> e2 + (~mm & 1) >= q && pow5Factor(mm) >= q
                    // <=> true && pow5Factor(mm) >= q, since e2 >= q.
                    vmIsTrailingZeros = multipleOfPowerOf5(mv - 1 - mmShift, q);
                }
                else
                {
                    // Same as min(e2 + 1, pow5Factor(mp)) >= q.
                    vp -= multipleOfPowerOf5(mv + 2, q);
                }
            }
        }
        else
        {
            // This expression is slightly faster than max(0, log10Pow5(-e2) - 1).
            const uint q = log10Pow5(-e2) - (-e2 > 1);
            e10 = q + e2;
            const int i = -e2 - q;
            const int k = pow5bits(i) - FLOAT_128_POW5_BITCOUNT;
            const int j = q - k;
            UInt!256 pow5;
            generic_computePow5(i, pow5);
            vr = mulShift(mv, pow5, j);
            vp = mulShift(mv + 2, pow5, j);
            vm = mulShift(mv - 1 - mmShift, pow5, j);
            debug(ryu) if (!__ctfe)
            {
                printf("%s * 5^%d / 10^%d\n", s(mv), -e2, q);
                printf("%d %d %d %d\n", q, i, k, j);
                printf("V+=%s\nV =%s\nV-=%s\n", s(vp), s(vr), s(vm));
            }
            if (q <= 1)
            {
                // {vr,vp,vm} is trailing zeros if {mv,mp,mm} has at least q trailing 0 bits.
                // mv = 4 m2, so it always has at least two trailing 0 bits.
                vrIsTrailingZeros = true;
                if (acceptBounds)
                {
                    // mm = mv - 1 - mmShift, so it has 1 trailing 0 bit iff mmShift == 1.
                    vmIsTrailingZeros = mmShift == 1;
                }
                else
                {
                    // mp = mv + 2, so it always has at least one trailing 0 bit.
                    --vp;
                }
            }
            else
            if (q < workSize - 1)
            {
                // TODO(ulfjack): Use a tighter bound here.
                // We need to compute min(ntz(mv), pow5Factor(mv) - e2) >= q-1
                // <=> ntz(mv) >= q-1  &&  pow5Factor(mv) - e2 >= q-1
                // <=> ntz(mv) >= q-1    (e2 is negative and -e2 >= q)
                // <=> (mv & ((1 << (q-1)) - 1)) == 0
                // We also need to make sure that the left shift does not overflow.
                vrIsTrailingZeros = multipleOfPowerOf2(mv, q - 1);
                debug(ryu) if (!__ctfe)
                {
                    printf("vr is trailing zeros=%s\n", (vrIsTrailingZeros ? "true" : "false").ptr);
                }
            }
        }
        debug(ryu) if (!__ctfe)
        {
            printf("e10=%d\n", e10);
            printf("V+=%s\nV =%s\nV-=%s\n", s(vp), s(vr), s(vm));
            printf("vm is trailing zeros=%s\n", (vmIsTrailingZeros ? "true" : "false").ptr);
            printf("vr is trailing zeros=%s\n", (vrIsTrailingZeros ? "true" : "false").ptr);
        }

        // Step 4: Find the shortest decimal representation in the interval of legal representations.
        uint removed = 0;
        uint lastRemovedDigit = 0;
        UInt!workSize output;

        for (;;)
        {
            auto div10vp = div10(vp);
            auto div10vm = div10(vm);
            if (div10vp == div10vm)
                break;
            vmIsTrailingZeros &= vm - div10vm * 10 == 0;
            vrIsTrailingZeros &= lastRemovedDigit == 0;
            lastRemovedDigit = vr.divRem10;
            vp = div10vp;
            vm = div10vm;
            ++removed;
        }
        debug(ryu) if (!__ctfe)
        {
            printf("V+=%s\nV =%s\nV-=%s\n", s(vp), s(vr), s(vm));
            printf("d-10=%s\n", (vmIsTrailingZeros ? "true" : "false").ptr);
            printf("lastRemovedDigit=%d\n", lastRemovedDigit);
        }
        if (vmIsTrailingZeros)
        {
            for (;;)
            {
                auto div10vm = div10(vm);
                if (vm - div10vm * 10)
                    break;
                vrIsTrailingZeros &= lastRemovedDigit == 0;
                lastRemovedDigit = cast(uint) (vr - div10vm * 10);
                vr = vp = vm = div10vm;
                ++removed;
            }
        }
        debug(ryu) if (!__ctfe)
        {
            printf("%s %d\n", s(vr), lastRemovedDigit);
            printf("vr is trailing zeros=%s\n", (vrIsTrailingZeros ? "true" : "false").ptr);
            printf("lastRemovedDigit=%d\n", lastRemovedDigit);
        }
        if (vrIsTrailingZeros && (lastRemovedDigit == 5) && ((vr & 1) == 0))
        {
            // Round even if the exact numbers is .....50..0.
            lastRemovedDigit = 4;
        }
        // We need to take vr+1 if vr is outside bounds or we need to round up.
        output = vr + ((vr == vm && (!acceptBounds || !vmIsTrailingZeros)) || (lastRemovedDigit >= 5));

        const int exp = e10 + removed;

        debug(ryu) if (!__ctfe)
        {
            printf("V+=%s\nV =%s\nV-=%s\n", s(vp), s(vr), s(vm));
            printf("acceptBounds=%d\n", acceptBounds);
            printf("vmIsTrailingZeros=%d\n", vmIsTrailingZeros);
            printf("lastRemovedDigit=%d\n", lastRemovedDigit);
            printf("vrIsTrailingZeros=%d\n", vrIsTrailingZeros);
            printf("O=%s\n", s(output));
            printf("EXP=%d\n", exp);
        }

        import mir.bignum.integer: BigInt;
        fd.coefficient.__ctor(output);
        fd.exponent = exp;
    }
    fd.coefficient.sign = x.signbit;
    return fd;
}

private enum FLOAT_128_POW5_INV_BITCOUNT = 249;
private enum FLOAT_128_POW5_BITCOUNT = 249;
