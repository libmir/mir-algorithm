module mir.bignum.kernel;

import mir.bignum.phobos_kernel: multibyteShl, multibyteShr;

import mir.checkedint;
private alias cop(string op : "-") = subu;
private alias cop(string op : "+") = addu;

U multiplyAddKernel(string op, U)(
    scope U[] c,
    scope const(U)[] a,
    U b,
    U overflow = 0,
)
    @trusted pure nothrow @nogc
    if (op == "+" || op == "-")
    in (a.length == c.length)
{
    size_t j;
    do
    {
        import mir.utility: extMul;

        //(n - 1) ^ 2 + overflow + n - 1 <= n ^ 2 - 1
        // n ^ 2 - 2n + 1 + n - 1 + overflow <= n ^ 2 - 1
        // - n + overflow <= - 1
        // overflow <= n - 1
        auto ext = a[0].extMul(b);
        {
            bool bit;
            ext.low = ext.low.addu(overflow, bit);
            assert(ext.high < ext.high.max);
            ext.high += bit;
        }
        {
            bool bit;
            c[0] = c[0].cop!op(ext.low, bit);
            assert(bit == 0 || ext.high < ext.high.max);
            overflow = ext.high + bit;
        }

        a = a[1 .. $];
        c = c[1 .. $];
    }
    while(c.length);
    return overflow;
}

U addKernel(string op, U)(
    scope U[] c,
    scope const(U)[] a,
    U overflow = 0,
)
    @trusted pure nothrow @nogc
    if (op == "+" || op == "-")
    in (a.length == c.length)
{
    size_t j;
    do
    {
        import mir.checkedint: addu;
        import mir.utility: extMul;

        //(n - 1) ^ 2 + overflow + n - 1 <= n ^ 2 - 1
        // n ^ 2 - 2n + 1 + n - 1 + overflow <= n ^ 2 - 1
        // - n + overflow <= - 1
        // overflow <= n - 1
        U ext = a[0];
        {
            bool bit;
            ext = ext.addu(overflow, bit);
            overflow = bit;
        }
        {
            bool bit;
            c[0] = c[0].cop!op(ext, bit);
            overflow += bit;
        }

        a = a[1 .. $];
        c = c[1 .. $];
    }
    while(c.length);
    return overflow;
}

void multiply(U)(
    scope U[] c,
    scope const(U)[] a,
    scope const(U)[] b,
)
    @trusted pure nothrow @nogc
{
    pragma (inline, false);

    if (a.length < b.length)
    {
        auto t = a;
        a = b;
        b = t;
    }

    if (a.length > c.length)
        a = a[0 .. c.length];

    if (b.length > c.length)
        b = b[0 .. c.length];

    if (b.length == 0)
        return;

    assert(a.length);
    assert(b.length);
    assert(c.length);
    c[0 .. a.length] = 0;

    do
    {
        size_t j;
        import mir.utility: min;
        auto length = min(a.length, c.length);
        auto overflow = multiplyAddKernel!("+", U)(c[0 .. length], a[0 .. length], b[0]);
        if (length < c.length)
            c[length] = overflow;

        c = c[1 .. $];
        b = b[1 .. $];
    }
    while(b.length);
}

private inout(uint)[] toUints()(inout ulong[] data)
    @trusted pure nothrow @nogc
{
    auto ret = cast(typeof(return)) data;
    if (ret.length && ret[$ - 1] == 0)
        ret = ret[0 .. $ - 1];
    return ret;
}

size_t divMod(
    scope ulong[] u,
    scope ulong[] v,
    scope ulong[] q,
)
    @trusted pure nothrow @nogc
    in (u.length == 0 || u[$ - 1])
    in (v.length)
    in (v[$ - 1])
    in (q.length + v.length >= u.length + 1)
{
    auto length = divMod(
        u.toUints,
        v.toUints,
        cast(uint[])q,
    );

    bool fillTail = length % 2;
    length = length / 2;
    if (fillTail)
        q[length] &= uint.max;
    return length + fillTail;
}

size_t divMod(
    scope uint[] u,
    scope uint[] v,
    scope uint[] q,
)
    @trusted pure nothrow @nogc
    in (u.length == 0 || u[$ - 1])
    in (v.length)
    in (v[$ - 1])
    in (q.length + v.length >= u.length + 1)
{
    pragma (inline, false);

    import mir.bitop: ctlz;
    import mir.utility: _expect;

    size_t m = u.length;
    size_t n = v.length;

    if (m < n)
        return 0;

    sizediff_t lastQ = -1;
    if (n == 1)
    {
        uint k = 0;
        uint d = v[0];
        foreach_reverse(j; 0 .. m)
        {
            auto ut = (cast(ulong)k << 32) | u[j]; 
            q[j] = cast(uint)(ut / d);
            k = ut % d;
            u[j] = 0;
            if (lastQ == -1 && q[j])
                lastQ = j;
        }
        u[0] = k;
    }
    else
    {
        auto s = cast(uint)ctlz(v[n - 1]);
        assert(s <= 31 && s >= 0);

        uint umn = s ? u[$ - 1] >> (32 - s) : 0;
        u.multibyteShl(u, s);
        v.multibyteShl(v, s);

        uint vhi = v[$ - 1];
        uint vlo = v[$ - 2];

        uint* ujnp = &umn;
        ref uint ujn() @property { return *ujnp; }
        size_t j = m - n;
        do
        {
            uint qhat;
            if (ujn == vhi)
            {
                qhat = uint.max;
            }
            else
            {
                uint ulo = u[j + n - 2];

                ulong uu = (cast(ulong) ujn << 32) | u[j + n - 1];
                immutable bigqhat = uu / vhi;
                ulong rhat =  uu - bigqhat * vhi;
                qhat = cast(uint) bigqhat;
    again:
                if (cast(ulong) qhat * vlo > ((rhat << 32) + ulo))
                {
                    --qhat;
                    rhat += vhi;
                    if (!(rhat & 0xFFFF_FFFF_0000_0000L))
                        goto again;
                }
            }
            
            uint overflow = multiplyAddKernel!("-", uint)(u[j .. j + n], v, qhat);

            if (ujn < overflow)
            {
                --qhat;
                overflow -= addKernel!("+", uint)(u[j .. j + n], v);
            }

            if (lastQ == -1 && qhat)
                lastQ = j;
            q[j] = cast(uint) qhat;
            ujn -= overflow;
            ujnp = &u[j - 1 + n];
        }
        while(j--);

        if (s)
        {
            u.multibyteShr(u, s);
            // v.multibyteShr(v, s);
            u[$ - 1] |= umn << (32 - s);
        }
    }

    return lastQ + 1;
}

///
version(mir_bignum_test_llv)
unittest
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.low_level_view: BigUIntView;

    auto divMod(BigUIntView!uint a, BigUIntView!uint b, BigUIntView!uint c)
    {
        return .divMod(
            a.coefficients,
            b.coefficients,
            c.coefficients,
        );
    }

    {
        // Test division by a single-digit divisor here.
        auto dividend = BigUIntView!uint.fromHexString("5");
        auto divisor = BigUIntView!uint.fromHexString("5");
        auto quotient = BigUIntView!uint.fromHexString("0");
        // auto remainder = BigUIntView!uint.fromHexString("0");

        divMod(dividend, divisor, quotient);
        assert(quotient == BigUIntView!uint.fromHexString("1"));
    }

    {
        // Test division by a single-digit divisor here.
        auto dividend = BigUIntView!uint.fromHexString("55a325ad18b2a77120d870d987d5237473790532acab45da44bc07c92c92babf");
        auto divisor = BigUIntView!uint.fromHexString("5");
        auto quotient = BigUIntView!uint.fromHexString("0000000000000000000000000000000000000000000000000000000000000000");
        divMod(dividend, divisor, quotient);
        assert(dividend.normalized == BigUIntView!uint.fromHexString("3"));
        assert(quotient == BigUIntView!uint.fromHexString("1120a1229e8a217d0691b02b819107174a4b677088ef0df874259b283c1d588c"));
    }

    // Test big number division
    {
        auto dividend = BigUIntView!uint.fromHexString("55a325ad18b2a77120d870d987d5237473790532acab45da44bc07c92c92babf0b5e2e2c7771cd472ae5d7acdb159a56fbf74f851a058ae341f69d1eb750d7e3");
        auto divisor = BigUIntView!uint.fromHexString("55e5669576d31726f4a9b58a90159de5923adc6c762ebd3c4ba518d495229072");
        auto quotient = BigUIntView!uint.fromHexString("00000000000000000000000000000000000000000000000000000000000000000");
        // auto remainder = BigUIntView!uint.fromHexString("00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");

        divMod(dividend, divisor, quotient);
        assert(quotient.normalized == BigUIntView!uint.fromHexString("ff3a8aa4da35237811a0ffbf007fe938630dee8a810f2f82ae01f80c033291f6"));
        assert(dividend.normalized == BigUIntView!uint.fromHexString("27926263cf248bef1c2cd63ea004d9f7041bffc8568560ec30fc9a9548057857"));
    }

    // Trigger the adding back sequence
    {
        auto dividend = BigUIntView!uint.fromHexString("800000000000000000000003");
        auto divisor = BigUIntView!uint.fromHexString("200000000000000000000001");
        auto quotient = BigUIntView!uint.fromHexString("0");
        // auto remainder = BigUIntView!uint.fromHexString("000000000000000000000000");
        divMod(dividend, divisor, quotient);
        assert(quotient == BigUIntView!uint.fromHexString("3"));
        assert(dividend == BigUIntView!uint.fromHexString("200000000000000000000000"));
    }
}
