module mir.bignum.internal.kernel;

import mir.bignum.internal.phobos_kernel;
public import mir.bignum.internal.phobos_kernel: karatsubaRequiredBuffSize, divisionRequiredBuffSize;

private inout(uint)[] toUints()(inout ulong[] data)
    @trusted pure nothrow @nogc
{
    auto ret = cast(typeof(return)) data;
    if (ret.length && ret[$ - 1] == 0)
        ret = ret[0 .. $ - 1];
    return ret;
}

static if (is(size_t == ulong))
size_t multiply(
    scope ulong[] c,
    scope const(ulong)[] a,
    scope const(ulong)[] b,
    scope ulong[] buffer,
)
    @safe pure nothrow @nogc
    in (c.length >= a.length + b.length)
{
    pragma (inline, false);

    c[a.length + b.length - 1] = 0;

    auto length = multiply(
        cast(uint[]) c,
        a.toUints,
        b.toUints,
        cast(uint[]) buffer,
    );

    return length / 2 + length % 2;
}

size_t multiply(
    scope uint[] c,
    scope const(uint)[] a,
    scope const(uint)[] b,
    scope uint[] buffer,
)
    @trusted pure nothrow @nogc
    in (c.length >= a.length + b.length)
{
    pragma (inline, false);

    if (a.length < b.length)
    {
        auto t = a;
        a = b;
        b = t;
    }

    if (b.length == 0)
        return 0;

    assert(a.length);
    assert(b.length);
    assert(c.length);

    c = c[0 .. a.length + b.length];

    if (a is b)
        squareInternal(c, a, buffer);
    else
        mulInternal(c, a, b, buffer);

    auto ret = a.length + b.length;
    ret -= ret && !c[ret - 1];
    return ret;
}


static if (is(size_t == ulong))
size_t divMod(
    scope ulong[] q,
    scope ulong[] r,
    scope const(ulong)[] u,
    scope const(ulong)[] v,
    scope ulong[] buffer,
)
    @trusted pure nothrow @nogc
    in (u.length == 0 || u[$ - 1])
    in (v.length)
    in (v[$ - 1])
    in (q.length + v.length >= u.length + 1)
{
    pragma (inline, false);

    sizediff_t idx = u.length - v.length;
    if (idx < 0)
        return 0;

    auto ui = u.toUints;
    auto vi = v.toUints;

    auto length = divMod(
        cast(uint[])q,
        cast(uint[])r,
        ui,
        vi,
        cast(uint[]) buffer,
    );

    if (r.length && vi.length % 2)
        r[vi.length / 2] &= uint.max;

    if (q.ptr is r.ptr)
        return 0;

    auto ret = length / 2;
        if (length % 2)
            q[ret++] &= uint.max;
    return ret;
}

size_t divMod(
    scope uint[] q,
    scope uint[] r,
    scope const(uint)[] u,
    scope const(uint)[] v,
    scope uint[] buffer,
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

    if (u.length < v.length)
        return 0;

    q = q[0 .. u.length - v.length + 1];
    if (v.length == 1)
    {
        if (q !is u)
            q[] = u;
        auto rem = multibyteDivAssign(q, v[0], 0);
        if (r)
        {
            r[0] = rem;
            r[1 .. $] = 0;
        }
    }
    else
    {
        divModInternal(q[], r ? r[0 .. v.length] : null, u, v, buffer);
    }

    auto length = u.length - v.length;
    return length + (q[length] != 0);
}

///
version(mir_bignum_test)
unittest
{
    import mir.bignum.fixed: UInt;
    import mir.bignum.low_level_view: BigUIntView;

    uint[100] buffer = void;
    auto divMod(BigUIntView!uint a, BigUIntView!uint b, BigUIntView!uint c)
    {
        .divMod(
            c.coefficients,
            a.coefficients,
            a.coefficients,
            b.coefficients,
            buffer,
        );
        a.coefficients[b.coefficients.length .. $] = 0;
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
