/**
This module contains various combinatorics algorithms.

Authors: Sebastian Wilzbach, Ilya Yaroshenko

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
*/
module mir.combinatorics;

import mir.math.sum: ResolveSummationType, Summation, Summator;
import mir.primitives: hasLength;
import mir.qualifier;
import std.traits;

///
version(mir_test) unittest
{
    import mir.ndslice.fuse;

    assert(['a', 'b'].permutations.fuse == [['a', 'b'], ['b', 'a']]);
    assert(['a', 'b'].cartesianPower(2).fuse == [['a', 'a'], ['a', 'b'], ['b', 'a'], ['b', 'b']]);
    assert(['a', 'b'].combinations(2).fuse == [['a', 'b']]);
    assert(['a', 'b'].combinationsRepeat(2).fuse == [['a', 'a'], ['a', 'b'], ['b', 'b']]);

    assert(permutations!ushort(2).fuse == [[0, 1], [1, 0]]);
    assert(cartesianPower!ushort(2, 2).fuse == [[0, 0], [0, 1], [1, 0], [1, 1]]);
    assert(combinations!ushort(2, 2).fuse == [[0, 1]]);
    assert(combinationsRepeat!ushort(2, 2).fuse == [[0, 0], [0, 1], [1, 1]]);

    assert([3, 1].permutations!ubyte.fuse == [[3, 1], [1, 3]]);
    assert([3, 1].cartesianPower!ubyte(2).fuse == [[3, 3], [3, 1], [1, 3], [1, 1]]);
    assert([3, 1].combinations!ubyte(2).fuse == [[3, 1]]);
    assert([3, 1].combinationsRepeat!ubyte(2).fuse == [[3, 3], [3, 1], [1, 1]]);
}

/**
Checks whether we can do basic arithmetic operations, comparisons, modulo and
assign values to the type.
*/
private template isArithmetic(R)
{
    enum bool isArithmetic = is(typeof(
    (inout int = 0)
    {
        R r = 1;
        R test = (r * r / r + r - r) % r;
        if (r < r && r > r) {}
    }));
}

/**
Checks whether we can do basic arithmetic operations, comparison and modulo
between two types. R needs to support item assignment of S (it includes S).
Both R and S need to be arithmetic types themselves.
*/
private template isArithmetic(R, S)
{
    enum bool isArithmetic = is(typeof(
    (inout int = 0)
    {
        if (isArithmetic!R && isArithmetic!S) {}
        S s = 1;
        R r = 1;
        R test = r * s + r * s;
        R test2 = r / s + r / s;
        R test3 = r - s + r - s;
        R test4 = r % s + r % s;
        if (r < s && s > r) {}
        if (s < r && r > s) {}
    }));
}

/**
Computes the $(WEB en.wikipedia.org/wiki/Binomial_coefficient, binomial coefficient)
of n and k.
It is also known as "n choose k" or more formally as `_n!/_k!(_n-_k)`.
If a fixed-length integer type is used and an overflow happens, `0` is returned.

Uses the generalized binomial coefficient for negative integers and floating
point number

Params:
    n = arbitrary arithmetic type
    k = arbitrary arithmetic type

Returns:
    Binomial coefficient
*/
R binomial(R = ulong, T)(T n, T k)
    if (isArithmetic!(R, T) &&
        ((is(typeof(T.min < 0)) && is(typeof(T.init & 1))) || !is(typeof(T.min < 0))) )
{
    R result = 1;

    enum hasMinProperty = is(typeof(T.min < 0));
    // only add negative support if possible
    static if ((hasMinProperty && T.min < 0) || !hasMinProperty)
    {
        if (n < 0)
        {
            if (k >= 0)
            {
                return (k & 1 ? -1 : 1) * binomial!(R, T)(-n + k-1, k);
            }
            else if (k <= n)
            {
                return ((n-k) & 1 ? -1 : 1) * binomial!(R, T)(-k-1, n-k);
            }
        }
        if (k < 0)
        {
            result = 0;
            return result;
        }
    }

    if (k > n)
    {
        result = 0;
        return result;
    }
    if (k > n - k)
    {
        k = n - k;
    }
    // make a copy of n (could be a custom type)
    for (T i = 1, m = n; i <= k; i++, m--)
    {
        // check whether an overflow can happen
        // hasMember!(Result, "max") doesn't work with dmd2.068 and ldc 0.17
        static if (is(typeof(0 > R.max)))
        {
            if (result / i > R.max / m) return 0;
            result = result / i * m + result % i * m / i;
        }
        else
        {
            result = result * m / i;
        }
    }
    return result;
}

///
pure version(mir_test) unittest
{
    assert(binomial(5, 2) == 10);
    assert(binomial(6, 4) == 15);
    assert(binomial(3, 1) == 3);

    import std.bigint: BigInt;
    assert(binomial!BigInt(1000, 10) == BigInt("263409560461970212832400"));
}

pure nothrow @safe @nogc version(mir_test) unittest
{
    assert(binomial(5, 1) == 5);
    assert(binomial(5, 0) == 1);
    assert(binomial(1, 2) == 0);
    assert(binomial(1, 0) == 1);
    assert(binomial(1, 1) == 1);
    assert(binomial(2, 1) == 2);
    assert(binomial(2, 1) == 2);

    // negative
    assert(binomial!long(-5, 3) == -35);
    assert(binomial!long(5, -3) == 0);
}

version(mir_test) unittest
{
    import std.bigint;

    // test larger numbers
    assert(binomial(100, 10) == 17_310_309_456_440);
    assert(binomial(999, 5) == 82_09_039_793_949);
    assert(binomial(300, 10) == 1_398_320_233_241_701_770LU);
    assert(binomial(300LU, 10LU) == 1_398_320_233_241_701_770LU);

    // test overflow
    assert(binomial(500, 10) == 0);

    // all parameters as custom types
    BigInt n = 1010, k = 9;
    assert(binomial!BigInt(n, k) == BigInt("2908077120956865974260"));

    // negative
    assert(binomial!BigInt(-5, 3) == -35);
    assert(binomial!BigInt(5, -3) == 0);
    assert(binomial!BigInt(-5, -7) == 15);
}

/**
Creates a projection of a generalized `Collection` range for the numeric case
case starting from `0` onto a custom `range` of any type.

Params:
    collection = range to be projected from
    range = random access range to be projected to

Returns:
    Range with a projection to range for every element of collection

See_Also:
    $(LREF permutations), $(LREF cartesianPower), $(LREF combinations),
    $(LREF combinationsRepeat)
*/
IndexedRoR!(Collection, Range) indexedRoR(Collection, Range)(Collection collection, Range range)
    if (__traits(compiles, Range.init[size_t.init]))
{
    return IndexedRoR!(Collection, Range)(collection, range);
}

/// ditto
struct IndexedRoR(Collection, Range)
    if (__traits(compiles, Range.init[size_t.init]))
{
    private Collection c;
    private Range r;

    ///
    alias DeepElement = ForeachType!Range;

    ///
    this()(Collection collection, Range range)
    {
        this.c = collection;
        this.r = range;
    }

    ///
    auto lightScope()()
    {
        return IndexedRoR!(LightScopeOf!Collection, LightScopeOf!Range)(.lightScope(c), .lightScope(r));
    }

    ///
    auto lightScope()() const
    {
        return IndexedRoR!(LightConstOf!(LightScopeOf!Collection), LightConstOf!(LightScopeOf!Range))(.lightScope(c), .lightScope(r));
    }

    ///
    auto lightConst()() const
    {
        return IndexedRoR!(LightConstOf!Collection, LightConstOf!Range)(.lightConst(c), .lightConst(r));
    }

    /// Input range primitives
    auto front()() @property
    {
        import mir.ndslice.slice: isSlice, sliced;
        import mir.ndslice.topology: indexed;
        import std.traits: ForeachType;
        static if (isSlice!(ForeachType!Collection))
            return r.indexed(c.front);
        else
            return r.indexed(c.front.sliced);
    }

    /// ditto
    void popFront() scope
    {
        c.popFront;
    }

    /// ditto
    bool empty()() @property scope const
    {
        return c.empty;
    }

    static if (hasLength!Collection)
    {
        /// ditto
        @property size_t length()() scope const
        {
            return c.length;
        }

        /// 
        @property size_t[2] shape()() scope const
        {
            return c.shape;
        }
    }

    static if (__traits(hasMember, Collection, "save"))
    {
        /// Forward range primitive. Calls `collection.save`.
        typeof(this) save()() @property
        {
            return IndexedRoR!(Collection, Range)(c.save, r);
        }
    }
}

///
@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.fuse;

    auto perms = 2.permutations;
    assert(perms.save.fuse == [[0, 1], [1, 0]]);

    auto projection = perms.indexedRoR([1, 2]);
    assert(projection.fuse == [[1, 2], [2, 1]]);
}

///
version(mir_test) unittest
{
    import mir.ndslice.fuse;
    // import mir.ndslice.topology: only;

    auto projectionD = 2.permutations.indexedRoR("ab"d);
    assert(projectionD.fuse == [['a', 'b'], ['b', 'a']]);

    // auto projectionC = 2.permutations.indexedRoR(only('a', 'b'));
    // assert(projectionC.fuse == [['a', 'b'], ['b', 'a']]);
}

@safe pure nothrow version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import std.range: dropOne;

    auto perms = 2.permutations;
    auto projection = perms.indexedRoR([1, 2]);
    assert(projection.length == 2);

    // can save
    assert(projection.save.dropOne.front == [2, 1]);
    assert(projection.front == [1, 2]);
}

@safe nothrow @nogc version(mir_test) unittest
{
    import mir.algorithm.iteration: all;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.fuse;
    static perms = 2.permutations;
    static immutable projectionArray = [1, 2];
    auto projection = perms.indexedRoR(projectionArray);

    static immutable result = [1, 2,
                               2, 1];
    assert(result.sliced(2, 2).all!"a == b"(projection));
}

/**
Lazily computes all _permutations of `r` using $(WEB
en.wikipedia.org/wiki/Heap%27s_algorithm, Heap's algorithm).

While generating a new item is in `O(k)` (amortized `O(1)`),
the number of permutations is `|n|!`.

Params:
    n = number of elements (`|r|`)
    r = random access field. A field may not have iteration primitivies.
    alloc = custom Allocator

Returns:
    Forward range, which yields the permutations

See_Also:
    $(LREF Permutations)
*/
Permutations!T permutations(T = uint)(size_t n) @safe pure nothrow
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(n, "must have at least one item");
    return Permutations!T(new T[n-1], new T[n]);
}

/// ditto
IndexedRoR!(Permutations!T, Range) permutations(T = uint, Range)(Range r) @safe pure nothrow
    if (__traits(compiles, Range.init[size_t.init]))
{
    return permutations!T(r.length).indexedRoR(r);
}

/// ditto
Permutations!T makePermutations(T = uint, Allocator)(auto ref Allocator alloc, size_t n)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(n, "must have at least one item");
    import std.experimental.allocator: makeArray;
    auto state = alloc.makeArray!T(n - 1);
    auto indices = alloc.makeArray!T(n);
    return Permutations!T(state, indices);
}

/**
Lazy Forward range of permutations using $(WEB
en.wikipedia.org/wiki/Heap%27s_algorithm, Heap's algorithm).

It always generates the permutations from 0 to `n - 1`,
use $(LREF indexedRoR) to map it to your range.

Generating a new item is in `O(k)` (amortized `O(1)`),
the total number of elements is `n^k`.

See_Also:
    $(LREF permutations), $(LREF makePermutations)
*/
struct Permutations(T)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    import mir.ndslice.slice: sliced, Slice;

    private T[] indices, state;
    private bool _empty;
    private size_t _max_states = 1, _pos;

    ///
    alias DeepElement = const T;

    /**
    state should have the length of `n - 1`,
    whereas the length of indices should be `n`
    */
    this()(T[] state, T[] indices) @safe pure nothrow @nogc
    {
        assert(state.length + 1 == indices.length);
        // iota
        foreach (i, ref index; indices)
            index = cast(T)i;
        state[] = 0;

        this.indices = indices;
        this.state = state;

        _empty = indices.length == 0;

        // factorial
        foreach (i; 1..indices.length + 1)
            _max_states *= i;
    }

    /// Input range primitives
    @property Slice!(const(T)*) front()() @safe pure nothrow @nogc
    {
        import mir.ndslice.slice: sliced;
        return indices.sliced;
    }

    /// ditto
    void popFront()() scope @safe pure nothrow @nogc
    {
        import std.algorithm.mutation : swapAt;

        assert(!empty);
        _pos++;

        for (T h = 0;;h++)
        {
            if (h + 2 > indices.length)
            {
                _empty = true;
                break;
            }

            indices.swapAt((h & 1) ? 0 : state[h], h + 1);

            if (state[h] == h + 1)
            {
                state[h] = 0;
                continue;
            }
            state[h]++;
            break;
        }
    }

    /// ditto
    @property bool empty()() @safe pure nothrow @nogc scope const
    {
        return _empty;
    }

    /// ditto
    @property size_t length()() @safe pure nothrow @nogc scope const
    {
        return _max_states - _pos;
    }

    /// 
    @property size_t[2] shape()() scope const
    {
        return [length, indices.length];
    }

    /// Forward range primitive. Allocates using GC.
    @property Permutations save()() @safe pure nothrow
    {
        typeof(this) c = this;
        c.indices = indices.dup;
        c.state = state.dup;
        return c;
    }
}

///
pure @safe nothrow version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology : iota;

    auto expectedRes = [[0, 1, 2],
         [1, 0, 2],
         [2, 0, 1],
         [0, 2, 1],
         [1, 2, 0],
         [2, 1, 0]];

    auto r = iota(3);
    auto rp = permutations(r.length).indexedRoR(r);
    assert(rp.fuse == expectedRes);

    // direct style
    auto rp2 = iota(3).permutations;
    assert(rp2.fuse == expectedRes);
}

///
@nogc version(mir_test) unittest
{
    import mir.algorithm.iteration: equal;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology : iota;

    import std.experimental.allocator.mallocator;

    static immutable expected2 = [0, 1, 1, 0];
    auto r = iota(2);
    auto rp = makePermutations(Mallocator.instance, r.length);
    assert(expected2.sliced(2, 2).equal(rp.indexedRoR(r)));
    dispose(Mallocator.instance, rp);
}

pure @safe nothrow version(mir_test) unittest
{
    // is copyable?
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;
    import std.range: dropOne;
    auto a = iota(2).permutations;
    assert(a.front == [0, 1]);
    assert(a.save.dropOne.front == [1, 0]);
    assert(a.front == [0, 1]);

    // length
    assert(1.permutations.length == 1);
    assert(2.permutations.length == 2);
    assert(3.permutations.length == 6);
    assert(4.permutations.length == 24);
    assert(10.permutations.length == 3_628_800);
}

version (assert)
version(mir_test) unittest
{
    // check invalid
    import std.exception: assertThrown;
    import core.exception: AssertError;
    import std.experimental.allocator.mallocator: Mallocator;

    assertThrown!AssertError(0.permutations);
    assertThrown!AssertError(Mallocator.instance.makePermutations(0));
}

/**
Disposes a Permutations object. It destroys and then deallocates the
Permutations object pointed to by a pointer.
It is assumed the respective entities had been allocated with the same allocator.

Params:
    alloc = Custom allocator
    perm = Permutations object

See_Also:
    $(LREF makePermutations)
*/
void dispose(T, Allocator)(auto ref Allocator alloc, auto ref Permutations!T perm)
{
    import std.experimental.allocator: dispose;
    dispose(alloc, perm.state);
    dispose(alloc, perm.indices);
}

/**
Lazily computes the Cartesian power of `r` with itself
for a number of repetitions `D repeat`.
If the input is sorted, the product is in lexicographic order.

While generating a new item is in `O(k)` (amortized `O(1)`),
the total number of elements is `n^k`.

Params:
    n = number of elements (`|r|`)
    r = random access field. A field may not have iteration primitivies.
    repeat = number of repetitions
    alloc = custom Allocator

Returns:
    Forward range, which yields the product items

See_Also:
    $(LREF CartesianPower)
*/
CartesianPower!T cartesianPower(T = uint)(size_t n, size_t repeat = 1) @safe pure nothrow
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(repeat >= 1, "Invalid number of repetitions");
    return CartesianPower!T(n, new T[repeat]);
}

/// ditto
IndexedRoR!(CartesianPower!T, Range) cartesianPower(T = uint, Range)(Range r, size_t repeat = 1)
if (isUnsigned!T && __traits(compiles, Range.init[size_t.init]))
{
    assert(repeat >= 1, "Invalid number of repetitions");
    return cartesianPower!T(r.length, repeat).indexedRoR(r);
}

/// ditto
CartesianPower!T makeCartesianPower(T = uint, Allocator)(auto ref Allocator alloc, size_t n, size_t repeat)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(repeat >= 1, "Invalid number of repetitions");
    import std.experimental.allocator: makeArray;
    return CartesianPower!T(n, alloc.makeArray!T(repeat));
}

/**
Lazy Forward range of Cartesian Power.
It always generates Cartesian Power from 0 to `n - 1`,
use $(LREF indexedRoR) to map it to your range.

Generating a new item is in `O(k)` (amortized `O(1)`),
the total number of elements is `n^k`.

See_Also:
    $(LREF cartesianPower), $(LREF makeCartesianPower)
*/
struct CartesianPower(T)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    import mir.ndslice.slice: Slice;

    private T[] _state;
    private size_t n;
    private size_t _max_states, _pos;

    ///
    alias DeepElement = const T;

    /// state should have the length of `repeat`
    this()(size_t n, T[] state) @safe pure nothrow @nogc
    {
        assert(state.length >= 1, "Invalid number of repetitions");

        import std.math: pow;
        this.n = n;
        assert(n <= T.max);
        this._state = state;

        _max_states = pow(n, state.length);
    }

    /// Input range primitives
    @property Slice!(const(T)*) front()() @safe pure nothrow @nogc
    {
        import mir.ndslice.slice: sliced;
        return _state.sliced;
    }

    /// ditto
    void popFront()() scope @safe pure nothrow @nogc
    {
        assert(!empty);
        _pos++;

        /*
        * Bitwise increment - starting from back
        * It works like adding 1 in primary school arithmetic.
        * If a block has reached the number of elements, we reset it to
        * 0, and continue to increment, e.g. for n = 2:
        *
        * [0, 0, 0] -> [0, 0, 1]
        * [0, 1, 1] -> [1, 0, 0]
        */
        foreach_reverse (i, ref el; _state)
        {
            ++el;
            if (el < n)
                break;

            el = 0;
        }
    }

    /// ditto
    @property size_t length()() @safe pure nothrow @nogc scope const
    {
        return _max_states - _pos;
    }

    /// ditto
    @property bool empty()() @safe pure nothrow @nogc scope const
    {
        return _pos == _max_states;
    }

    /// 
    @property size_t[2] shape()() scope const
    {
        return [length, _state.length];
    }

    /// Forward range primitive. Allocates using GC.
    @property CartesianPower save()() @safe pure nothrow
    {
        typeof(this) c = this;
        c._state = _state.dup;
        return c;
    }
}

///
pure nothrow @safe version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;
    assert(iota(2).cartesianPower.fuse == [[0], [1]]);
    assert(iota(2).cartesianPower(2).fuse == [[0, 0], [0, 1], [1, 0], [1, 1]]);

    auto three_nums_two_bins = [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]];
    assert(iota(3).cartesianPower(2).fuse == three_nums_two_bins);

    assert("AB"d.cartesianPower(2).fuse == ["AA"d, "AB"d, "BA"d, "BB"d]);
}

///
@nogc version(mir_test) unittest
{
    import mir.ndslice.topology: iota;
    import mir.algorithm.iteration: equal;
    import mir.ndslice.slice: sliced;

    import std.experimental.allocator.mallocator: Mallocator;
    auto alloc = Mallocator.instance;

    static immutable expected2r2 = [
        0, 0,
        0, 1,
        1, 0,
        1, 1];
    auto r = iota(2);
    auto rc = alloc.makeCartesianPower(r.length, 2);
    assert(expected2r2.sliced(4, 2).equal(rc.indexedRoR(r)));
    alloc.dispose(rc);
}

pure nothrow @safe version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import mir.array.allocation: array;
    import mir.ndslice.topology: iota;
    import std.range: dropOne;

    assert(iota(0).cartesianPower.length == 0);
    assert("AB"d.cartesianPower(3).fuse == ["AAA"d, "AAB"d, "ABA"d, "ABB"d, "BAA"d, "BAB"d, "BBA"d, "BBB"d]);
    auto expected = ["AA"d, "AB"d, "AC"d, "AD"d,
                     "BA"d, "BB"d, "BC"d, "BD"d,
                     "CA"d, "CB"d, "CC"d, "CD"d,
                     "DA"d, "DB"d, "DC"d, "DD"d];
    assert("ABCD"d.cartesianPower(2).fuse == expected);
    // verify with array too
    assert("ABCD"d.cartesianPower(2).fuse == expected);

    assert(iota(2).cartesianPower.front == [0]);

    // is copyable?
    auto a = iota(2).cartesianPower;
    assert(a.front == [0]);
    assert(a.save.dropOne.front == [1]);
    assert(a.front == [0]);

    // test length shrinking
    auto d = iota(2).cartesianPower;
    assert(d.length == 2);
    d.popFront;
    assert(d.length == 1);
}

version(assert)
version(mir_test) unittest
{
    // check invalid
    import std.exception: assertThrown;
    import core.exception: AssertError;
    import std.experimental.allocator.mallocator : Mallocator;

    assertThrown!AssertError(0.cartesianPower(0));
    assertThrown!AssertError(Mallocator.instance.makeCartesianPower(0, 0));
}

// length
pure nothrow @safe version(mir_test) unittest
{
    assert(1.cartesianPower(1).length == 1);
    assert(1.cartesianPower(2).length == 1);
    assert(2.cartesianPower(1).length == 2);
    assert(2.cartesianPower(2).length == 4);
    assert(2.cartesianPower(3).length == 8);
    assert(3.cartesianPower(1).length == 3);
    assert(3.cartesianPower(2).length == 9);
    assert(3.cartesianPower(3).length == 27);
    assert(3.cartesianPower(4).length == 81);
    assert(4.cartesianPower(10).length == 1_048_576);
    assert(14.cartesianPower(7).length == 105_413_504);
}

/**
Disposes a CartesianPower object. It destroys and then deallocates the
CartesianPower object pointed to by a pointer.
It is assumed the respective entities had been allocated with the same allocator.

Params:
    alloc = Custom allocator
    cartesianPower = CartesianPower object

See_Also:
    $(LREF makeCartesianPower)
*/
void dispose(T = uint, Allocator)(auto ref Allocator alloc, auto ref CartesianPower!T cartesianPower)
{
    import std.experimental.allocator: dispose;
    dispose(alloc, cartesianPower._state);
}

/**
Lazily computes all k-combinations of `r`.
Imagine this as the $(LREF cartesianPower) filtered for only strictly ordered items.

While generating a new combination is in `O(k)`,
the number of combinations is `binomial(n, k)`.

Params:
    n = number of elements (`|r|`)
    r = random access field. A field may not have iteration primitivies.
    k = number of combinations
    alloc = custom Allocator

Returns:
    Forward range, which yields the k-combinations items

See_Also:
    $(LREF Combinations)
*/
Combinations!T combinations(T = uint)(size_t n, size_t k = 1) @safe pure nothrow
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(k >= 1, "Invalid number of combinations");
    return Combinations!T(n, new T[k]);
}

/// ditto
IndexedRoR!(Combinations!T, Range) combinations(T = uint, Range)(Range r, size_t k = 1)
if (isUnsigned!T && __traits(compiles, Range.init[size_t.init]))
{
    assert(k >= 1, "Invalid number of combinations");
    return combinations!T(r.length, k).indexedRoR(r);
}

/// ditto
Combinations!T makeCombinations(T = uint, Allocator)(auto ref Allocator alloc, size_t n, size_t repeat)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(repeat >= 1, "Invalid number of repetitions");
    import std.experimental.allocator: makeArray;
    return Combinations!T(cast(T) n, alloc.makeArray!T(cast(T) repeat));
}

/**
Lazy Forward range of Combinations.
It always generates combinations from 0 to `n - 1`,
use $(LREF indexedRoR) to map it to your range.

Generating a new combination is in `O(k)`,
the number of combinations is `binomial(n, k)`.

See_Also:
    $(LREF combinations), $(LREF makeCombinations)
*/
struct Combinations(T)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    import mir.ndslice.slice: Slice;

    private T[] state;
    private size_t n;
    private size_t max_states, pos;

    ///
    alias DeepElement = const T;

    /// state should have the length of `repeat`
    this()(size_t n, T[] state) @safe pure nothrow @nogc
    {
        import mir.ndslice.topology: iota;

        assert(state.length <= T.max);
        this.n = n;
        assert(n <= T.max);
        this.max_states = cast(size_t) binomial(n, state.length);
        this.state = state;

        // set initial state and calculate max possibilities
        if (n > 0)
        {
            // skip first duplicate
            if (n > 1 && state.length > 1)
            {
                auto iotaResult = iota(state.length);
                foreach (i, ref el; state)
                {
                    el = cast(T) iotaResult[i];
                }
            }
        }
    }

    /// Input range primitives
    @property Slice!(const(T)*) front()() @safe pure nothrow @nogc
    {
        import mir.ndslice.slice: sliced;
        return state.sliced;
    }

    /// ditto
    void popFront()() scope @safe pure nothrow @nogc
    {
        assert(!empty);
        pos++;
        // we might have bumped into the end state now
        if (empty) return;

        // Behaves like: do _getNextState();  while (!_state.isStrictlySorted);
        size_t i = state.length - 1;
        /* Go from the back to next settable block
        * - A must block must be lower than it's previous
        * - A state i is not settable if it's maximum height is reached
        *
        * Think of it as a backwords search on state with
        * iota(_repeat + d, _repeat + d) as search mask.
        * (d = _nrElements -_repeat)
        *
        * As an example n = 3, r = 2, iota is [1, 2] and hence:
        * [0, 1] -> i = 2
        * [0, 2] -> i = 1
        */
        while (state[i] == n - state.length + i)
        {
            i--;
        }
        state[i] = cast(T)(state[i] + 1);

        /* Starting from our changed block, we need to take the change back
        * to the end of the state array and update them by their new diff.
        * [0, 1, 4] -> [0, 2, 3]
        * [0, 3, 4] -> [1, 2, 3]
        */
        foreach (j; i + 1 .. state.length)
        {
            state[j] = cast(T)(state[i] + j - i);
        }
    }

    /// ditto
    @property size_t length()() @safe pure nothrow @nogc scope const
    {
        return max_states - pos;
    }

    /// ditto
    @property bool empty()() @safe pure nothrow @nogc scope const
    {
        return pos == max_states;
    }

    /// 
    @property size_t[2] shape()() scope const
    {
        return [length, state.length];
    }

    /// Forward range primitive. Allocates using GC.
    @property Combinations save()() @safe pure nothrow
    {
        typeof(this) c = this;
        c.state = state.dup;
        return c;
    }
}

///
pure nothrow @safe version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;
    assert(iota(3).combinations(2).fuse == [[0, 1], [0, 2], [1, 2]]);
    assert("AB"d.combinations(2).fuse == ["AB"d]);
    assert("ABC"d.combinations(2).fuse == ["AB"d, "AC"d, "BC"d]);
}

///
@nogc version(mir_test) unittest
{
    import mir.algorithm.iteration: equal;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: iota;

    import std.experimental.allocator.mallocator;
    auto alloc = Mallocator.instance;

    static immutable expected3r2 = [
        0, 1,
        0, 2,
        1, 2];
    auto r = iota(3);
    auto rc = alloc.makeCombinations(r.length, 2);
    assert(expected3r2.sliced(3, 2).equal(rc.indexedRoR(r)));
    alloc.dispose(rc);
}

pure nothrow @safe version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import mir.array.allocation: array;
    import mir.ndslice.topology: iota;
    import std.range: dropOne;

    assert(iota(0).combinations.length == 0);
    assert(iota(2).combinations.fuse == [[0], [1]]);

    auto expected = ["AB"d, "AC"d, "AD"d, "BC"d, "BD"d, "CD"d];
    assert("ABCD"d.combinations(2).fuse == expected);
    // verify with array too
    assert("ABCD"d.combinations(2).fuse == expected);
    assert(iota(2).combinations.front == [0]);

    // is copyable?
    auto a = iota(2).combinations;
    assert(a.front == [0]);
    assert(a.save.dropOne.front == [1]);
    assert(a.front == [0]);

    // test length shrinking
    auto d = iota(2).combinations;
    assert(d.length == 2);
    d.popFront;
    assert(d.length == 1);

    // test larger combinations
    auto expected5 = [[0, 1, 2], [0, 1, 3], [0, 1, 4],
                      [0, 2, 3], [0, 2, 4], [0, 3, 4],
                      [1, 2, 3], [1, 2, 4], [1, 3, 4],
                      [2, 3, 4]];
    assert(iota(5).combinations(3).fuse == expected5);
    assert(iota(4).combinations(3).fuse == [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]);
    assert(iota(3).combinations(3).fuse == [[0, 1, 2]]);
    assert(iota(2).combinations(3).length == 0);
    assert(iota(1).combinations(3).length == 0);

    assert(iota(3).combinations(2).fuse == [[0, 1], [0, 2], [1, 2]]);
    assert(iota(2).combinations(2).fuse == [[0, 1]]);
    assert(iota(1).combinations(2).length == 0);

    assert(iota(1).combinations(1).fuse == [[0]]);
}

pure nothrow @safe version(mir_test) unittest
{
    // test larger combinations
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;

    auto expected6r4 = [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 5],
                        [0, 1, 3, 4], [0, 1, 3, 5], [0, 1, 4, 5],
                        [0, 2, 3, 4], [0, 2, 3, 5], [0, 2, 4, 5],
                        [0, 3, 4, 5], [1, 2, 3, 4], [1, 2, 3, 5],
                        [1, 2, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5]];
    assert(iota(6).combinations(4).fuse == expected6r4);

    auto expected6r3 = [[0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 1, 5],
                        [0, 2, 3], [0, 2, 4], [0, 2, 5], [0, 3, 4],
                        [0, 3, 5], [0, 4, 5], [1, 2, 3], [1, 2, 4],
                        [1, 2, 5], [1, 3, 4], [1, 3, 5], [1, 4, 5],
                        [2, 3, 4], [2, 3, 5], [2, 4, 5], [3, 4, 5]];
    assert(iota(6).combinations(3).fuse == expected6r3);

    auto expected6r2 = [[0, 1], [0, 2], [0, 3], [0, 4], [0, 5],
                        [1, 2], [1, 3], [1, 4], [1, 5], [2, 3],
                        [2, 4], [2, 5], [3, 4], [3, 5], [4, 5]];
    assert(iota(6).combinations(2).fuse == expected6r2);

    auto expected7r5 = [[0, 1, 2, 3, 4], [0, 1, 2, 3, 5], [0, 1, 2, 3, 6],
                        [0, 1, 2, 4, 5], [0, 1, 2, 4, 6], [0, 1, 2, 5, 6],
                        [0, 1, 3, 4, 5], [0, 1, 3, 4, 6], [0, 1, 3, 5, 6],
                        [0, 1, 4, 5, 6], [0, 2, 3, 4, 5], [0, 2, 3, 4, 6],
                        [0, 2, 3, 5, 6], [0, 2, 4, 5, 6], [0, 3, 4, 5, 6],
                        [1, 2, 3, 4, 5], [1, 2, 3, 4, 6], [1, 2, 3, 5, 6],
                        [1, 2, 4, 5, 6], [1, 3, 4, 5, 6], [2, 3, 4, 5, 6]];
    assert(iota(7).combinations(5).fuse == expected7r5);
}

// length
pure nothrow @safe version(mir_test) unittest
{
    assert(1.combinations(1).length == 1);
    assert(1.combinations(2).length == 0);
    assert(2.combinations(1).length == 2);
    assert(2.combinations(2).length == 1);
    assert(2.combinations(3).length == 0);
    assert(3.combinations(1).length == 3);
    assert(3.combinations(2).length == 3);
    assert(3.combinations(3).length == 1);
    assert(3.combinations(4).length == 0);
    assert(4.combinations(10).length == 0);
    assert(14.combinations(11).length == 364);
    assert(20.combinations(7).length == 77_520);
    assert(30.combinations(10).length == 30_045_015);
    assert(30.combinations(15).length == 155_117_520);
}

version(assert)
version(mir_test) unittest
{
    // check invalid
    import std.exception: assertThrown;
    import core.exception: AssertError;
    import std.experimental.allocator.mallocator: Mallocator;

    assertThrown!AssertError(0.combinations(0));
    assertThrown!AssertError(Mallocator.instance.makeCombinations(0, 0));
}

/**
Disposes a Combinations object. It destroys and then deallocates the
Combinations object pointed to by a pointer.
It is assumed the respective entities had been allocated with the same allocator.

Params:
    alloc = Custom allocator
    perm = Combinations object

See_Also:
    $(LREF makeCombinations)
*/
void dispose(T, Allocator)(auto ref Allocator alloc, auto ref Combinations!T perm)
{
    import std.experimental.allocator: dispose;
    dispose(alloc, perm.state);
}

/**
Lazily computes all k-combinations of `r` with repetitions.
A k-combination with repetitions, or k-multicombination,
or multisubset of size k from a set S is given by a sequence of k
not necessarily distinct elements of S, where order is not taken into account.
Imagine this as the cartesianPower filtered for only ordered items.

While generating a new combination with repeats is in `O(k)`,
the number of combinations with repeats is `binomial(n + k - 1, k)`.

Params:
    n = number of elements (`|r|`)
    r = random access field. A field may not have iteration primitivies.
    k = number of combinations
    alloc = custom Allocator

Returns:
    Forward range, which yields the k-multicombinations items

See_Also:
    $(LREF CombinationsRepeat)
*/
CombinationsRepeat!T combinationsRepeat(T = uint)(size_t n, size_t k = 1) @safe pure nothrow
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(k >= 1, "Invalid number of combinations");
    return CombinationsRepeat!T(n, new T[k]);
}

/// ditto
IndexedRoR!(CombinationsRepeat!T, Range) combinationsRepeat(T = uint, Range)(Range r, size_t k = 1)
    if (isUnsigned!T && __traits(compiles, Range.init[size_t.init]))
{
    assert(k >= 1, "Invalid number of combinations");
    return combinationsRepeat!T(r.length, k).indexedRoR(r);
}

/// ditto
CombinationsRepeat!T makeCombinationsRepeat(T = uint, Allocator)(auto ref Allocator alloc, size_t n, size_t repeat)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    assert(repeat >= 1, "Invalid number of repetitions");
    import std.experimental.allocator: makeArray;
    return CombinationsRepeat!T(n, alloc.makeArray!T(repeat));
}

/**
Lazy Forward range of combinations with repeats.
It always generates combinations with repeats from 0 to `n - 1`,
use $(LREF indexedRoR) to map it to your range.

Generating a new combination with repeats is in `O(k)`,
the number of combinations with repeats is `binomial(n, k)`.

See_Also:
    $(LREF combinationsRepeat), $(LREF makeCombinationsRepeat)
*/
struct CombinationsRepeat(T)
    if (isUnsigned!T && T.sizeof <= size_t.sizeof)
{
    import mir.ndslice.slice: Slice;

    private T[] state;
    private size_t n;
    private size_t max_states, pos;

    ///
    alias DeepElement = const T;

    /// state should have the length of `repeat`
    this()(size_t n, T[] state) @safe pure nothrow @nogc
    {
        this.n = n;
        assert(n <= T.max);
        this.state = state;
        size_t repeatLen = state.length;

        // set initial state and calculate max possibilities
        if (n > 0)
        {
            max_states = cast(size_t) binomial(n + repeatLen - 1, repeatLen);
        }
    }

    /// Input range primitives
    @property Slice!(const(T)*) front()() @safe pure nothrow @nogc
    {
        import mir.ndslice.slice: sliced;
        return state.sliced;
    }

    /// ditto
    void popFront()() scope @safe pure nothrow @nogc
    {
        assert(!empty);
        pos++;

        immutable repeat = state.length;

        // behaves like: do _getNextState();  while (!_state.isSorted);
        size_t i = repeat - 1;
        // go to next settable block
        // a block is settable if its not in the end state (=nrElements - 1)
        while (state[i] == n - 1 && i != 0)
        {
            i--;
        }
        state[i] = cast(T)(state[i] + 1);

        // if we aren't at the last block, we need to set all blocks
        // to equal the current one
        // e.g. [0, 2] -> (upper block: [1, 2]) -> [1, 1]
        if (i != repeat - 1)
        {
            for (size_t j = i + 1; j < repeat; j++)
                state[j] = state[i];
        }
    }

    /// ditto
    @property size_t length()() @safe pure nothrow @nogc scope const
    {
        return max_states - pos;
    }

    /// ditto
    @property bool empty()() @safe pure nothrow @nogc scope const
    {
        return pos == max_states;
    }

    /// 
    @property size_t[2] shape()() scope const
    {
        return [length, state.length];
    }

    /// Forward range primitive. Allocates using GC.
    @property CombinationsRepeat save()() @safe pure nothrow
    {
        typeof(this) c = this;
        c.state = state.dup;
        return c;
    }
}

///
pure nothrow @safe version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;

    assert(iota(2).combinationsRepeat.fuse == [[0], [1]]);
    assert(iota(2).combinationsRepeat(2).fuse == [[0, 0], [0, 1], [1, 1]]);
    assert(iota(3).combinationsRepeat(2).fuse == [[0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [2, 2]]);
    assert("AB"d.combinationsRepeat(2).fuse == ["AA"d, "AB"d,  "BB"d]);
}

///
@nogc version(mir_test) unittest
{
    import mir.algorithm.iteration: equal;
    import mir.ndslice.slice: sliced;
    import mir.ndslice.topology: iota;

    import std.experimental.allocator.mallocator;
    auto alloc = Mallocator.instance;

    static immutable expected3r1 = [
        0, 
        1, 
        2];
    auto r = iota(3);
    auto rc = alloc.makeCombinationsRepeat(r.length, 1);
    assert(expected3r1.sliced(3, 1).equal(rc.indexedRoR(r)));
    alloc.dispose(rc);
}

version(mir_test) unittest
{
    import mir.ndslice.fuse;
    import mir.array.allocation: array;
    import mir.ndslice.topology: iota;
    import std.range: dropOne;

    assert(iota(0).combinationsRepeat.length == 0);
    assert("AB"d.combinationsRepeat(3).fuse == ["AAA"d, "AAB"d, "ABB"d,"BBB"d]);

    auto expected = ["AA"d, "AB"d, "AC"d, "AD"d, "BB"d, "BC"d, "BD"d, "CC"d, "CD"d, "DD"d];
    assert("ABCD"d.combinationsRepeat(2).fuse == expected);
    // verify with array too
    assert("ABCD"d.combinationsRepeat(2).fuse == expected);

    assert(iota(2).combinationsRepeat.front == [0]);

    // is copyable?
    auto a = iota(2).combinationsRepeat;
    assert(a.front == [0]);
    assert(a.save.dropOne.front == [1]);
    assert(a.front == [0]);

    // test length shrinking
    auto d = iota(2).combinationsRepeat;
    assert(d.length == 2);
    d.popFront;
    assert(d.length == 1);
}

// length
pure nothrow @safe version(mir_test) unittest
{
    assert(1.combinationsRepeat(1).length == 1);
    assert(1.combinationsRepeat(2).length == 1);
    assert(2.combinationsRepeat(1).length == 2);
    assert(2.combinationsRepeat(2).length == 3);
    assert(2.combinationsRepeat(3).length == 4);
    assert(3.combinationsRepeat(1).length == 3);
    assert(3.combinationsRepeat(2).length == 6);
    assert(3.combinationsRepeat(3).length == 10);
    assert(3.combinationsRepeat(4).length == 15);
    assert(4.combinationsRepeat(10).length == 286);
    assert(11.combinationsRepeat(14).length == 1_961_256);
    assert(20.combinationsRepeat(7).length == 657_800);
    assert(20.combinationsRepeat(10).length == 20_030_010);
    assert(30.combinationsRepeat(10).length == 635_745_396);
}

pure nothrow @safe version(mir_test) unittest
{
    // test larger combinations
    import mir.ndslice.fuse;
    import mir.ndslice.topology: iota;

    auto expected3r1 = [[0], [1], [2]];
    assert(iota(3).combinationsRepeat(1).fuse == expected3r1);

    auto expected3r2 = [[0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [2, 2]];
    assert(iota(3).combinationsRepeat(2).fuse == expected3r2);

    auto expected3r3 = [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 1],
                        [0, 1, 2], [0, 2, 2], [1, 1, 1], [1, 1, 2],
                        [1, 2, 2], [2, 2, 2]];
    assert(iota(3).combinationsRepeat(3).fuse == expected3r3);

    auto expected3r4 = [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 2],
                        [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 2],
                        [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 2, 2],
                        [0, 2, 2, 2], [1, 1, 1, 1], [1, 1, 1, 2],
                        [1, 1, 2, 2], [1, 2, 2, 2], [2, 2, 2, 2]];
    assert(iota(3).combinationsRepeat(4).fuse == expected3r4);

    auto expected4r3 = [[0, 0, 0], [0, 0, 1], [0, 0, 2],
                        [0, 0, 3], [0, 1, 1], [0, 1, 2],
                        [0, 1, 3], [0, 2, 2], [0, 2, 3],
                        [0, 3, 3], [1, 1, 1], [1, 1, 2],
                        [1, 1, 3], [1, 2, 2], [1, 2, 3],
                        [1, 3, 3], [2, 2, 2], [2, 2, 3],
                        [2, 3, 3], [3, 3, 3]];
    assert(iota(4).combinationsRepeat(3).fuse == expected4r3);

    auto expected4r2 = [[0, 0], [0, 1], [0, 2], [0, 3],
                         [1, 1], [1, 2], [1, 3], [2, 2],
                         [2, 3], [3, 3]];
    assert(iota(4).combinationsRepeat(2).fuse == expected4r2);

    auto expected5r3 = [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 0, 3], [0, 0, 4],
                        [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 2],
                        [0, 2, 3], [0, 2, 4], [0, 3, 3], [0, 3, 4], [0, 4, 4],
                        [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 1, 4], [1, 2, 2],
                        [1, 2, 3], [1, 2, 4], [1, 3, 3], [1, 3, 4], [1, 4, 4],
                        [2, 2, 2], [2, 2, 3], [2, 2, 4], [2, 3, 3], [2, 3, 4],
                        [2, 4, 4], [3, 3, 3], [3, 3, 4], [3, 4, 4], [4, 4, 4]];
    assert(iota(5).combinationsRepeat(3).fuse == expected5r3);

    auto expected5r2 = [[0, 0], [0, 1], [0, 2], [0, 3], [0, 4],
                        [1, 1], [1, 2], [1, 3], [1, 4], [2, 2],
                        [2, 3], [2, 4], [3, 3], [3, 4], [4, 4]];
    assert(iota(5).combinationsRepeat(2).fuse == expected5r2);
}

version(assert)
version(mir_test) unittest
{
    // check invalid
    import std.exception: assertThrown;
    import core.exception: AssertError;
    import std.experimental.allocator.mallocator: Mallocator;

    assertThrown!AssertError(0.combinationsRepeat(0));
    assertThrown!AssertError(Mallocator.instance.makeCombinationsRepeat(0, 0));
}

/**
Disposes a CombinationsRepeat object. It destroys and then deallocates the
CombinationsRepeat object pointed to by a pointer.
It is assumed the respective entities had been allocated with the same allocator.

Params:
    alloc = Custom allocator
    perm = CombinationsRepeat object

See_Also:
    $(LREF makeCombinationsRepeat)
*/
void dispose(T, Allocator)(auto ref Allocator alloc, auto ref CombinationsRepeat!T perm)
{
    import std.experimental.allocator: dispose;
    dispose(alloc, perm.state);
}

/++
Computes the log of the factorial of the input.

The log of the factorial is computed directly if the input is less than 1,000.
For values 1,000 or larger, the log of the gamma function is used.

Params:
    F = controls type of output
    summation = algorithm for calculating sums (default: Summation.appropriate)

Returns:
    The log of the factorial of the input, must be floating point type

See_also: 
    $(SUBREF sum, Summation)
+/
template logFactorial(F, Summation summation = Summation.appropriate)
    if (isFloatingPoint!F)
{
    /++
    Params:
        n = arbitrary arithmetic type
    +/
    F logFactorial(T)(const T n)
        if (isArithmetic!T &&
            ((is(typeof(T.min < 0)) && is(typeof(T.init & 1))) || !is(typeof(T.min < 0))) )
        in(n >= 0, "n must be bigger than or equal to zero")
    {
        import mir.math.common: log;

        return .logFactorialPartial!(F, ResolveSummationType!(summation, const(F)[], F), T)(n);
    }
}

/// ditto
template logFactorial(Summation summation = Summation.appropriate)
{
    double logFactorial(T)(const T n)
        if (isArithmetic!T &&
            ((is(typeof(T.min < 0)) && is(typeof(T.init & 1))) || !is(typeof(T.min < 0))) )
        in(n >= 0, "n must be bigger than or equal to zero")
    {
        return .logFactorial!(double, summation)(n);
    }
}

///
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;
    assert(logFactorial(0) == 0);
    assert(logFactorial(1) == 0);
    assert(logFactorial(2).approxEqual(log(1.0 * 2)));
    assert(logFactorial(3).approxEqual(log(1.0 * 2 * 3)));
    assert(logFactorial(4).approxEqual(log(1.0 * 2 * 3 * 4)));
    assert(logFactorial(5).approxEqual(log(1.0 * 2 * 3 * 4 * 5)));
}

/// Can also set algorithm or output type
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    static assert(is(typeof(logFactorial!real(5)) == real));
    static assert(is(typeof(logFactorial!float(5)) == float));

    assert(logFactorial!(double, Summation.precise)(5).approxEqual(log(1.0 * 2 * 3 * 4 * 5)));
    assert(logFactorial!(Summation.precise)(5).approxEqual(log(1.0 * 2 * 3 * 4 * 5)));
}

// test larger value
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual;
    import std.mathspecial: logGamma;

    size_t x = logFactorialGammaAlternative + 500;
    assert(logFactorial(x).approxEqual(logGamma(cast(double) x + 1)));
    assert(logFactorial(cast(double) x).approxEqual(logGamma(cast(double) x + 1)));
}

// test BigInt
@safe pure nothrow
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;
    import std.mathspecial: logGamma;
    import std.bigint: BigInt;

    size_t x = logFactorialGammaAlternative + 500;
    assert(logFactorial(BigInt(5)).approxEqual(log(1.0 * 2 * 3 * 4 * 5)));
    assert(logFactorial(BigInt(x)).approxEqual(logGamma(cast(double) x + 1)));
}

// Controls when to switch from a direct calculation to using the Gamma function
// value selected based on performance comparison of logBinomial(x - 1, (x - 1) / 2)
// and logBinomial(x + 1, (x + 1) / 2)
private enum size_t logFactorialGammaAlternative = 2500;

@trusted
package(mir)
F logFactorialPartial(F = double, Summation summation = Summation.appropriate, T)(const T n, const T k = 0)
    if (isFloatingPoint!F && 
        isArithmetic!T &&
        ((is(typeof(T.min < 0)) && is(typeof(T.init & 1))) || !is(typeof(T.min < 0))) )
    in(k <= n, "k must be less than or equal to n")
    in(n >= 0, "n must be bigger than or equal to zero")
    in(k >= 0, "k must be bigger than or equal to zero")
{
    import mir.math.common: log;
    import std.bigint: BigInt;

    alias summationResolved = ResolveSummationType!(summation, const(F)[], F);
    Summator!(F, summationResolved) summator;

    if (n > 1 && n < logFactorialPartialSimpleTableLength) {
        static if (!is(T == BigInt)) {
            summator.put(cast(F) logFactorialPartialSimpleTable[cast(size_t) n]);
            summator.put(cast(F) -logFactorialPartialSimpleTable[cast(size_t) k]);
        } else {
            summator.put(logFactorialPartialSimple!(F, summation)(n, k));
        }
    } else if (n < logFactorialGammaAlternative) {
        summator.put(logFactorialPartialSimple!(F, summation)(n, k));
    } else {
        import std.mathspecial: logGamma;

        // logGamma is defined on real types, this ensures that the input is 
        // cast correctly, if needed
        static if (is(typeof(n) : real)) {
            alias V = typeof(n);
        } else {
            static if (__traits(hasMember, T, "max") && T.max < F.max) {
                // Handles fixed width custom data types that are not impicitly
                // convertible to real
                alias V = F;
            } else {
                assert(n <= real.max, "n must be less than or equal to real.max to be compatible with logGamma");
                alias V = real;
            }
        }

        // Add in n! and then subtract out k!
        summator.put(cast(F) logGamma(cast(V) n + 1));
        if (k > 1) {
            if (k < logFactorialPartialSimpleTableLength) {
                static if (!is(T == BigInt)) {
                    summator.put(cast(F) -logFactorialPartialSimpleTable[cast(size_t) k]);
                } else {
                    summator.put(-logFactorialPartialSimple!(F, summation)(k, T(1)));
                }
            } else if (k < logFactorialGammaAlternative) {
                summator.put(-logFactorialPartialSimple!(F, summation)(k, T(1)));
            } else if (k >= logFactorialGammaAlternative) {
                summator.put(cast(F) -logGamma(cast(V) k + 1));
            }
        }
    }
    return summator.sum;
}

// test values
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    assert(logFactorialPartial(0) == 0);
    assert(logFactorialPartial(1) == 0);
    assert(logFactorialPartial(1, 1) == 0);
    assert(logFactorialPartial(2).approxEqual(log(1.0 * 2)));
    assert(logFactorialPartial(2, 1).approxEqual(log(1.0 * 2)));
    assert(logFactorialPartial(2, 2) == 0);
    assert(logFactorialPartial(3).approxEqual(log(1.0 * 2 * 3)));
    assert(logFactorialPartial(3, 1).approxEqual(log(1.0 * 2 * 3)));
    assert(logFactorialPartial(3, 2).approxEqual(log(3.0)));
    assert(logFactorialPartial(3, 3) == 0);
    assert(logFactorialPartial(4).approxEqual(log(1.0 * 2 * 3 * 4)));
    assert(logFactorialPartial(4, 1).approxEqual(log(1.0 * 2 * 3 * 4)));
    assert(logFactorialPartial(4, 2).approxEqual(log(3.0 * 4)));
    assert(logFactorialPartial(4, 3).approxEqual(log(4.0)));
    assert(logFactorialPartial(4, 4) == 0);
}

// test large values
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual;
    import std.mathspecial: logGamma;

    size_t x = logFactorialGammaAlternative + 500;

    assert(logFactorialPartial(x).approxEqual(logGamma(cast(double) x + 1)));
    assert(logFactorialPartial(x, 250).approxEqual(logGamma(cast(double) x + 1) - logGamma(251.0)));
    assert(logFactorialPartial(x, x - 250).approxEqual(logGamma(cast(double) x + 1) - logGamma(cast(double) x - 250 + 1)));

    assert(logFactorialPartial(cast(double) x).approxEqual(logGamma(cast(double) x + 1)));
    assert(logFactorialPartial(cast(double) x, 250).approxEqual(logGamma(cast(double) x + 1) - logGamma(251.0)));
    assert(logFactorialPartial(cast(double) x, x - 250).approxEqual(logGamma(cast(double) x + 1) - logGamma(cast(double) x - 250 + 1)));
}

private
F logFactorialPartialSimple(F = double, Summation summation = Summation.appropriate, T)(const T n, const T k)
    if (isFloatingPoint!F && 
        isArithmetic!T &&
        ((is(typeof(T.min < 0)) && is(typeof(T.init & 1))) || !is(typeof(T.min < 0))) )
    in(k <= n, "k must be less than or equal to n")
    in(n >= 0, "n must be bigger than or equal to zero")
    in(k >= 0, "k must be bigger than or equal to zero")
{
    import mir.math.common: log;

    Summator!(F, ResolveSummationType!(summation, const(F)[], F)) summator;
    for (T i = T(k + 1); i < n + 1; i++) {
        summator.put(log(cast(F) i));
    }
    return summator.sum;
}

enum size_t logFactorialPartialSimpleTableLength = 256;
static assert(logFactorialPartialSimpleTableLength < logFactorialGammaAlternative, 
    "logFactorialPartialSimpleTableLength is assumed to be smaller than logFactorialGammaAlternative");
static immutable real[logFactorialPartialSimpleTableLength] logFactorialPartialSimpleTable;

shared static this()
{
    logFactorialPartialSimpleTable[0] = 0;
    logFactorialPartialSimpleTable[1] = 0;
    for (size_t i = 2; i < logFactorialPartialSimpleTableLength; i++) {
        logFactorialPartialSimpleTable[i] = logFactorialPartialSimple!(real, Summation.precise)(i, 1);
    }
}

/++
Computes the log of the $(WEB en.wikipedia.org/wiki/Binomial_coefficient, binomial coefficient)
of n and k.

The binomial coefficient is also known as "n choose k" or more formally as `_n!/_k!(_n-_k)`. The
log of the binomial coefficient is less likely to overflow than the raw binomial coefficient.

Params:
    F = controls type of output
    summation = algorithm for calculating sums (default: Summation.appropriate)

Returns:
    The log of binomial coefficient, must be a floating point type

See_also: 
    $(SUBREF sum, Summation)
+/
template logBinomial(F, Summation summation = Summation.appropriate)
    if (isFloatingPoint!F)
{
    /++
    Params:
        n = arbitrary arithmetic type
        k = arbitrary arithmetic type
    +/
    F logBinomial(T)(const T n, const T k)
        if (isArithmetic!T &&
            ((is(typeof(T.min < 0)) && is(typeof(T.init & 1))) || !is(typeof(T.min < 0))) )
        in(k <= n, "k must be less than or equal to n")
        in(n >= 0, "n must be bigger than or equal to zero")
        in(k >= 0, "k must be bigger than or equal to zero")
    {
        import mir.math.common: log;

        if ((k == 0) || (n == k) || (n == 1)) {
            return F(0);
        } else if (k == 1 || (n - k) == 1) {
            return log(cast(F) n);
        } else {
            alias summationResolved = ResolveSummationType!(summation, const(F)[], F);
            Summator!(F, summationResolved) summator;
            F logFactorial_k = 0;
            F logFactorial_n_k = 0;
            F logFactorial_n = 0;
            if ((n - k) > k) {
                logFactorial_k = logFactorialPartial!(F, summationResolved)(k);
                logFactorial_n = logFactorialPartial!(F, summationResolved)(n, n - k);
            } else if ((n - k) < k) {
                logFactorial_n_k = logFactorialPartial!(F, summationResolved)(n - k);
                logFactorial_n = logFactorialPartial!(F, summationResolved)(n, k);
            } else {
                logFactorial_k = logFactorialPartial!(F, summationResolved)(k);
                logFactorial_n = logFactorialPartial!(F, summationResolved)(n, k);
            }
            summator.put(logFactorial_n);
            summator.put(-logFactorial_k);
            summator.put(-logFactorial_n_k);
            return summator.sum;
        }
    }
}

/// ditto
template logBinomial(Summation summation = Summation.appropriate) {
    /// ditto
    double logBinomial(T)(const T n, const T k)
        if (isArithmetic!T && 
            ((is(typeof(T.min < 0)) && is(typeof(T.init & 1))) || !is(typeof(T.min < 0))) )
        in(k <= n, "k must be less than or equal to n")
        in(n >= 0, "n must be bigger than or equal to zero")
        in(k >= 0, "k must be bigger than or equal to zero")
    {
        return .logBinomial!(double, summation)(n, k);
    }
}

/// ditto
template logBinomial(F, string summation)
{
    mixin("alias logBinomial = .logBinomial!(F, Summation." ~ summation ~ ");");
}

/// ditto
template logBinomial(string summation)
{
    mixin("alias logBinomial = .logBinomial!(Summation." ~ summation ~ ");");
}

///
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    assert(logBinomial(5, 1).approxEqual(log(5.0)));
    assert(logBinomial(5, 2).approxEqual(log(cast(double) binomial(5, 2))));
    assert(logBinomial(5, 3).approxEqual(log(cast(double) binomial(5, 3))));
    assert(logBinomial(5, 4).approxEqual(log(cast(double) binomial(5, 4))));
}

/// Can also set algorithm or output type
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    static assert(is(typeof(logBinomial!real(5, 1)) == real));
    static assert(is(typeof(logBinomial!float(5, 1)) == float));

    assert(logBinomial!(double, "precise")(25, 12).approxEqual(log(cast(double) binomial(25, 12))));
    assert(logBinomial!"precise"(25, 12).approxEqual(log(cast(double) binomial(25, 12))));
}

// test n = 6
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    assert(logBinomial(6, 1).approxEqual(log(cast(double) binomial(6, 1))));
    assert(logBinomial(6, 2).approxEqual(log(cast(double) binomial(6, 2))));
    assert(logBinomial(6, 3).approxEqual(log(cast(double) binomial(6, 3))));
    assert(logBinomial(6, 4).approxEqual(log(cast(double) binomial(6, 4))));
    assert(logBinomial(6, 5).approxEqual(log(cast(double) binomial(6, 5))));
}

// test n = 7
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    assert(logBinomial(7, 1).approxEqual(log(cast(double) binomial(7, 1))));
    assert(logBinomial(7, 2).approxEqual(log(cast(double) binomial(7, 2))));
    assert(logBinomial(7, 3).approxEqual(log(cast(double) binomial(7, 3))));
    assert(logBinomial(7, 4).approxEqual(log(cast(double) binomial(7, 4))));
    assert(logBinomial(7, 5).approxEqual(log(cast(double) binomial(7, 5))));
    assert(logBinomial(7, 6).approxEqual(log(cast(double) binomial(7, 6))));
}

// test n = 8
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    assert(logBinomial(8, 1).approxEqual(log(cast(double) binomial(8, 1))));
    assert(logBinomial(8, 2).approxEqual(log(cast(double) binomial(8, 2))));
    assert(logBinomial(8, 3).approxEqual(log(cast(double) binomial(8, 3))));
    assert(logBinomial(8, 4).approxEqual(log(cast(double) binomial(8, 4))));
    assert(logBinomial(8, 5).approxEqual(log(cast(double) binomial(8, 5))));
    assert(logBinomial(8, 6).approxEqual(log(cast(double) binomial(8, 6))));
    assert(logBinomial(8, 7).approxEqual(log(cast(double) binomial(8, 7))));
}

// test k = 0, n = k
@safe pure nothrow @nogc
version(mir_test)
unittest {
    assert(logBinomial(5, 0) == 0);
    assert(logBinomial(5, 5) == 0);
    assert(logBinomial(1, 1) == 0);
    assert(logBinomial(1, 0) == 0);
}

// Test large values
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    size_t x = logFactorialGammaAlternative + 500;

    assert(logBinomial(x, 1).approxEqual(log(cast(double) x)));
    assert(logBinomial(x, 250).approxEqual(logFactorial(x) - logFactorial(250) - logFactorial(x - 250)));
    assert(logBinomial(x, x - 250).approxEqual(logBinomial(x, 250)));

    assert(logBinomial(cast(double) x, 1).approxEqual(log(cast(double) x)));
    assert(logBinomial(cast(double) x, 250).approxEqual(logFactorial(x) - logFactorial(250) - logFactorial(x - 250)));
    assert(logBinomial(cast(double) x, x - 250).approxEqual(logBinomial(x, 250)));
}

// additional check on providing summation
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    assert(logBinomial!(double, Summation.precise)(5, 3).approxEqual(log(cast(double) binomial(5, 3))));
    assert(logBinomial!(Summation.precise)(5, 3).approxEqual(log(cast(double) binomial(5, 3))));
}

// test BigInt
@safe pure nothrow
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;
    import std.mathspecial: logGamma;
    import std.bigint: BigInt;

    size_t x = logFactorialGammaAlternative + 500;
    assert(logBinomial(BigInt(5), BigInt(2)).approxEqual(log(cast(double) binomial(5, 2))));
    assert(logBinomial(BigInt(x), BigInt(1)).approxEqual(log(cast(double) x)));
    assert(logBinomial(BigInt(x), BigInt(250)).approxEqual(logFactorial(x) - logFactorial(250) - logFactorial(x - 250)));
    assert(logBinomial(BigInt(x), BigInt(x - 250)).approxEqual(logBinomial(x, 250)));
}

// check use of doubles
@safe pure nothrow @nogc
version(mir_test)
unittest {
    import mir.math.common: approxEqual, log;

    assert(logBinomial(5.0, 3.0).approxEqual(log(cast(double) binomial(5, 3))));
}
