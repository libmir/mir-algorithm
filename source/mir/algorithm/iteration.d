// Written in the D programming language.
/**
This is a submodule of $(MREF std, algorithm).
It contains generic _iteration algorithms.
$(SCRIPT inhibitQuickIndex = 1;)
$(BOOKTABLE Cheat Sheet,
$(TR $(TH Function Name) $(TH Description))
$(T2 uniq,
        Iterates over the unique elements in a range, which is assumed sorted.)
)
Copyright: Andrei Alexandrescu 2008-.
License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: $(HTTP erdani.com, Andrei Alexandrescu) (original Phobos code), Ilya Yaroshenko (Mir & BetterC rework).
Source: $(PHOBOSSRC std/algorithm/_iteration.d)
Macros:
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
 */
module mir.algorithm.iteration;

import std.range.primitives: isInputRange, isBidirectionalRange, isInfinite, isForwardRange, ElementType;
import mir.functional: naryFun;
import mir.array.primitives;

// uniq
/**
Lazily iterates unique consecutive elements of the given range (functionality
akin to the $(HTTP wikipedia.org/wiki/_Uniq, _uniq) system
utility). Equivalence of elements is assessed by using the predicate
$(D pred), by default $(D "a == b"). The predicate is passed to
$(REF nary, mir,functional), and can either accept a string, or any callable
that can be executed via $(D pred(element, element)). If the given range is
bidirectional, $(D uniq) also yields a
`std,range,primitives`.
Params:
    pred = Predicate for determining equivalence between range elements.
    r = An input range of elements to filter.
Returns:
    An input range of
    consecutively unique elements in the original range. If `r` is also a
    forward range or bidirectional range, the returned range will be likewise.
*/
Uniq!(naryFun!pred, Range) uniq(alias pred = "a == b", Range)(auto ref Range r)
if (isInputRange!Range && is(typeof(naryFun!pred(r.front, r.front)) == bool))
{
    return typeof(return)(r);
}

///
@safe unittest
{
    import std.algorithm.comparison : equal;
    import std.algorithm.mutation : copy;

    int[] arr = [ 1, 2, 2, 2, 2, 3, 4, 4, 4, 5 ];
    assert(equal(uniq(arr), [ 1, 2, 3, 4, 5 ][]));

    // Filter duplicates in-place using copy
    arr.length -= arr.uniq().copy(arr).length;
    assert(arr == [ 1, 2, 3, 4, 5 ]);

    // Note that uniqueness is only determined consecutively; duplicated
    // elements separated by an intervening different element will not be
    // eliminated:
    assert(equal(uniq([ 1, 1, 2, 1, 1, 3, 1]), [1, 2, 1, 3, 1]));
}

///
struct Uniq(alias pred, Range)
{
    Range _input;

    // this()(auto ref Range input)
    // {
    //     import std.meta: AliasSeq;
    //     import mir.functional: forward;
    //     AliasSeq!_input = forward!input;
    // }

    auto opSlice()()
    {
        return this;
    }

    void popFront()()
    {
        assert(!empty, "Attempting to popFront an empty uniq.");
        auto last = _input.front;
        do
        {
            _input.popFront();
        }
        while (!_input.empty && pred(last, _input.front));
    }

    @property ElementType!Range front()()
    {
        assert(!empty, "Attempting to fetch the front of an empty uniq.");
        return _input.front;
    }

    static if (isBidirectionalRange!Range)
    {
        void popBack()()
        {
            assert(!empty, "Attempting to popBack an empty uniq.");
            auto last = _input.back;
            do
            {
                _input.popBack();
            }
            while (!_input.empty && pred(last, _input.back));
        }

        @property ElementType!Range back()()
        {
            assert(!empty, "Attempting to fetch the back of an empty uniq.");
            return _input.back;
        }
    }

    static if (isInfinite!Range)
    {
        enum bool empty = false;  // Propagate infiniteness.
    }
    else
    {
        @property bool empty()() { return _input.empty; }
    }

    static if (isForwardRange!Range)
    {
        @property typeof(this) save()() {
            return typeof(this)(_input.save);
        }
    }
}

version(none)
@safe unittest
{
    import std.algorithm.comparison : equal;
    import std.internal.test.dummyrange;
    import std.range;

    int[] arr = [ 1, 2, 2, 2, 2, 3, 4, 4, 4, 5 ];
    auto r = uniq(arr);
    static assert(isForwardRange!(typeof(r)));

    assert(equal(r, [ 1, 2, 3, 4, 5 ][]));
    assert(equal(retro(r), retro([ 1, 2, 3, 4, 5 ][])));

    foreach (DummyType; AllDummyRanges)
    {
        DummyType d;
        auto u = uniq(d);
        assert(equal(u, [1,2,3,4,5,6,7,8,9,10]));

        static assert(d.rt == RangeType.Input || isForwardRange!(typeof(u)));

        static if (d.rt >= RangeType.Bidirectional)
        {
            assert(equal(retro(u), [10,9,8,7,6,5,4,3,2,1]));
        }
    }
}

@safe unittest // https://issues.dlang.org/show_bug.cgi?id=17264
{
    import std.algorithm.comparison : equal;

    const(int)[] var = [0, 1, 1, 2];
    assert(var.uniq.equal([0, 1, 2]));
}
