// Keep this caller separate from the library unittests: earlier bignum
// instantiations can hide the forward reference in issue #485.
// https://github.com/libmir/mir-algorithm/issues/485
import mir.math.numeric : factorial;

@safe pure nothrow @nogc
void main()
{
    assert(cast(double) factorial(0) == 1);
    assert(cast(double) factorial(3) == 6);
    assert(cast(double) factorial(10) == 3_628_800);
    assert(cast(double) factorial(3, 4) == 120);
    assert(cast(double) factorial!256(10) == 3_628_800);
}
