/// Math constants
module mir.math.constant;

/++
Exponent of minus Euler–Mascheroni constant.
+/
enum real expMEuler = 0x0.8fbbcf07f2e5f2c56894d7014c3086p0;

///
unittest
{
	import mir.math.func.expdigamma;
    import std.math: approxEqual;
    assert(approxEqual(expDigamma(1.0L), expMEuler));
}
