[![Bountysource](https://www.bountysource.com/badge/team?team_id=145399&style=bounties_received)](https://www.bountysource.com/teams/libmir)
[![Gitter](https://img.shields.io/gitter/room/libmir/public.svg)](https://gitter.im/libmir/public)
[![codecov.io](https://codecov.io/github/libmir/mir-algorithm/coverage.svg?branch=master)](https://codecov.io/github/libmir/mir-algorithm?branch=master)
[![Circle CI](https://circleci.com/gh/libmir/mir-algorithm.svg?style=svg)](https://circleci.com/gh/libmir/mir-algorithm)

[![Dub downloads](https://img.shields.io/dub/dt/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Dub downloads](https://img.shields.io/dub/dm/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![License](https://img.shields.io/dub/l/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Latest version](https://img.shields.io/dub/v/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)

Mir Algorithm
=============
Dlang core library for math, finance and a home for Dlang multidimensional array package - ndslice.

### Links
 - [API Documentation](http://docs.algorithm.dlang.io)
 - [Scheme of basic API (advanced)](https://rawgit.com/libmir/mir-algorithm/master/ndslice.svg)
 - [Lubeck](https://github.com/kaleidicassociates/lubeck) - Linear Algebra Library for Mir Algorithm
 - [numir](https://github.com/libmir/numir) - mir extension with numpy-like API

#### Blogs
  - [Mir Blog](http://blog.mir.dlang.io/)
  - Shigeki Karita - [D言語で数値計算 mir-algorithm](https://shigekikarita.github.io/blog/2017/09/22/026.html)

#### Example (3 sec)
```d
/+dub.sdl:
dependency "mir-algorithm" version="~>0.8.0"
+/

void main()
{
    import mir.ndslice;

    auto matrix = slice!double(3, 4);
    matrix[] = 0;
    matrix.diagonal[] = 1;

    auto row = matrix[2];
    row[3] = 6;
    assert(matrix[2, 3] == 6); // D & C index order
    
    import std.stdio;
    matrix.writeln; // [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 6]]
}
```

[![Open on run.dlang.io](https://img.shields.io/badge/run.dlang.io-open-blue.svg)](https://run.dlang.io/is/on6YTM)

#### Example (30 sec)
```d
/+dub.sdl:
dependency "mir-algorithm" version="~>0.8.0"
+/
void main()
{
    import mir.ndslice;
    import std.stdio : writefln;

    enum fmt = "%(%(%.2f %)\n%)\n";

    // Magic sqaure. 
    // `a` is lazy, each element is computed on-demand.
    auto a = magic(5).as!float;
    writefln(fmt, a);

    // 5x5 grid on sqaure [1, 2] x [0, 1] with values x * x + y. 
    // `b` is lazy, each element is computed on-demand.
    auto b = linspace!float([5, 5], [1f, 2f], [0f, 1f]).map!"a * a + b";
    writefln(fmt, b);

    // allocate a 5 x 5 contiguous matrix
    auto c = slice!float(5, 5);

    c[] = transposed(a + b / 2); // no memory allocations here
    // 1. b / 2 - lazy element-wise operation with scalars
    // 2. a + (...) - lazy element-wise operation with other slices
    // Both slices must be `contiguous` or one-dimensional.
    // 3. transposed(...) - trasposes matrix view. The result is `universal` (numpy-like) matrix.
    // 5. c[] = (...) -- performs element-wise assignment.
    writefln(fmt, c);
}
```

[![Open on run.dlang.io](https://img.shields.io/badge/run.dlang.io-open-blue.svg)](https://run.dlang.io/is/gSlbMb)

### Our sponsors

[<img src="https://raw.githubusercontent.com/libmir/mir-algorithm/master/images/symmetry.png" height="80" />](http://symmetryinvestments.com/) 	&nbsp; 	&nbsp;	&nbsp;	&nbsp;
[<img src="https://raw.githubusercontent.com/libmir/mir-algorithm/master/images/kaleidic.jpeg" height="80" />](https://github.com/kaleidicassociates)

