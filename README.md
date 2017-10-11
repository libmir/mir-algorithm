[![Dub downloads](https://img.shields.io/dub/dt/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Dub downloads](https://img.shields.io/dub/dm/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![License](https://img.shields.io/dub/l/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Bountysource](https://www.bountysource.com/badge/team?team_id=145399&style=bounties_received)](https://www.bountysource.com/teams/libmir)
[![Gitter](https://img.shields.io/gitter/room/libmir/public.svg)](https://gitter.im/libmir/public)

[![Latest version](https://img.shields.io/dub/v/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)

[![codecov.io](https://codecov.io/github/libmir/mir-algorithm/coverage.svg?branch=master)](https://codecov.io/github/libmir/mir-algorithm?branch=master)
[![Circle CI](https://circleci.com/gh/libmir/mir-algorithm.svg?style=svg)](https://circleci.com/gh/libmir/mir-algorithm)

Mir Algorithm
=============
Dlang core library for math, finance and a home for Dlang multidimensional array package - ndslice.

### Links
 - [API Documentation](http://docs.algorithm.dlang.io)
 - [Scheme of basic API (advanced)](https://rawgit.com/libmir/mir-algorithm/master/ndslice.svg)
 - [Mir Blog](http://blog.mir.dlang.io/)
 - [Lubeck](https://github.com/kaleidicassociates/lubeck) - Linear Algebra Library for Mir Algorithm

#### Example (3 sec)
```d
import mir.ndslice;

auto matrix = slice!double(3, 4);
matrix[] = 0;
matrix.diagonal[] = 1;

auto row = matrix[2];
row[3] = 6;
assert(matrix[2, 3] == 6); // D & C index order
```

#### Example (10 sec)
```d
import mir.ndslice;
import std.stdio: writefln;

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
```

### Our sponsors

[<img src="https://raw.githubusercontent.com/libmir/mir-algorithm/master/images/symmetry.png" height="80" />](http://symmetryinvestments.com/) 	&nbsp; 	&nbsp;	&nbsp;	&nbsp;
[<img src="https://raw.githubusercontent.com/libmir/mir-algorithm/master/images/kaleidic.jpeg" height="80" />](https://github.com/kaleidicassociates)

