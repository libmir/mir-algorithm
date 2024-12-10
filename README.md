[![codecov.io](https://codecov.io/github/libmir/mir-algorithm/coverage.svg?branch=master)](https://codecov.io/github/libmir/mir-algorithm?branch=master)
[![GitHub Workflow Status](https://img.shields.io/github/actions/workflow/status/libmir/mir-algorithm/ci.yml?branch=master)](https://github.com/libmir/mir-algorithm/actions)
[![Circle CI](https://circleci.com/gh/libmir/mir-algorithm.svg?style=svg)](https://circleci.com/gh/libmir/mir-algorithm)

[![Dub downloads](https://img.shields.io/dub/dt/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Dub downloads](https://img.shields.io/dub/dm/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![License](https://img.shields.io/dub/l/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Latest version](https://img.shields.io/dub/v/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Bountysource](https://www.bountysource.com/badge/team?team_id=145399&style=bounties_received)](https://www.bountysource.com/teams/libmir)

Mir Algorithm
=============

#### [API Documentation](http://mir-algorithm.libmir.org)

#### Blogs
  - Tasty D - [Multidimensional Arrays in D](https://tastyminerals.github.io/tasty-blog/dlang/2020/03/22/multidimensional_arrays_in_d.html)
  - Tasty D - [Using External D Libraries in D Scripts and Projects](https://tastyminerals.github.io/tasty-blog/dlang/2020/03/01/how_to_use_external_libraries_in_d_project.html)
  - Tasty D - [Pretty-printing D Arrays](https://tastyminerals.github.io/tasty-blog/dlang/2020/06/25/pretty_printing_arrays.html)
  - Shigeki Karita - [D言語で数値計算 mir-algorithm](https://shigekikarita.github.io/blog/2017/09/22/026.html)
  - Shigeki Karita - [D言語(mir)でNumPyを拡張する](https://qiita.com/ShigekiKarita/items/af84b0ef864608ee1f21) (mir-pybuffer integration)
  - [Mir Blog](http://blog.mir.dlang.io/) (deprecated)

#### [Mir Type System for .NET](https://github.com/libmir/mir.net)

#### Example (3 sec)
```d
/+dub.sdl:
dependency "mir-algorithm" version="~>2.0.0"
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
    
    import mir.stdio;
    matrix.writeln;
    // prints [[1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0], [0.0, 0.0, 1.0, 6.0]]
}
```

[![Open on run.dlang.io](https://img.shields.io/badge/run.dlang.io-open-blue.svg)](https://run.dlang.io/is/OdGbCj)

#### Example (30 sec)
```d
/+dub.sdl:
dependency "mir-algorithm" version="~>2.0.0"
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

[![Open on run.dlang.io](https://img.shields.io/badge/run.dlang.io-open-blue.svg)](https://run.dlang.io/is/67Gi6X)
