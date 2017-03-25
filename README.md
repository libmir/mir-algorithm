[![Dub downloads](https://img.shields.io/dub/dt/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![License](https://img.shields.io/dub/l/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Bountysource](https://www.bountysource.com/badge/team?team_id=145399&style=bounties_received)](https://www.bountysource.com/teams/libmir)
[![Gitter](https://img.shields.io/gitter/room/libmir/public.svg)](https://gitter.im/libmir/public)

[![Latest version](https://img.shields.io/dub/v/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)

[![codecov.io](https://codecov.io/github/libmir/mir-algorithm/coverage.svg?branch=master)](https://codecov.io/github/libmir/mir-algorithm?branch=master)
[![Circle CI](https://circleci.com/gh/libmir/mir-algorithm.svg?style=svg)](https://circleci.com/gh/libmir/mir-algorithm)

# mir-algorithm

1. Generic Multidimensional arrays of three kinds
   - BLAS like - `Canonical`
   - Numpy like - `Universal`
   - `Contiguous` in memory (without strides).
2.  `std.range`, `std.functional`, and partially `std.algorithm` alternative suitable for fast executaion and multidimensional algorithms.
3. Iterators like random access iterators in C++, Fields, and ndFields.

### API Documentation

http://docs.algorithm.dlang.io

### Scheme of basic elements

https://rawgit.com/libmir/mir-algorithm/master/ndslice.svg

### Old ndslice
If you are looking for old `ndslice`, please use [the main repo](https://github.com/libmir/mir) with old tag `v0.22.1`.
