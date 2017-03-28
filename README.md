[![Dub downloads](https://img.shields.io/dub/dt/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![License](https://img.shields.io/dub/l/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)
[![Bountysource](https://www.bountysource.com/badge/team?team_id=145399&style=bounties_received)](https://www.bountysource.com/teams/libmir)
[![Gitter](https://img.shields.io/gitter/room/libmir/public.svg)](https://gitter.im/libmir/public)

[![Latest version](https://img.shields.io/dub/v/mir-algorithm.svg)](http://code.dlang.org/packages/mir-algorithm)

[![codecov.io](https://codecov.io/github/libmir/mir-algorithm/coverage.svg?branch=master)](https://codecov.io/github/libmir/mir-algorithm?branch=master)
[![Circle CI](https://circleci.com/gh/libmir/mir-algorithm.svg?style=svg)](https://circleci.com/gh/libmir/mir-algorithm)

# mir-algorithm

New ndslice comes with a lot of new features

  - [mir.ndslice.topology](http://docs.algorithm.dlang.io/latest/mir_ndslice_topology.html) - Multidimensional `std.range` analog. Includes `bitwise`, `bitpack`, `zip`, `unzip`, `map`, `indexed` and many other features.)
  - [mir.ndslice.concatenation](http://docs.algorithm.dlang.io/latest/mir_ndslice_concatenation.html) - Concatenation and padding)
  - [mir.ndslice.algorithm](http://docs.algorithm.dlang.io/latest/mir_ndslice_algorithm.html) - Slim multidimensional `std.algorithm` analog)
  - [mir.ndslice.sorting](http://docs.algorithm.dlang.io/latest/mir_ndslice_sorting.html) - Multidimensional sorting utilities)

`ndslice` design was changed. New ndslices can be created on top of random access iterators including pointers. There are three kinds of ndslice:

 - `Contiguous` - Contiguous in memory representation. It does not store strides and can be always flattened to 1 dimensional ndslice on top of the same iterator type.
 - `Canonical` - BLAS like. Stride for row dimension assumed to be equal to 1.
 - `Universal` - Numpy like. Each dimension has strides. All dimensions can be exchanged without reallocation. The old ndslice ABI corresponds to to the `Universal` ndslice.

1. Generic Multidimensional arrays of three kinds
   - BLAS like - `Canonical`
   - Numpy like - `Universal`
   - `Contiguous` in memory (without strides).
2.  `std.range`, `std.functional`, and partially `std.algorithm` alternative suitable for fast executaion and multidimensional algorithms.
3. Iterators like random access iterators in C++, Fields, and ndFields.

### Known bugs
- With LDC <=1.1.0 `mir.ndslice.topology.map` may not work because LDC has deprecated DMD FE.
- With LDC ==1.2.0-beta1 compiled with LLVM 4.0 some code from `mir.algorithm` may not work because https://github.com/ldc-developers/ldc/issues/2037.

### API Documentation

http://docs.algorithm.dlang.io

### Scheme of basic elements

https://rawgit.com/libmir/mir-algorithm/master/ndslice.svg

### Old ndslice
If you are looking for old `ndslice`, please use [the main repo](https://github.com/libmir/mir) with old tag `v0.22.1`.
