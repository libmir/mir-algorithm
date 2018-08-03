project('mir-algorithm', 'd', version : '2.0.0')

pversion = meson.project_version()
name = meson.project_name()
vname = name + '-' + pversion

the_src = [
    'source/mir/algorithm/iteration.d',
    'source/mir/algorithm/setops.d',
    'source/mir/array/allocation.d',
    'source/mir/array/primitives.d',
    'source/mir/bitmanip.d',
    'source/mir/combinatorics/package.d',
    'source/mir/container/binaryheap.d',
    'source/mir/conv.d',
    'source/mir/functional.d',
    'source/mir/graph/package.d',
    'source/mir/graph/tarjan.d',
    'source/mir/internal/memory.d',
    'source/mir/internal/utility.d',
    'source/mir/interpolate/constant.d',
    'source/mir/interpolate/linear.d',
    'source/mir/interpolate/package.d',
    'source/mir/interpolate/pchip.d',
    'source/mir/interpolate/spline.d',
    'source/mir/interpolate/utility.d',
    'source/mir/math/common.d',
    'source/mir/math/constant.d',
    'source/mir/math/func/expdigamma.d',
    'source/mir/math/numeric.d',
    'source/mir/math/package.d',
    'source/mir/math/sum.d',
    'source/mir/ndslice/algorithm.d',
    'source/mir/ndslice/allocation.d',
    'source/mir/ndslice/chunks.d',
    'source/mir/ndslice/concatenation.d',
    'source/mir/ndslice/connect/cpython.d',
    'source/mir/ndslice/dynamic.d',
    'source/mir/ndslice/field.d',
    'source/mir/ndslice/fuse.d',
    'source/mir/ndslice/internal.d',
    'source/mir/ndslice/iterator.d',
    'source/mir/ndslice/mutation.d',
    'source/mir/ndslice/ndfield.d',
    'source/mir/ndslice/package.d',
    'source/mir/ndslice/slice.d',
    'source/mir/ndslice/sorting.d',
    'source/mir/ndslice/topology.d',
    'source/mir/ndslice/traits.d',
    'source/mir/primitives.d',
    'source/mir/qualifier.d',
    'source/mir/range.d',
    'source/mir/series.d',
    'source/mir/utility.d',
    'source/std/backdoor.d',
]

mir_algorithm_lib = library(name,
    [the_src],
    install: true,
    version: pversion,
    include_directories: [include_directories('source')],
)

install_subdir('include/',
    strip_directory :true,
    install_dir: 'include/',
)

install_subdir('source/',
    strip_directory : true,
    install_dir: 'include/d/' + vname,
)

import('pkgconfig').generate(
    name: name,
    description: 'Mir Algorithm - Dlang Core Library for math and finance.',
    subdirs: 'd/' + vname,
    libraries: [mir_algorithm_lib],
    version: pversion,
)
