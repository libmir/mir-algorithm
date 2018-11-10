project('mir-algorithm', 'd', version : '3.1.0', license: 'BSL-1.0')

mir_algorithm_dir = include_directories('source/', 'include/')

mir_core_dep = dependency('mir-core', fallback : ['mir-core', 'mir_core_dep'])

required_deps = [mir_core_dep]

mir_algorithm_src = [
    'source/mir/algorithm/iteration.d',
    'source/mir/algorithm/setops.d',
    'source/mir/array/allocation.d',
    'source/mir/combinatorics/package.d',
    'source/mir/container/binaryheap.d',
    'source/mir/graph/package.d',
    'source/mir/graph/tarjan.d',
    'source/mir/interpolate/constant.d',
    'source/mir/interpolate/linear.d',
    'source/mir/interpolate/package.d',
    'source/mir/interpolate/pchip.d',
    'source/mir/interpolate/spline.d',
    'source/mir/interpolate/utility.d',
    'source/mir/math/func/expdigamma.d',
    'source/mir/math/numeric.d',
    'source/mir/math/sum.d',
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
    'source/mir/range.d',
    'source/mir/rcarray.d',
    'source/mir/series.d',
]

mir_algorithm_lib = library(meson.project_name(),
    mir_algorithm_src,
    include_directories: mir_algorithm_dir,
    install: true,
    version: meson.project_version(),
    dependencies: required_deps,
)

mir_algorithm_dep = declare_dependency(
    link_with: [mir_algorithm_lib],
    include_directories: mir_algorithm_dir,
    dependencies: required_deps,
)

mir_algorithm_test_exe = executable(meson.project_name() + '-test',
    mir_algorithm_src,
    include_directories: mir_algorithm_dir,
    d_unittest: true,
    d_module_versions: ['mir_test'],
    link_args: '-main',
    dependencies: required_deps,
)

install_subdir('include/',
    strip_directory :true,
    install_dir: 'include/',
)

install_subdir('source/',
    strip_directory : true,
    install_dir: 'include/d/' + meson.project_name(),
)

import('pkgconfig').generate(
    name: meson.project_name(),
    description: 'Mir Algorithm - Dlang Core Library for Math and Finance.',
    subdirs: 'd/' + meson.project_name(),
    libraries: [mir_algorithm_lib],
    version: meson.project_version(),
)

test(meson.project_name() + '-test', mir_algorithm_test_exe)
