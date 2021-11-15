project('mir-algorithm', 'cpp', 'd', version : '3.7.0', license: 'Apache-2.0',
        default_options : ['cpp_std=c++1z'])

description = 'Mir Algorithm - Dlang Core Library'

subprojects = ['mir-core']

has_cpp_headers = true

sources_list = [
    'mir/algebraic_alias/ion',
    'mir/algebraic_alias/json',
    'mir/algorithm/iteration',
    'mir/algorithm/setops',
    'mir/annotated',
    'mir/appender',
    'mir/array/allocation',
    'mir/bignum/decimal',
    'mir/bignum/fixed',
    'mir/bignum/fp',
    'mir/bignum/integer',
    'mir/bignum/internal/dec2flt_table',
    'mir/bignum/internal/ryu/generic_128',
    'mir/bignum/low_level_view',
    'mir/combinatorics/package',
    'mir/container/binaryheap',
    'mir/cpp_export/numeric',
    'mir/date',
    'mir/format_impl',
    'mir/format',
    'mir/graph/package',
    'mir/graph/tarjan',
    'mir/interpolate/constant',
    'mir/interpolate/generic',
    'mir/interpolate/linear',
    'mir/interpolate/package',
    'mir/interpolate/polynomial',
    'mir/interpolate/spline',
    'mir/interpolate/utility',
    'mir/lob',
    'mir/math/func/expdigamma',
    'mir/math/numeric',
    'mir/math/stat',
    'mir/math/sum',
    'mir/ndslice/allocation',
    'mir/ndslice/chunks',
    'mir/ndslice/concatenation',
    'mir/ndslice/connect/cpython',
    'mir/ndslice/dynamic',
    'mir/ndslice/field',
    'mir/ndslice/filling',
    'mir/ndslice/fuse',
    'mir/ndslice/internal',
    'mir/ndslice/iterator',
    'mir/ndslice/mutation',
    'mir/ndslice/ndfield',
    'mir/ndslice/package',
    'mir/ndslice/slice',
    'mir/ndslice/sorting',
    'mir/ndslice/topology',
    'mir/ndslice/traits',
    'mir/numeric',
    'mir/parse',
    'mir/polynomial',
    'mir/range',
    'mir/rc/array',
    'mir/rc/context',
    'mir/rc/package',
    'mir/rc/ptr',
    'mir/rc/slim_ptr',
    'mir/serde',
    'mir/series',
    'mir/small_array',
    'mir/small_string',
    'mir/string_map',
    'mir/timestamp',
    'mir/type_info',
]

sources = []
foreach s : sources_list
    sources += 'source/' + s + '.d'
endforeach

add_project_arguments([
    '-preview=dip1008',
    '-lowmem',
], language: 'd')

required_deps = []

foreach p : subprojects 
    required_deps += dependency(p, fallback : [p, 'this_dep'])
endforeach

directories = ['source']

if has_cpp_headers
    directories += 'include'
endif

directories = include_directories(directories)

this_lib = library(meson.project_name(),
    sources,
    include_directories: directories,
    install: true,
    version: meson.project_version(),
    dependencies: required_deps,
)

this_dep = declare_dependency(
    link_with: [this_lib],
    include_directories: directories,
    dependencies: required_deps,
)

test_versions = ['mir_test', 'mir_bignum_test', 'mir_secure_memory']

if has_cpp_headers
    install_subdir('include/',
        strip_directory :true,
        install_dir: 'include/',
    )
endif

install_subdir('source/',
    strip_directory : true,
    install_dir: 'include/d/' + meson.project_name(),
)

import('pkgconfig').generate(this_lib,
    description: description,
    subdirs: 'd/' + meson.project_name(),
)

mir_algorithm_dep = this_dep
mir_algorithm_lib = this_lib

test_subdirs = ['cpp_example']
