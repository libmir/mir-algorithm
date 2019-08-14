project('mir-algorithm', 'cpp', 'd', version : '3.4.0', license: 'BSL-1.0',
        default_options : ['cpp_std=c++1z'])

description = 'Mir Algorithm - Dlang Core Library'

subprojects = ['mir-core']

has_cpp_headers = true

sources_list = [
    'mir/algorithm/iteration',
    'mir/algorithm/setops',
    'mir/array/allocation',
    'mir/combinatorics/package',
    'mir/container/binaryheap',
    'mir/cpp_export/numeric',
    'mir/graph/package',
    'mir/graph/tarjan',
    'mir/interpolate/constant',
    'mir/interpolate/linear',
    'mir/interpolate/package',
    'mir/interpolate/pchip',
    'mir/interpolate/spline',
    'mir/interpolate/utility',
    'mir/math/func/expdigamma',
    'mir/math/numeric',
    'mir/math/sum',
    'mir/ndslice/allocation',
    'mir/ndslice/chunks',
    'mir/ndslice/concatenation',
    'mir/ndslice/connect/cpython',
    'mir/ndslice/dynamic',
    'mir/ndslice/field',
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
    'mir/range',
    'mir/rc/array',
    'mir/rc/context',
    'mir/rc/package',
    'mir/rc/ptr',
    'mir/rc/slim_ptr',
    'mir/series',
    'mir/small_string',
    'mir/type_info',
]

sources = []
foreach s : sources_list
    sources += 'source/' + s + '.d'
endforeach

add_project_arguments([
    '-preview=dip1000',
    '-preview=dip1008',
    ], language: 'd')

required_deps = []

foreach p : subprojects 
    required_deps += dependency(p, fallback : [p, p.underscorify() + '_dep'])
endforeach

directories = ['source']

if has_cpp_headers
    directories += 'include'
endif

directories = include_directories(directories)

mir_algorithm_lib = library(meson.project_name(),
    sources,
    include_directories: directories,
    install: true,
    version: meson.project_version(),
    dependencies: required_deps,
)

mir_algorithm_dep = declare_dependency(
    link_with: [mir_algorithm_lib],
    include_directories: directories,
    dependencies: required_deps,
)

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

import('pkgconfig').generate(mir_algorithm_lib,
    description: description,
    subdirs: 'd/' + meson.project_name(),
)

if get_option('with_test')

    test_exe = executable(meson.project_name() + '-test',
        sources,
        include_directories: directories,
        d_unittest: true,
        d_module_versions: ['mir_test'],
        link_args: '-main',
        dependencies: required_deps,
    )

    test(meson.project_name() + '-test', test_exe)

    subdir('cpp_example')

endif

tags = run_command('python3', 'stable_and_latest_tags.py').stdout().split()
stable_tag = tags[0]
latest_tag = tags[1]

docs_config =  latest_tag + '.ddoc'
latest_file = custom_target('latest_target',
            build_by_default: true,
            input : [],
            output : docs_config,
            capture: true,
            command: ['echo',
                '\nLATEST=' + latest_tag +
                '\nLATEST_STABLE=' + stable_tag +
                '\nPROJECT=' + meson.project_name() +
                '\nMETA_DESCRIPTION=' + description
            ])

d_compiler = meson.get_compiler('d').get_id()
if d_compiler == 'gcc'
    d_compiler = 'gdmd'
elif d_compiler == 'llvm'
    d_compiler = 'ldmd2'
endif

root = meson.source_root()

menu = custom_target('menu_target',
            build_by_default: true,
            input : files('docgen/gen_modlist.d'),
            output : 'mir.ddoc',
            capture: true,
            command: [d_compiler, '-run', '@INPUT0@', join_paths(root, 'source')])

includes = ['-I' + join_paths(root, 'source')]
foreach sub_name : subprojects
    includes += '-I' + join_paths(root, 'subprojects', sub_name, 'source')
endforeach

extra_args = [d_compiler, '-w', '-c', '-o-',
        docs_config,
        join_paths(root, 'docgen/macros.ddoc'),
        join_paths(root, 'docgen/html.ddoc'),
        join_paths(root, 'docgen/dlang.org.ddoc'),
        join_paths(root, 'docgen/std.ddoc'),
        join_paths(root, 'docgen/custom.ddoc'),
        includes,
        '-Df@OUTPUT@', '@INPUT@']

documented_unittests = custom_target('documented_unittests',
            output: 'documented_unittests',
            command: [
                'dub',
                'run',
                'dtools:tests_extractor',
                '--build=release',
                '--',
                '-i',
                join_paths(root, 'source'),
                '-o',
                '@OUTPUT@'
            ])

i = 0
foreach source : sources_list

    test_exe = executable(source.underscorify()+'-doc',
        sources[i],
        include_directories: directories,
        d_unittest: true,
        d_module_versions: ['mir_test'],
        link_args: '-main',
        dependencies: mir_algorithm_dep,
    )

    test(source.underscorify() + '-doc-test', test_exe)

    i += 1
endforeach

htmls = []

foreach f : sources_list
    s = []
    foreach e : f.split('/')
        if e != 'package'
            s += e
        endif
    endforeach
    htmls += '_'.join(s) + '.html'
endforeach

htmls = ['index.html'] + htmls
sources = ['index.d'] + sources

i = 0
foreach source : sources
    custom_target('doc_target_' + i.to_string(),
            build_by_default: true,
            input : source,
            output : htmls[i],
            depends: [menu, latest_file],
            command: extra_args)
    i += 1
endforeach
