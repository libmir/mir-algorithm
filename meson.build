project('mir-algorithm', 'cpp', 'd', version : '3.7.0', license: 'BSL-1.0',
        default_options : ['cpp_std=c++1z'])

description = 'Mir Algorithm - Dlang Core Library'

subprojects = ['mir-core']

has_cpp_headers = true

sources_list = [
    'mir/algorithm/iteration',
    'mir/algorithm/setops',
    'mir/appender',
    'mir/array/allocation',
    'mir/combinatorics/package',
    'mir/container/binaryheap',
    'mir/cpp_export/numeric',
    'mir/exception',
    'mir/format_impl',
    'mir/format',
    'mir/graph/package',
    'mir/graph/tarjan',
    'mir/interpolate/constant',
    'mir/interpolate/linear',
    'mir/interpolate/package',
    'mir/interpolate/spline',
    'mir/interpolate/utility',
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
    'mir/series',
    'mir/small_array',
    'mir/small_string',
    'mir/type_info',
    'mir/variant',
]

sources = []
foreach s : sources_list
    sources += 'source/' + s + '.d'
endforeach

add_project_arguments([
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

test_versions = ['mir_test']

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

if get_option('with_test')

    test_exe = executable(meson.project_name() + '-test',
        sources,
        include_directories: directories,
        d_unittest: true,
        d_module_versions: test_versions,
        link_args: '-main',
        dependencies: required_deps,
    )

    test(meson.project_name() + '-test', test_exe)

    subdir('cpp_example')

endif

if get_option('with_doc')

    tags = run_command('python3', 'docgen/stable_and_latest_tags.py').stdout().split()
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
    else
        d_compiler = 'dmd'
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
            'mir.ddoc',
            join_paths(root, 'docgen/macros.ddoc'),
            join_paths(root, 'docgen/html.ddoc'),
            join_paths(root, 'docgen/dlang.org.ddoc'),
            join_paths(root, 'docgen/std.ddoc'),
            join_paths(root, 'docgen/custom.ddoc'),
            includes,
            '-Dfweb/@OUTPUT@', '@INPUT@']

    i = 0
    foreach source : sources_list

        test_name = 'documented_unittests_' + source.underscorify()
        test_source_name = test_name + '.d'

        test_source = custom_target(test_name,
            output: test_source_name,
            input: sources[i],
            capture: true,
            command: [
                'dtools_tests_extractor',
                # '--betterC',
                '-i',
                '@INPUT@',
            ]
        )

        test_exe = executable(test_name + '_exe',
            test_source,
            include_directories: directories,
            d_unittest: true,
            d_module_versions: test_versions,
            link_args: '-main',
            dependencies: this_dep,
        )

        test(source + ' documented unittest', test_exe)

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
                command: extra_args,
            )
        i += 1
    endforeach

endif
