mir_algorithm_cpp_test_exe = executable(meson.project_name() + '-test',
    ['eye.d', 'init_rcarray.d', 'main.cpp'],
    include_directories: directories,
    dependencies: mir_algorithm_dep,
)

test(meson.project_name() + '-cpp-test', mir_algorithm_cpp_test_exe)
