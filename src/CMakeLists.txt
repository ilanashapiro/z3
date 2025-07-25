################################################################################
# API header files
################################################################################
# This lists the API header files that are scanned by
# some of the build rules to generate some files needed
# by the build
set(Z3_API_HEADER_FILES_TO_SCAN
  z3_api.h
  z3_ast_containers.h
  z3_algebraic.h
  z3_polynomial.h
  z3_rcf.h
  z3_fixedpoint.h
  z3_optimization.h
  z3_fpa.h
  z3_spacer.h
)
set(Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN "")
foreach (header_file ${Z3_API_HEADER_FILES_TO_SCAN})
  set(full_path_api_header_file "${CMAKE_CURRENT_SOURCE_DIR}/api/${header_file}")
  list(APPEND Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN "${full_path_api_header_file}")
  if (NOT EXISTS "${full_path_api_header_file}")
    message(FATAL_ERROR "API header file \"${full_path_api_header_file}\" does not exist")
  endif()
endforeach()

################################################################################
# Traverse directories each adding a Z3 component
################################################################################
# I'm duplicating the order in ``mk_project.py`` for now to help us keep
# the build systems in sync.
#
# The components in these directory explicitly declare their dependencies so
# you may be able to re-order some of these directories but an error will be
# raised if you try to declare a component is dependent on another component
# that has not yet been declared.
add_subdirectory(util)
add_subdirectory(math/polynomial)
add_subdirectory(math/dd)
add_subdirectory(math/hilbert)
add_subdirectory(math/simplex)
add_subdirectory(math/automata)
add_subdirectory(math/interval)
add_subdirectory(math/realclosure)
add_subdirectory(math/subpaving)
add_subdirectory(ast)
add_subdirectory(params)
add_subdirectory(ast/rewriter)
add_subdirectory(ast/rewriter/bit_blaster)
add_subdirectory(ast/normal_forms)
add_subdirectory(ast/macros)
add_subdirectory(model)
add_subdirectory(ast/euf)
add_subdirectory(ast/converters)
add_subdirectory(ast/substitution)
add_subdirectory(ast/simplifiers)
add_subdirectory(tactic)
add_subdirectory(qe/mbp)
add_subdirectory(qe/lite)
add_subdirectory(parsers/util)
add_subdirectory(math/grobner)
add_subdirectory(sat)
add_subdirectory(nlsat)
add_subdirectory(tactic/core)
add_subdirectory(math/subpaving/tactic)
add_subdirectory(tactic/aig)
add_subdirectory(tactic/arith)
add_subdirectory(solver)
add_subdirectory(cmd_context)
add_subdirectory(cmd_context/extra_cmds)
add_subdirectory(parsers/smt2)
add_subdirectory(solver/assertions)
add_subdirectory(ast/pattern)
add_subdirectory(math/lp)
add_subdirectory(ast/sls)
add_subdirectory(sat/smt)
add_subdirectory(sat/tactic)
add_subdirectory(nlsat/tactic)
add_subdirectory(ackermannization)
add_subdirectory(ast/proofs)
add_subdirectory(ast/fpa)
add_subdirectory(smt/proto_model)
add_subdirectory(smt)
add_subdirectory(tactic/bv)
add_subdirectory(smt/tactic)
add_subdirectory(tactic/sls)
add_subdirectory(qe)
add_subdirectory(muz/base)
add_subdirectory(muz/dataflow)
add_subdirectory(muz/transforms)
add_subdirectory(muz/rel)
add_subdirectory(muz/clp)
add_subdirectory(muz/tab)
add_subdirectory(muz/bmc)
add_subdirectory(muz/ddnf)
add_subdirectory(muz/spacer)
add_subdirectory(muz/fp)
add_subdirectory(tactic/ufbv)
add_subdirectory(sat/sat_solver)
add_subdirectory(tactic/smtlogics)
add_subdirectory(tactic/fpa)
add_subdirectory(tactic/fd_solver)
add_subdirectory(tactic/portfolio)
add_subdirectory(opt)
add_subdirectory(api)
add_subdirectory(api/dll)
################################################################################
# libz3
################################################################################
get_property(Z3_LIBZ3_COMPONENTS_LIST GLOBAL PROPERTY Z3_LIBZ3_COMPONENTS)
set (object_files "")
foreach (component ${Z3_LIBZ3_COMPONENTS_LIST})
  list(APPEND object_files $<TARGET_OBJECTS:${component}>)
endforeach()
if (Z3_BUILD_LIBZ3_SHARED)
  set(lib_type "SHARED")
else()
  set(lib_type "STATIC")
endif()
# Enable static msvc runtime.
if (MSVC AND Z3_BUILD_LIBZ3_MSVC_STATIC)
    set(CompilerFlags
        CMAKE_CXX_FLAGS
        CMAKE_CXX_FLAGS_DEBUG
        CMAKE_CXX_FLAGS_RELEASE
        CMAKE_CXX_FLAGS_MINSIZEREL
        CMAKE_CXX_FLAGS_RELWITHDEBINFO
        CMAKE_C_FLAGS
        CMAKE_C_FLAGS_DEBUG
        CMAKE_C_FLAGS_RELEASE
        CMAKE_C_FLAGS_MINSIZEREL
        CMAKE_C_FLAGS_RELWITHDEBINFO
        )
    foreach(CompilerFlag ${CompilerFlags})
        string(REPLACE "/MD" "/MT" ${CompilerFlag} "${${CompilerFlag}}")
        string(REPLACE "/MDd" "/MTd" ${CompilerFlag} "${${CompilerFlag}}")
        set(${CompilerFlag} "${${CompilerFlag}}" CACHE STRING "msvc compiler flags" FORCE)
        message("MSVC flags: ${CompilerFlag}:${${CompilerFlag}}")
    endforeach()
endif()
add_library(libz3 ${lib_type} ${object_files})
target_include_directories(libz3 INTERFACE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/api>
  $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)
set_target_properties(libz3 PROPERTIES
  # VERSION determines the version in the filename of the shared library.
  # SOVERSION determines the value of the DT_SONAME field on ELF platforms.
  # On ELF platforms the final compiled filename will be libz3.so.W.X.Y.Z
  # but symlinks will be made to this file from libz3.so and also from
  # libz3.so.W.X.
  # This indicates that no breaking API changes will be made within a single
  # minor version.
  VERSION ${Z3_VERSION}
  SOVERSION ${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR})

if (NOT MSVC)
  # On UNIX like platforms if we don't change the OUTPUT_NAME
  # the library gets a name like ``liblibz3.so`` so we change it
  # here. We don't do a rename with MSVC because we get file naming
  # conflicts (the z3 executable also has this OUTPUT_NAME) with
  # ``.ilk``, ``.pdb``, ``.lib`` and ``.exp`` files sharing the same
  # prefix.
  set_target_properties(libz3 PROPERTIES OUTPUT_NAME z3)
endif()

# The `PRIVATE` usage requirement is specified so that when building Z3 as a
# shared library the dependent libraries are specified on the link command line
# so that if those are also shared libraries they are referenced by `libz3.so`.
target_link_libraries(libz3 PRIVATE ${Z3_DEPENDENT_LIBS})

# This is currently only for the OpenMP flags. It needs to be set
# via `target_link_libraries()` rather than `z3_append_linker_flag_list_to_target()`
# because when building the `libz3` as a static library when the target is exported
# the link dependencies need to be exported too.
foreach (flag_name ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
  target_link_libraries(libz3 PRIVATE ${flag_name})
endforeach()

# Declare which header file are the public header files of libz3
# these will automatically installed when the libz3 target is installed
set (libz3_public_headers
  z3_algebraic.h
  z3_api.h
  z3_ast_containers.h
  z3_fixedpoint.h
  z3_fpa.h
  z3.h
  c++/z3++.h
  z3_macros.h
  z3_optimization.h
  z3_polynomial.h
  z3_rcf.h
  z3_v1.h
  z3_spacer.h
)
foreach (header ${libz3_public_headers})
  set_property(TARGET libz3 APPEND PROPERTY
    PUBLIC_HEADER "${PROJECT_SOURCE_DIR}/src/api/${header}")
endforeach()
set_property(TARGET libz3 APPEND PROPERTY
    PUBLIC_HEADER "${CMAKE_CURRENT_BINARY_DIR}/util/z3_version.h")

install(TARGETS libz3
  EXPORT Z3_EXPORTED_TARGETS
  LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
  ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}" # On Windows this installs ``libz3.lib`` which CMake calls the "corresponding import library". Do we want this installed?
  RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}" # For Windows. DLLs are runtime targets for CMake
  PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
)

if (MSVC)
  # Handle settings dll exports when using MSVC
  # FIXME: This seems unnecessarily complicated but I'm doing
  # this because this is what the python build system does.
  # CMake has a much more elegant (see ``GenerateExportHeader.cmake``)
  # way of handling this.
  set(dll_module_exports_file "${CMAKE_CURRENT_BINARY_DIR}/api_dll.def")
  add_custom_command(OUTPUT "${dll_module_exports_file}"
    COMMAND
      "${Python3_EXECUTABLE}"
      "${PROJECT_SOURCE_DIR}/scripts/mk_def_file.py"
      "${dll_module_exports_file}"
      "libz3"
      ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    DEPENDS
      "${PROJECT_SOURCE_DIR}/scripts/mk_def_file.py"
      ${Z3_GENERATED_FILE_EXTRA_DEPENDENCIES}
      ${Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN}
    COMMENT "Generating \"${dll_module_exports_file}\""
    USES_TERMINAL
    VERBATIM
  )
  add_custom_target(libz3_extra_depends
    DEPENDS "${dll_module_exports_file}"
  )
  add_dependencies(libz3 libz3_extra_depends)
  z3_append_linker_flag_list_to_target(libz3 "/DEF:${dll_module_exports_file}")
endif()

################################################################################
# Z3 executable
################################################################################
cmake_dependent_option(Z3_BUILD_EXECUTABLE
    "Build the z3 executable" ON
    "CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR" OFF)

if (Z3_BUILD_EXECUTABLE)
    add_subdirectory(shell)
endif()

################################################################################
# z3-test
################################################################################

cmake_dependent_option(Z3_BUILD_TEST_EXECUTABLES
    "Build test executables" ON
    "CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR" OFF)


if (Z3_BUILD_TEST_EXECUTABLES)
    add_subdirectory(test)
endif()


################################################################################
# Z3 API bindings
################################################################################
option(Z3_BUILD_PYTHON_BINDINGS "Build Python bindings for Z3" OFF)
if (Z3_BUILD_PYTHON_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The python bindings will not work with a static libz3. "
            "You either need to disable Z3_BUILD_PYTHON_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/python)
endif()

################################################################################
# .NET bindings
################################################################################
option(Z3_BUILD_DOTNET_BINDINGS "Build .NET bindings for Z3" OFF)
if (Z3_BUILD_DOTNET_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The .NET bindings will not work with a static libz3. "
      "You either need to disable Z3_BUILD_DOTNET_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/dotnet)
endif()

################################################################################
# Java bindings
################################################################################
option(Z3_BUILD_JAVA_BINDINGS "Build Java bindings for Z3" OFF)
if (Z3_BUILD_JAVA_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The Java bindings will not work with a static libz3. "
      "You either need to disable Z3_BUILD_JAVA_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/java)
endif()

################################################################################
# OCaml bindings
################################################################################
option(Z3_BUILD_OCAML_BINDINGS "Build OCaml bindings for Z3" OFF)
if (Z3_BUILD_OCAML_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The OCaml bindings will not work with a static libz3. "
      "You either need to disable Z3_BUILD_OCAML_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/ml)
endif()

################################################################################
# Julia bindings
################################################################################
option(Z3_BUILD_JULIA_BINDINGS "Build Julia bindings for Z3" OFF)
if (Z3_BUILD_JULIA_BINDINGS)
  if (NOT Z3_BUILD_LIBZ3_SHARED)
    message(FATAL_ERROR "The Julia bindings will not work with a static libz3."
      "You either need to disable Z3_BUILD_JULIA_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
  endif()
  add_subdirectory(api/julia)
endif()

# TODO: Implement support for other bindigns
