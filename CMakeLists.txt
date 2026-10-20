cmake_minimum_required(VERSION 3.20)

option(CPU_FALLBACK "Build the runtime as plain C++17 without the CUDA toolkit" OFF)
option(GLIMMER_BUILD_OCAML_STUB "Build the OCaml Bigarray FFI stub (needs ocamlfind or ocamlc)" OFF)
set(GLIMMER_PTX_ARCH "sm_80" CACHE STRING "Virtual/real architecture passed to nvcc -ptx")

if(NOT CPU_FALLBACK AND NOT DEFINED CMAKE_CUDA_ARCHITECTURES)
  set(CMAKE_CUDA_ARCHITECTURES 75 80 86 89 90)
endif()

project(glimmer_verify_runtime LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set(CMAKE_BUILD_TYPE Release)
endif()

set(RT ${CMAKE_CURRENT_SOURCE_DIR}/src/runtime)

if(CPU_FALLBACK)
  add_library(glimmer_runtime SHARED ${RT}/cpu_fallback_unity.cpp)
  target_compile_definitions(glimmer_runtime PUBLIC GLIMMER_CPU_FALLBACK)
else()
  enable_language(CUDA)
  find_package(CUDAToolkit REQUIRED)
  set(CMAKE_CUDA_STANDARD 17)
  set(CMAKE_CUDA_STANDARD_REQUIRED ON)
  add_library(glimmer_runtime SHARED ${RT}/cuda_glue.cu ${RT}/paged_kv_indexer.cu)
  target_link_libraries(glimmer_runtime PUBLIC CUDA::cudart)
  target_compile_options(glimmer_runtime PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-lineinfo>)

  set(PTX_OUT ${CMAKE_BINARY_DIR}/ptx/paged_kv_indexer.ptx)
  add_custom_command(
    OUTPUT ${PTX_OUT}
    COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/ptx
    COMMAND ${CMAKE_CUDA_COMPILER} -std=c++17 -O3 -lineinfo -ptx -arch=${GLIMMER_PTX_ARCH} -I${RT}
            ${RT}/paged_kv_indexer.cu -o ${PTX_OUT}
    DEPENDS ${RT}/paged_kv_indexer.cu ${RT}/paged_kv_indexer.cuh ${RT}/cuda_compat.hpp
    COMMENT "nvcc -ptx paged_kv_indexer.cu (${GLIMMER_PTX_ARCH})"
    VERBATIM)
  add_custom_target(ptx DEPENDS ${PTX_OUT})
endif()

target_include_directories(glimmer_runtime PUBLIC ${RT})
target_compile_definitions(glimmer_runtime PRIVATE GLIMMER_BUILDING_LIBRARY)
set_target_properties(glimmer_runtime PROPERTIES PREFIX "lib" C_VISIBILITY_PRESET hidden CXX_VISIBILITY_PRESET hidden
                                                 CUDA_VISIBILITY_PRESET hidden)
if(MINGW)
  target_link_options(glimmer_runtime PRIVATE -static)
endif()
if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
  target_compile_options(glimmer_runtime PRIVATE $<$<COMPILE_LANGUAGE:CXX>:-Wall -Wextra>)
endif()

add_executable(glimmer_harness ${RT}/harness_main.cpp)
target_link_libraries(glimmer_harness PRIVATE glimmer_runtime)
if(MINGW)
  target_link_options(glimmer_harness PRIVATE -static)
endif()

enable_testing()
add_test(NAME runtime_harness COMMAND glimmer_harness)

if(GLIMMER_BUILD_OCAML_STUB)
  find_program(OCAMLFIND ocamlfind)
  find_program(OCAMLC ocamlc)
  if(OCAMLFIND)
    execute_process(COMMAND ${OCAMLFIND} ocamlc -where OUTPUT_VARIABLE OCAML_STDLIB OUTPUT_STRIP_TRAILING_WHITESPACE)
  elseif(OCAMLC)
    execute_process(COMMAND ${OCAMLC} -where OUTPUT_VARIABLE OCAML_STDLIB OUTPUT_STRIP_TRAILING_WHITESPACE)
  else()
    message(FATAL_ERROR "GLIMMER_BUILD_OCAML_STUB=ON but neither ocamlfind nor ocamlc was found")
  endif()
  add_library(glimmer_ocaml_stubs STATIC ${RT}/ocaml_c_ffi_stub.c)
  target_include_directories(glimmer_ocaml_stubs PRIVATE ${OCAML_STDLIB})
  target_link_libraries(glimmer_ocaml_stubs PUBLIC glimmer_runtime)
  set_target_properties(glimmer_ocaml_stubs PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()
