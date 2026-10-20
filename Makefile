# GNU make front-end for glimmer-verify.
#
#   make runtime harness CPU_FALLBACK=1   # no CUDA toolkit needed (Linux, macOS, MSYS2 mingw32-make)
#   make runtime harness CUDA_ARCH=sm_80  # CUDA build (Linux; on Windows+CUDA use CMake)
#   make ptx CUDA_ARCH=sm_80              # needs nvcc, not a GPU
#   make lean lean-bench test
#
# Recipes avoid POSIX-only shell utilities so they also run under cmd.exe (mingw32-make).

CPU_FALLBACK ?= 0
BUILD_DIR    ?= build
CUDA_ARCH    ?= sm_80
NVCC         ?= nvcc
PYTHON       ?= python
LAKE         ?= lake
OCAMLFIND    ?= ocamlfind
RUN_DIR      ?= $(lastword $(sort $(wildcard runs/*)))
AGENT_ARGS   ?=

RT       := src/runtime
LEAN_DIR := src/verification/GlimmerVerify
HEADERS  := $(wildcard $(RT)/*.hpp $(RT)/*.cuh $(RT)/*.h)

PY_MKDIR  := $(PYTHON) -c "import os,sys; [os.makedirs(d, exist_ok=True) for d in sys.argv[1:]]"
PY_RMTREE := $(PYTHON) -c "import shutil,sys; [shutil.rmtree(d, ignore_errors=True) for d in sys.argv[1:]]"

ifeq ($(OS),Windows_NT)
  LIB_FILE := libglimmer_runtime.dll
  EXE      := .exe
  PIC      :=
  STATIC   := -static
  RPATH    :=
  IMPLIB   := -Wl,--out-implib,$(BUILD_DIR)/libglimmer_runtime.dll.a
  LINK_RT  := $(BUILD_DIR)/libglimmer_runtime.dll.a
  fix_path  = $(subst /,\,$(1))
else
  ifeq ($(shell uname -s),Darwin)
    LIB_FILE := libglimmer_runtime.dylib
    RPATH    := -Wl,-rpath,@loader_path
  else
    LIB_FILE := libglimmer_runtime.so
    RPATH    := -Wl,-rpath,'$$ORIGIN'
  endif
  EXE      :=
  PIC      := -fPIC
  STATIC   :=
  IMPLIB   :=
  LINK_RT  := -L$(BUILD_DIR) -lglimmer_runtime
  fix_path  = $(1)
endif

LIB        := $(BUILD_DIR)/$(LIB_FILE)
HARNESS    := $(BUILD_DIR)/glimmer_harness$(EXE)
PTX        := $(BUILD_DIR)/ptx/paged_kv_indexer.ptx
OCAML_STUB := $(BUILD_DIR)/ocaml_c_ffi_stub.o
OCAML_WHERE = $(shell $(OCAMLFIND) ocamlc -where)

.PHONY: all runtime harness ptx ocaml-stub lean lean-bench test test-runtime test-python agent plots clean help

all: runtime harness

help:
	@echo "targets: runtime harness ptx ocaml-stub lean lean-bench test test-runtime test-python agent plots clean"
	@echo "vars:    CPU_FALLBACK=0|1 CUDA_ARCH=sm_80 BUILD_DIR=build PYTHON=python LAKE=lake RUN_DIR=runs/<id>"

runtime: $(LIB)
harness: $(HARNESS)
ptx: $(PTX)
ocaml-stub: $(OCAML_STUB)

ifeq ($(CPU_FALLBACK),1)

CXXFLAGS_RT := -std=c++17 -O2 -Wall -Wextra -DGLIMMER_CPU_FALLBACK -I$(RT)

$(LIB): $(RT)/cpu_fallback_unity.cpp $(RT)/paged_kv_indexer.cu $(RT)/cuda_glue.cu $(HEADERS)
	@$(PY_MKDIR) $(BUILD_DIR)
	$(CXX) $(CXXFLAGS_RT) $(PIC) -fvisibility=hidden -DGLIMMER_BUILDING_LIBRARY -shared $< -o $@ $(IMPLIB) $(STATIC)

$(HARNESS): $(RT)/harness_main.cpp $(LIB) $(HEADERS)
	$(CXX) $(CXXFLAGS_RT) $< -o $@ $(LINK_RT) $(RPATH) $(STATIC)

OCAML_CFLAGS := -DGLIMMER_CPU_FALLBACK

else

ifeq ($(OS),Windows_NT)
$(LIB) $(HARNESS):
	$(error CUDA builds on Windows go through CMake: cmake -S . -B build && cmake --build build --config Release)
else
NVCCFLAGS := -std=c++17 -O3 -lineinfo -arch=$(CUDA_ARCH) -I$(RT) -Xcompiler -fPIC,-fvisibility=hidden

$(LIB): $(RT)/cuda_glue.cu $(RT)/paged_kv_indexer.cu $(HEADERS)
	@$(PY_MKDIR) $(BUILD_DIR)
	$(NVCC) $(NVCCFLAGS) -DGLIMMER_BUILDING_LIBRARY -shared $(RT)/cuda_glue.cu $(RT)/paged_kv_indexer.cu -o $@

$(HARNESS): $(RT)/harness_main.cpp $(LIB) $(HEADERS)
	$(NVCC) -std=c++17 -O2 -I$(RT) $< -o $@ $(LINK_RT) -Xlinker -rpath -Xlinker '$$ORIGIN'
endif

OCAML_CFLAGS :=

endif

$(PTX): $(RT)/paged_kv_indexer.cu $(HEADERS)
	@$(PY_MKDIR) $(BUILD_DIR)/ptx
	$(NVCC) -std=c++17 -O3 -lineinfo -ptx -arch=$(CUDA_ARCH) -I$(RT) $< -o $@
	@echo "PTX written to $@"

$(OCAML_STUB): $(RT)/ocaml_c_ffi_stub.c $(RT)/glimmer_runtime.h $(LIB)
	$(CC) -O2 $(PIC) $(OCAML_CFLAGS) -I"$(OCAML_WHERE)" -I$(RT) -c $< -o $@
	@echo "link OCaml executables with: $(OCAML_STUB) $(LINK_RT)"

lean:
	cd $(call fix_path,$(LEAN_DIR)) && $(LAKE) build

lean-bench: lean
	$(PYTHON) -m pytest tests/test_lean_checker.py -v -k "library or reference"

test-runtime: $(HARNESS)
	$(call fix_path,$(HARNESS))

test-python: runtime
	$(PYTHON) -m pytest -q

test: test-runtime test-python

agent:
	$(PYTHON) -m src.agent.proof_repair_agent $(AGENT_ARGS)

plots:
	$(PYTHON) -m src.telemetry.metrics_collector plot --run-dir $(RUN_DIR) --out plots

clean:
	$(PY_RMTREE) $(BUILD_DIR)
