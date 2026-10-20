// CPU_FALLBACK builds compile the CUDA sources as plain C++17 through this translation unit, so no
// compiler needs to understand the .cu extension.
#if !defined(GLIMMER_CPU_FALLBACK)
#error "cpu_fallback_unity.cpp is only part of CPU_FALLBACK builds; compile the .cu files with nvcc instead"
#endif

#include "paged_kv_indexer.cu"
#include "cuda_glue.cu"
