// Single switch point between the CUDA runtime and the host-only CPU_FALLBACK build.
//
// With GLIMMER_CPU_FALLBACK defined, the subset of the CUDA runtime API used by this repo is
// implemented on host memory and kernels are executed by `glimmer::compat::cpu_launch`.
#pragma once

#include <cstddef>
#include <cstdint>

#if defined(GLIMMER_CPU_FALLBACK)

#include <cstdlib>
#include <cstring>

using cudaError_t = int;
enum : int {
  cudaSuccess = 0,
  cudaErrorInvalidValue = 1,
  cudaErrorMemoryAllocation = 2,
  cudaErrorInvalidConfiguration = 9,
  cudaErrorHostMemoryAlreadyRegistered = 712,
};

enum cudaMemcpyKind {
  cudaMemcpyHostToHost = 0,
  cudaMemcpyHostToDevice = 1,
  cudaMemcpyDeviceToHost = 2,
  cudaMemcpyDeviceToDevice = 3,
  cudaMemcpyDefault = 4,
};

struct CUstream_st;
using cudaStream_t = CUstream_st*;

inline constexpr unsigned int cudaHostRegisterDefault = 0x00;
inline constexpr unsigned int cudaHostRegisterMapped = 0x02;
inline constexpr unsigned int cudaStreamNonBlocking = 0x01;

namespace glimmer::compat {
inline thread_local cudaError_t g_last_error = cudaSuccess;
}  // namespace glimmer::compat

inline cudaError_t cudaMalloc(void** ptr, std::size_t bytes) {
  if (ptr == nullptr) return cudaErrorInvalidValue;
  *ptr = std::malloc(bytes == 0 ? 1 : bytes);
  return *ptr != nullptr ? cudaSuccess : cudaErrorMemoryAllocation;
}
inline cudaError_t cudaFree(void* ptr) {
  std::free(ptr);
  return cudaSuccess;
}
inline cudaError_t cudaMallocHost(void** ptr, std::size_t bytes) { return cudaMalloc(ptr, bytes); }
inline cudaError_t cudaFreeHost(void* ptr) { return cudaFree(ptr); }

inline cudaError_t cudaMemcpy(void* dst, const void* src, std::size_t bytes, cudaMemcpyKind) {
  if (bytes != 0 && (dst == nullptr || src == nullptr)) return cudaErrorInvalidValue;
  if (bytes != 0) std::memcpy(dst, src, bytes);
  return cudaSuccess;
}
inline cudaError_t cudaMemcpyAsync(void* dst, const void* src, std::size_t bytes, cudaMemcpyKind kind,
                                   cudaStream_t) {
  return cudaMemcpy(dst, src, bytes, kind);
}

inline cudaError_t cudaStreamCreateWithFlags(cudaStream_t* stream, unsigned int) {
  if (stream == nullptr) return cudaErrorInvalidValue;
  *stream = nullptr;
  return cudaSuccess;
}
inline cudaError_t cudaStreamSynchronize(cudaStream_t) { return cudaSuccess; }
inline cudaError_t cudaStreamDestroy(cudaStream_t) { return cudaSuccess; }
inline cudaError_t cudaDeviceSynchronize() { return cudaSuccess; }

inline cudaError_t cudaHostRegister(void* ptr, std::size_t, unsigned int) {
  return ptr != nullptr ? cudaSuccess : cudaErrorInvalidValue;
}
inline cudaError_t cudaHostUnregister(void*) { return cudaSuccess; }
inline cudaError_t cudaHostGetDevicePointer(void** device, void* host, unsigned int) {
  if (device == nullptr) return cudaErrorInvalidValue;
  *device = host;
  return cudaSuccess;
}

inline cudaError_t cudaGetLastError() {
  const cudaError_t err = glimmer::compat::g_last_error;
  glimmer::compat::g_last_error = cudaSuccess;
  return err;
}

inline const char* cudaGetErrorString(cudaError_t err) {
  switch (err) {
    case cudaSuccess: return "no error (cpu_fallback)";
    case cudaErrorInvalidValue: return "invalid argument (cpu_fallback)";
    case cudaErrorMemoryAllocation: return "out of memory (cpu_fallback)";
    case cudaErrorInvalidConfiguration: return "invalid configuration argument (cpu_fallback)";
    case cudaErrorHostMemoryAlreadyRegistered: return "host memory already registered (cpu_fallback)";
    default: return "unknown error (cpu_fallback)";
  }
}

struct dim3 {
  unsigned int x, y, z;
  constexpr dim3(unsigned int vx = 1, unsigned int vy = 1, unsigned int vz = 1) noexcept
      : x(vx), y(vy), z(vz) {}
};

inline thread_local dim3 threadIdx{0, 0, 0};
inline thread_local dim3 blockIdx{0, 0, 0};
inline thread_local dim3 blockDim{1, 1, 1};
inline thread_local dim3 gridDim{1, 1, 1};

#define GLIMMER_KERNEL
#define GLIMMER_DEVICE inline
#define GLIMMER_LDG(ptr) (*(ptr))
#if defined(_MSC_VER)
#define GLIMMER_RESTRICT __restrict
#else
#define GLIMMER_RESTRICT __restrict__
#endif

namespace glimmer::compat {

// Threads run one after another, so only kernels without __syncthreads(), shared memory, or warp
// intrinsics may be launched through this path.
template <typename Kernel, typename... Args>
void cpu_launch(dim3 grid, dim3 block, Kernel&& kernel, Args&&... args) {
  if (grid.x == 0 || grid.y == 0 || grid.z == 0 || block.x == 0 || block.y == 0 || block.z == 0) {
    g_last_error = cudaErrorInvalidConfiguration;
    return;
  }
  gridDim = grid;
  blockDim = block;
  for (unsigned int bz = 0; bz < grid.z; ++bz)
    for (unsigned int by = 0; by < grid.y; ++by)
      for (unsigned int bx = 0; bx < grid.x; ++bx) {
        blockIdx = dim3(bx, by, bz);
        for (unsigned int tz = 0; tz < block.z; ++tz)
          for (unsigned int ty = 0; ty < block.y; ++ty)
            for (unsigned int tx = 0; tx < block.x; ++tx) {
              threadIdx = dim3(tx, ty, tz);
              kernel(args...);
            }
      }
}

}  // namespace glimmer::compat

#define GLIMMER_LAUNCH(kernel, grid, block, smem, stream, ...)            \
  do {                                                                    \
    (void)(smem);                                                         \
    (void)(stream);                                                       \
    ::glimmer::compat::cpu_launch((grid), (block), kernel, __VA_ARGS__);  \
  } while (0)

#else  // CUDA

#include <cuda_runtime.h>

#define GLIMMER_KERNEL __global__
#define GLIMMER_DEVICE __device__ __forceinline__
#define GLIMMER_LDG(ptr) __ldg(ptr)
#define GLIMMER_RESTRICT __restrict__

#define GLIMMER_LAUNCH(kernel, grid, block, smem, stream, ...) \
  kernel<<<(grid), (block), (smem), (stream)>>>(__VA_ARGS__)

#endif
