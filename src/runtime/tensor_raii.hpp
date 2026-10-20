// RAII ownership for CUDA device memory, page-locked host memory, host-memory registration,
// and streams. Every acquisition happens in a constructor and every release in a destructor,
// so early returns and exceptions cannot leak VRAM or pinned pages.
#pragma once

#include "cuda_compat.hpp"

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>

namespace glimmer {

class CudaError final : public std::runtime_error {
 public:
  CudaError(cudaError_t code, const char* expr, const char* file, int line)
      : std::runtime_error(std::string(file) + ":" + std::to_string(line) + ": " + expr +
                           " failed: " + cudaGetErrorString(code)),
        code_(code) {}

  cudaError_t code() const noexcept { return code_; }

 private:
  cudaError_t code_;
};

#define GLIMMER_CUDA_CHECK(expr)                                                \
  do {                                                                          \
    const cudaError_t glimmer_status_ = (expr);                                 \
    if (glimmer_status_ != cudaSuccess)                                         \
      throw ::glimmer::CudaError(glimmer_status_, #expr, __FILE__, __LINE__);   \
  } while (0)

namespace detail {

// Per binary: the shared library and an executable that includes this header each keep their own.
inline std::atomic<std::int64_t> g_live_device_bytes{0};
inline std::atomic<std::int64_t> g_live_pinned_bytes{0};

template <typename T>
std::size_t checked_bytes(std::size_t count) {
  if (count > std::numeric_limits<std::size_t>::max() / sizeof(T)) {
    throw std::length_error("glimmer: allocation size overflows size_t");
  }
  return count * sizeof(T);
}

}  // namespace detail

inline std::int64_t live_device_bytes() noexcept {
  return detail::g_live_device_bytes.load(std::memory_order_relaxed);
}
inline std::int64_t live_pinned_bytes() noexcept {
  return detail::g_live_pinned_bytes.load(std::memory_order_relaxed);
}

// Owning handle to `count` elements of device memory. The handle itself is a pointer and a size.
template <typename T>
class DeviceTensor {
  static_assert(std::is_trivially_copyable_v<T>, "DeviceTensor elements are moved with cudaMemcpy");

 public:
  DeviceTensor() noexcept = default;

  explicit DeviceTensor(std::size_t count) {
    const std::size_t nbytes = detail::checked_bytes<T>(count);
    if (nbytes == 0) return;
    void* raw = nullptr;
    GLIMMER_CUDA_CHECK(cudaMalloc(&raw, nbytes));
    ptr_ = static_cast<T*>(raw);
    count_ = count;
    detail::g_live_device_bytes.fetch_add(static_cast<std::int64_t>(nbytes), std::memory_order_relaxed);
  }

  ~DeviceTensor() { reset(); }

  DeviceTensor(const DeviceTensor&) = delete;
  DeviceTensor& operator=(const DeviceTensor&) = delete;

  DeviceTensor(DeviceTensor&& other) noexcept
      : ptr_(std::exchange(other.ptr_, nullptr)), count_(std::exchange(other.count_, 0)) {}

  DeviceTensor& operator=(DeviceTensor&& other) noexcept {
    if (this != &other) {
      reset();
      ptr_ = std::exchange(other.ptr_, nullptr);
      count_ = std::exchange(other.count_, 0);
    }
    return *this;
  }

  T* data() noexcept { return ptr_; }
  const T* data() const noexcept { return ptr_; }
  std::size_t size() const noexcept { return count_; }
  std::size_t bytes() const noexcept { return count_ * sizeof(T); }
  bool empty() const noexcept { return count_ == 0; }

  void reset() noexcept {
    if (ptr_ != nullptr) {
      static_cast<void>(cudaFree(ptr_));
      detail::g_live_device_bytes.fetch_sub(static_cast<std::int64_t>(bytes()), std::memory_order_relaxed);
    }
    ptr_ = nullptr;
    count_ = 0;
  }

  // H2D. `src` should be pinned (PinnedHostBuffer / HostRegistration) for the copy to be truly async.
  void upload_async(const T* src, std::size_t count, cudaStream_t stream) {
    require_fits(count);
    if (count == 0) return;
    GLIMMER_CUDA_CHECK(cudaMemcpyAsync(ptr_, src, count * sizeof(T), cudaMemcpyHostToDevice, stream));
  }

  // D2H.
  void download_async(T* dst, std::size_t count, cudaStream_t stream) const {
    require_fits(count);
    if (count == 0) return;
    GLIMMER_CUDA_CHECK(cudaMemcpyAsync(dst, ptr_, count * sizeof(T), cudaMemcpyDeviceToHost, stream));
  }

 private:
  void require_fits(std::size_t count) const {
    if (count > count_) throw std::out_of_range("glimmer: copy larger than DeviceTensor");
  }

  T* ptr_ = nullptr;
  std::size_t count_ = 0;
};

static_assert(sizeof(DeviceTensor<float>) == sizeof(float*) + sizeof(std::size_t),
              "DeviceTensor must stay a (pointer, size) handle");

// Owning handle to page-locked host memory (cudaMallocHost). The OS cannot page it out, so the
// DMA engine can read and write it directly for full-bandwidth async H2D/D2H transfers.
template <typename T>
class PinnedHostBuffer {
  static_assert(std::is_trivially_copyable_v<T>, "PinnedHostBuffer elements are moved by DMA");

 public:
  PinnedHostBuffer() noexcept = default;

  explicit PinnedHostBuffer(std::size_t count) {
    const std::size_t nbytes = detail::checked_bytes<T>(count);
    if (nbytes == 0) return;
    void* raw = nullptr;
    GLIMMER_CUDA_CHECK(cudaMallocHost(&raw, nbytes));
    ptr_ = static_cast<T*>(raw);
    count_ = count;
    detail::g_live_pinned_bytes.fetch_add(static_cast<std::int64_t>(nbytes), std::memory_order_relaxed);
  }

  ~PinnedHostBuffer() { reset(); }

  PinnedHostBuffer(const PinnedHostBuffer&) = delete;
  PinnedHostBuffer& operator=(const PinnedHostBuffer&) = delete;

  PinnedHostBuffer(PinnedHostBuffer&& other) noexcept
      : ptr_(std::exchange(other.ptr_, nullptr)), count_(std::exchange(other.count_, 0)) {}

  PinnedHostBuffer& operator=(PinnedHostBuffer&& other) noexcept {
    if (this != &other) {
      reset();
      ptr_ = std::exchange(other.ptr_, nullptr);
      count_ = std::exchange(other.count_, 0);
    }
    return *this;
  }

  T* data() noexcept { return ptr_; }
  const T* data() const noexcept { return ptr_; }
  std::size_t size() const noexcept { return count_; }
  std::size_t bytes() const noexcept { return count_ * sizeof(T); }
  T& operator[](std::size_t i) noexcept { return ptr_[i]; }
  const T& operator[](std::size_t i) const noexcept { return ptr_[i]; }
  T* begin() noexcept { return ptr_; }
  T* end() noexcept { return ptr_ + count_; }

  void reset() noexcept {
    if (ptr_ != nullptr) {
      static_cast<void>(cudaFreeHost(ptr_));
      detail::g_live_pinned_bytes.fetch_sub(static_cast<std::int64_t>(bytes()), std::memory_order_relaxed);
    }
    ptr_ = nullptr;
    count_ = 0;
  }

 private:
  T* ptr_ = nullptr;
  std::size_t count_ = 0;
};

// Page-locks caller-owned memory for the lifetime of the object (cudaHostRegister). With
// cudaHostRegisterMapped the GPU addresses it directly over PCIe/NVLink: zero copies.
class HostRegistration {
 public:
  HostRegistration() noexcept = default;

  HostRegistration(const void* host, std::size_t bytes, unsigned int flags = cudaHostRegisterMapped) {
    void* mutable_host = const_cast<void*>(host);
    device_ = mutable_host;
    if (mutable_host == nullptr || bytes == 0) return;

    const cudaError_t err = cudaHostRegister(mutable_host, bytes, flags);
    if (err == cudaErrorHostMemoryAlreadyRegistered) {
      static_cast<void>(cudaGetLastError());
    } else {
      GLIMMER_CUDA_CHECK(err);
      registered_ = mutable_host;
    }

    if ((flags & cudaHostRegisterMapped) != 0) {
      const cudaError_t map_err = cudaHostGetDevicePointer(&device_, mutable_host, 0);
      if (map_err != cudaSuccess) {
        release();
        GLIMMER_CUDA_CHECK(map_err);
      }
    }
  }

  ~HostRegistration() { release(); }

  HostRegistration(const HostRegistration&) = delete;
  HostRegistration& operator=(const HostRegistration&) = delete;

  HostRegistration(HostRegistration&& other) noexcept
      : registered_(std::exchange(other.registered_, nullptr)), device_(std::exchange(other.device_, nullptr)) {}

  HostRegistration& operator=(HostRegistration&& other) noexcept {
    if (this != &other) {
      release();
      registered_ = std::exchange(other.registered_, nullptr);
      device_ = std::exchange(other.device_, nullptr);
    }
    return *this;
  }

  template <typename T>
  T* device_ptr() const noexcept {
    return static_cast<T*>(device_);
  }

 private:
  void release() noexcept {
    if (registered_ != nullptr) static_cast<void>(cudaHostUnregister(registered_));
    registered_ = nullptr;
  }

  void* registered_ = nullptr;
  void* device_ = nullptr;
};

class CudaStream {
 public:
  CudaStream() { GLIMMER_CUDA_CHECK(cudaStreamCreateWithFlags(&stream_, cudaStreamNonBlocking)); }
  ~CudaStream() {
    if (stream_ != nullptr) static_cast<void>(cudaStreamDestroy(stream_));
  }

  CudaStream(const CudaStream&) = delete;
  CudaStream& operator=(const CudaStream&) = delete;
  CudaStream(CudaStream&&) = delete;
  CudaStream& operator=(CudaStream&&) = delete;

  cudaStream_t get() const noexcept { return stream_; }
  void synchronize() const { GLIMMER_CUDA_CHECK(cudaStreamSynchronize(stream_)); }

 private:
  cudaStream_t stream_ = nullptr;
};

}  // namespace glimmer
