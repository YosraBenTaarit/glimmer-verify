// C ABI over the RAII runtime: staged (pinned -> device) and zero-copy (mapped host) data paths.
#include "glimmer_runtime.h"
#include "paged_kv_indexer.cuh"
#include "tensor_raii.hpp"

#include <cstring>
#include <new>
#include <stdexcept>
#include <string>

namespace {

thread_local std::string g_last_error;

template <typename Fn>
int guarded(Fn&& fn) noexcept {
  try {
    fn();
    g_last_error.clear();
    return GLIMMER_OK;
  } catch (const glimmer::CudaError& e) {
    g_last_error = e.what();
    return e.code() == cudaErrorMemoryAllocation ? GLIMMER_ERR_OUT_OF_MEMORY : GLIMMER_ERR_CUDA;
  } catch (const std::bad_alloc&) {
    g_last_error = "host allocation failed";
    return GLIMMER_ERR_OUT_OF_MEMORY;
  } catch (const std::logic_error& e) {
    g_last_error = e.what();
    return GLIMMER_ERR_INVALID_ARGUMENT;
  } catch (const std::exception& e) {
    g_last_error = e.what();
    return GLIMMER_ERR_INTERNAL;
  } catch (...) {
    g_last_error = "unknown exception";
    return GLIMMER_ERR_INTERNAL;
  }
}

void validate_index_args(const std::int32_t* block_tables, std::int32_t num_reqs, std::int32_t max_blocks_per_req,
                         std::int32_t num_physical_blocks, const std::int32_t* req_ids,
                         const std::int32_t* token_pos, std::int32_t n_queries, const std::int64_t* out_slots) {
  if (num_reqs < 0 || max_blocks_per_req < 0 || num_physical_blocks < 0 || n_queries < 0) {
    throw std::invalid_argument("glimmer_paged_kv_index: dimensions must be non-negative");
  }
  if (num_reqs > 0 && max_blocks_per_req > 0 && block_tables == nullptr) {
    throw std::invalid_argument("glimmer_paged_kv_index: block_tables is null");
  }
  if (n_queries > 0 && (req_ids == nullptr || token_pos == nullptr || out_slots == nullptr)) {
    throw std::invalid_argument("glimmer_paged_kv_index: query buffers are null");
  }
}

std::size_t table_elems(std::int32_t num_reqs, std::int32_t max_blocks_per_req) {
  return static_cast<std::size_t>(num_reqs) * static_cast<std::size_t>(max_blocks_per_req);
}

}  // namespace

extern "C" {

GLIMMER_API const char* glimmer_backend_name(void) {
#if defined(GLIMMER_CPU_FALLBACK)
  return "cpu_fallback";
#else
  return "cuda";
#endif
}

GLIMMER_API const char* glimmer_last_error(void) { return g_last_error.c_str(); }

GLIMMER_API int32_t glimmer_kv_block_size(void) { return glimmer::kKVBlockSize; }

GLIMMER_API int64_t glimmer_live_device_bytes(void) { return glimmer::live_device_bytes(); }

GLIMMER_API int64_t glimmer_live_pinned_bytes(void) { return glimmer::live_pinned_bytes(); }

GLIMMER_API int glimmer_paged_kv_index(const int32_t* block_tables, int32_t num_reqs, int32_t max_blocks_per_req,
                                       int32_t num_physical_blocks, const int32_t* req_ids,
                                       const int32_t* token_pos, int32_t n_queries, int64_t* out_slots) {
  return guarded([&] {
    validate_index_args(block_tables, num_reqs, max_blocks_per_req, num_physical_blocks, req_ids, token_pos,
                        n_queries, out_slots);
    if (n_queries == 0) return;
    const std::size_t n = static_cast<std::size_t>(n_queries);
    const std::size_t tables = table_elems(num_reqs, max_blocks_per_req);

    glimmer::CudaStream stream;
    glimmer::PinnedHostBuffer<std::int32_t> h_tables(tables);
    glimmer::PinnedHostBuffer<std::int32_t> h_req(n);
    glimmer::PinnedHostBuffer<std::int32_t> h_pos(n);
    glimmer::PinnedHostBuffer<std::int64_t> h_out(n);
    if (tables != 0) std::memcpy(h_tables.data(), block_tables, h_tables.bytes());
    std::memcpy(h_req.data(), req_ids, h_req.bytes());
    std::memcpy(h_pos.data(), token_pos, h_pos.bytes());

    glimmer::DeviceTensor<std::int32_t> d_tables(tables);
    glimmer::DeviceTensor<std::int32_t> d_req(n);
    glimmer::DeviceTensor<std::int32_t> d_pos(n);
    glimmer::DeviceTensor<std::int64_t> d_out(n);
    d_tables.upload_async(h_tables.data(), tables, stream.get());
    d_req.upload_async(h_req.data(), n, stream.get());
    d_pos.upload_async(h_pos.data(), n, stream.get());

    GLIMMER_CUDA_CHECK(glimmer::launch_paged_kv_index(
        {d_tables.data(), num_reqs, max_blocks_per_req, num_physical_blocks, d_req.data(), d_pos.data(), n_queries,
         d_out.data()},
        stream.get()));

    d_out.download_async(h_out.data(), n, stream.get());
    stream.synchronize();
    std::memcpy(out_slots, h_out.data(), h_out.bytes());
  });
}

GLIMMER_API int glimmer_paged_kv_index_zero_copy(const int32_t* block_tables, int32_t num_reqs,
                                                 int32_t max_blocks_per_req, int32_t num_physical_blocks,
                                                 const int32_t* req_ids, const int32_t* token_pos,
                                                 int32_t n_queries, int64_t* out_slots) {
  return guarded([&] {
    validate_index_args(block_tables, num_reqs, max_blocks_per_req, num_physical_blocks, req_ids, token_pos,
                        n_queries, out_slots);
    if (n_queries == 0) return;
    const std::size_t n = static_cast<std::size_t>(n_queries);
    const std::size_t tables = table_elems(num_reqs, max_blocks_per_req);

    glimmer::CudaStream stream;
    // Declared after the stream so they are unregistered before it is destroyed.
    const glimmer::HostRegistration r_tables(block_tables, tables * sizeof(std::int32_t));
    const glimmer::HostRegistration r_req(req_ids, n * sizeof(std::int32_t));
    const glimmer::HostRegistration r_pos(token_pos, n * sizeof(std::int32_t));
    const glimmer::HostRegistration r_out(out_slots, n * sizeof(std::int64_t));

    GLIMMER_CUDA_CHECK(glimmer::launch_paged_kv_index(
        {r_tables.device_ptr<const std::int32_t>(), num_reqs, max_blocks_per_req, num_physical_blocks,
         r_req.device_ptr<const std::int32_t>(), r_pos.device_ptr<const std::int32_t>(), n_queries,
         r_out.device_ptr<std::int64_t>()},
        stream.get()));
    stream.synchronize();
  });
}

GLIMMER_API int glimmer_paged_kv_gather(const float* kv_cache, int32_t num_physical_blocks, int32_t row_elems,
                                        const int64_t* slots, int32_t n_slots, float* out) {
  return guarded([&] {
    if (num_physical_blocks < 0 || row_elems < 0 || n_slots < 0) {
      throw std::invalid_argument("glimmer_paged_kv_gather: dimensions must be non-negative");
    }
    const std::size_t rows = static_cast<std::size_t>(num_physical_blocks) * glimmer::kKVBlockSize;
    const std::size_t cache_elems = rows * static_cast<std::size_t>(row_elems);
    const std::size_t out_elems = static_cast<std::size_t>(n_slots) * static_cast<std::size_t>(row_elems);
    if (out_elems == 0) return;
    if ((cache_elems != 0 && kv_cache == nullptr) || slots == nullptr || out == nullptr) {
      throw std::invalid_argument("glimmer_paged_kv_gather: buffers are null");
    }

    glimmer::CudaStream stream;
    glimmer::DeviceTensor<float> d_cache(cache_elems);
    glimmer::DeviceTensor<std::int64_t> d_slots(static_cast<std::size_t>(n_slots));
    glimmer::DeviceTensor<float> d_out(out_elems);
    d_cache.upload_async(kv_cache, cache_elems, stream.get());
    d_slots.upload_async(slots, static_cast<std::size_t>(n_slots), stream.get());

    GLIMMER_CUDA_CHECK(glimmer::launch_paged_kv_gather(
        {d_cache.data(), num_physical_blocks, row_elems, d_slots.data(), n_slots, d_out.data()}, stream.get()));

    d_out.download_async(out, out_elems, stream.get());
    stream.synchronize();
  });
}

}  // extern "C"
