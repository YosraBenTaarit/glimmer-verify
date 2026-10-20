#pragma once

#include "cuda_compat.hpp"

#include <cstdint>

namespace glimmer {

inline constexpr std::int32_t kKVBlockSize = 16;
inline constexpr std::int32_t kKVBlockShift = 4;
static_assert((1 << kKVBlockShift) == kKVBlockSize, "block size must be 2^shift");

// All pointers are device-accessible (device allocations or mapped host memory).
struct PagedKVIndexArgs {
  const std::int32_t* block_tables;  // [num_reqs, max_blocks_per_req]
  std::int32_t num_reqs;
  std::int32_t max_blocks_per_req;
  std::int32_t num_physical_blocks;
  const std::int32_t* req_ids;    // [n_queries]
  const std::int32_t* token_pos;  // [n_queries]
  std::int32_t n_queries;
  std::int64_t* out_slots;  // [n_queries]
};

struct PagedKVGatherArgs {
  const float* kv_cache;  // [num_physical_blocks * kKVBlockSize, row_elems]
  std::int32_t num_physical_blocks;
  std::int32_t row_elems;
  const std::int64_t* slots;  // [n_slots]
  std::int32_t n_slots;
  float* out;  // [n_slots, row_elems]
};

// Enqueue on `stream`; return the launch status (cudaGetLastError).
cudaError_t launch_paged_kv_index(const PagedKVIndexArgs& args, cudaStream_t stream);
cudaError_t launch_paged_kv_gather(const PagedKVGatherArgs& args, cudaStream_t stream);

}  // namespace glimmer
