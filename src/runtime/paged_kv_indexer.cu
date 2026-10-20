// Paged KV-cache indexing kernels. This file is also the `nvcc -ptx` extraction target (`make ptx`);
// kernels are extern "C" so their PTX entry names are unmangled.
#include "paged_kv_indexer.cuh"

#include <algorithm>

// glimmer:snippet-begin paged_kv_index_kernel
// One thread per query. Lane i reads req_ids[i] / token_pos[i] and writes out_slots[i], so those
// streams are fully coalesced per warp; the block_tables read is a gather that coalesces when
// consecutive lanes query consecutive positions of one request (vLLM's prefill/decode layout).
extern "C" GLIMMER_KERNEL void paged_kv_index_kernel(const std::int32_t* GLIMMER_RESTRICT block_tables,
                                                     std::int32_t num_reqs, std::int32_t max_blocks_per_req,
                                                     std::int32_t num_physical_blocks,
                                                     const std::int32_t* GLIMMER_RESTRICT req_ids,
                                                     const std::int32_t* GLIMMER_RESTRICT token_pos,
                                                     std::int32_t n_queries,
                                                     std::int64_t* GLIMMER_RESTRICT out_slots) {
  const std::int64_t idx = static_cast<std::int64_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  // Predicate %p1 of the PTX; Lean: GlimmerVerify.ptx_predicate_bounds_safe.
  if (idx >= n_queries) return;

  const std::int32_t req = GLIMMER_LDG(req_ids + idx);
  const std::int32_t pos = GLIMMER_LDG(token_pos + idx);

  std::int64_t slot = -1;
  if (req >= 0 && req < num_reqs && pos >= 0) {
    const std::int32_t logical_block = pos >> glimmer::kKVBlockShift;
    if (logical_block < max_blocks_per_req) {
      const std::int32_t phys =
          GLIMMER_LDG(block_tables + static_cast<std::int64_t>(req) * max_blocks_per_req + logical_block);
      if (phys >= 0 && phys < num_physical_blocks) {
        // Lean: GlimmerVerify.physSlot.
        slot = static_cast<std::int64_t>(phys) * glimmer::kKVBlockSize + (pos & (glimmer::kKVBlockSize - 1));
      }
    }
  }
  out_slots[idx] = slot;
}
// glimmer:snippet-end

// glimmer:snippet-begin paged_kv_gather_kernel
// Grid-stride loop over the flattened [n_slots, row_elems] output; consecutive lanes copy
// consecutive elements of one KV row, so both the cache read and the output write coalesce.
extern "C" GLIMMER_KERNEL void paged_kv_gather_kernel(const float* GLIMMER_RESTRICT kv_cache,
                                                      std::int64_t num_slots_total, std::int32_t row_elems,
                                                      const std::int64_t* GLIMMER_RESTRICT slots,
                                                      std::int32_t n_slots, float* GLIMMER_RESTRICT out) {
  const std::int64_t total = static_cast<std::int64_t>(n_slots) * row_elems;
  const std::int64_t stride = static_cast<std::int64_t>(gridDim.x) * blockDim.x;
  for (std::int64_t idx = static_cast<std::int64_t>(blockIdx.x) * blockDim.x + threadIdx.x; idx < total;
       idx += stride) {
    const std::int64_t q = idx / row_elems;
    const std::int64_t e = idx - q * row_elems;
    const std::int64_t slot = slots[q];
    out[idx] = (slot >= 0 && slot < num_slots_total) ? GLIMMER_LDG(kv_cache + slot * row_elems + e) : 0.0f;
  }
}
// glimmer:snippet-end

namespace glimmer {
namespace {

constexpr unsigned int kThreadsPerBlock = 256;
constexpr std::int64_t kMaxGatherBlocks = 4096;

unsigned int blocks_for(std::int64_t work_items, std::int64_t max_blocks) {
  const std::int64_t blocks = (work_items + kThreadsPerBlock - 1) / kThreadsPerBlock;
  return static_cast<unsigned int>(std::min(blocks, max_blocks));
}

}  // namespace

cudaError_t launch_paged_kv_index(const PagedKVIndexArgs& a, cudaStream_t stream) {
  if (a.n_queries <= 0) return cudaSuccess;
  const unsigned int blocks = blocks_for(a.n_queries, std::int64_t{1} << 31);
  GLIMMER_LAUNCH(paged_kv_index_kernel, dim3(blocks), dim3(kThreadsPerBlock), 0, stream, a.block_tables,
                 a.num_reqs, a.max_blocks_per_req, a.num_physical_blocks, a.req_ids, a.token_pos, a.n_queries,
                 a.out_slots);
  return cudaGetLastError();
}

cudaError_t launch_paged_kv_gather(const PagedKVGatherArgs& a, cudaStream_t stream) {
  const std::int64_t total = static_cast<std::int64_t>(a.n_slots) * a.row_elems;
  if (total <= 0) return cudaSuccess;
  const std::int64_t num_slots_total = static_cast<std::int64_t>(a.num_physical_blocks) * kKVBlockSize;
  const unsigned int blocks = blocks_for(total, kMaxGatherBlocks);
  GLIMMER_LAUNCH(paged_kv_gather_kernel, dim3(blocks), dim3(kThreadsPerBlock), 0, stream, a.kv_cache,
                 num_slots_total, a.row_elems, a.slots, a.n_slots, a.out);
  return cudaGetLastError();
}

}  // namespace glimmer
