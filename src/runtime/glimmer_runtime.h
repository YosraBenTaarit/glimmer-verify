/* Public C ABI of the glimmer runtime (used by ctypes, the OCaml stub, and the C++ harness).
 *
 * All functions are thread-safe, never throw, and return a glimmer_status. On failure,
 * glimmer_last_error() describes the error raised on the calling thread.
 */
#ifndef GLIMMER_RUNTIME_H_
#define GLIMMER_RUNTIME_H_

#include <stdint.h>

#if defined(_WIN32)
#if defined(GLIMMER_BUILDING_LIBRARY)
#define GLIMMER_API __declspec(dllexport)
#else
#define GLIMMER_API __declspec(dllimport)
#endif
#else
#define GLIMMER_API __attribute__((visibility("default")))
#endif

#ifdef __cplusplus
extern "C" {
#endif

enum glimmer_status {
  GLIMMER_OK = 0,
  GLIMMER_ERR_INVALID_ARGUMENT = 1,
  GLIMMER_ERR_CUDA = 2,
  GLIMMER_ERR_OUT_OF_MEMORY = 3,
  GLIMMER_ERR_INTERNAL = 4
};

/* Tokens per KV-cache block. */
#define GLIMMER_KV_BLOCK_SIZE 16

/* "cuda" or "cpu_fallback". */
GLIMMER_API const char* glimmer_backend_name(void);
GLIMMER_API const char* glimmer_last_error(void);
GLIMMER_API int32_t glimmer_kv_block_size(void);

/* Bytes currently held by the library's DeviceTensor / PinnedHostBuffer objects. */
GLIMMER_API int64_t glimmer_live_device_bytes(void);
GLIMMER_API int64_t glimmer_live_pinned_bytes(void);

/* Translates (req_ids[i], token_pos[i]) into a physical KV slot:
 *
 *   out_slots[i] = block_tables[req][pos / 16] * 16 + pos % 16
 *
 * block_tables is row-major [num_reqs, max_blocks_per_req]. out_slots[i] = -1 when req is outside
 * [0, num_reqs), pos < 0, pos / 16 >= max_blocks_per_req, or the table entry is outside
 * [0, num_physical_blocks) (unallocated entries are conventionally -1).
 *
 * Staged path: inputs are copied into pinned buffers, DMA'd to device tensors, and the result is
 * DMA'd back. All buffers are host pointers owned by the caller.
 */
GLIMMER_API int glimmer_paged_kv_index(const int32_t* block_tables, int32_t num_reqs, int32_t max_blocks_per_req,
                                       int32_t num_physical_blocks, const int32_t* req_ids,
                                       const int32_t* token_pos, int32_t n_queries, int64_t* out_slots);

/* Same contract, zero-copy: the caller's buffers are page-locked and mapped into the device address
 * space for the duration of the call, and the kernel reads/writes them in place. */
GLIMMER_API int glimmer_paged_kv_index_zero_copy(const int32_t* block_tables, int32_t num_reqs,
                                                 int32_t max_blocks_per_req, int32_t num_physical_blocks,
                                                 const int32_t* req_ids, const int32_t* token_pos,
                                                 int32_t n_queries, int64_t* out_slots);

/* Gathers KV rows by slot: out[i, :] = kv_cache[slots[i], :], or zeros when slots[i] is outside
 * [0, num_physical_blocks * 16). kv_cache is row-major [num_physical_blocks * 16, row_elems]
 * (vLLM's [num_blocks, block_size, num_kv_heads, head_dim] with the last two dims flattened). */
GLIMMER_API int glimmer_paged_kv_gather(const float* kv_cache, int32_t num_physical_blocks, int32_t row_elems,
                                        const int64_t* slots, int32_t n_slots, float* out);

#ifdef __cplusplus
}
#endif

#endif /* GLIMMER_RUNTIME_H_ */
