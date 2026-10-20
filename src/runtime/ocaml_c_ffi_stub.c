/* Zero-copy OCaml -> CUDA stub for the paged KV indexer.
 *
 * OCaml side (e.g. code extracted from a verified model, or a hand-written driver):
 *
 *   open Bigarray
 *   type i32_mat = (int32, int32_elt, c_layout) Array2.t
 *   type i32_vec = (int32, int32_elt, c_layout) Array1.t
 *   type i64_vec = (int64, int64_elt, c_layout) Array1.t
 *
 *   external paged_kv_index :
 *     i32_mat -> int -> i32_vec -> i32_vec -> i64_vec -> unit = "glimmer_ml_paged_kv_index"
 *   (* paged_kv_index block_tables num_physical_blocks req_ids token_pos out_slots *)
 *
 * Bigarray payloads live outside the OCaml heap, so the GC never moves them. The raw pointers are
 * taken while holding the runtime lock, the lock is released for the device work, and the
 * arguments stay alive because CAMLparam registers them as local roots for the whole call.
 *
 * Build: cc -c -I"$(ocamlfind ocamlc -where)" -Isrc/runtime src/runtime/ocaml_c_ffi_stub.c
 *        and link with -lglimmer_runtime (see `make ocaml-stub`).
 */
#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/bigarray.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/threads.h>

#include <stdint.h>

#include "glimmer_runtime.h"

static struct caml_ba_array* expect_bigarray(value v, int kind, int num_dims, const char* name) {
  struct caml_ba_array* ba = Caml_ba_array_val(v);
  if ((ba->flags & CAML_BA_KIND_MASK) != kind) caml_invalid_argument(name);
  if ((ba->flags & CAML_BA_LAYOUT_MASK) != CAML_BA_C_LAYOUT) caml_invalid_argument(name);
  if (ba->num_dims != num_dims) caml_invalid_argument(name);
  return ba;
}

static int32_t expect_int32_dim(intnat dim, const char* name) {
  if (dim < 0 || dim > INT32_MAX) caml_invalid_argument(name);
  return (int32_t)dim;
}

CAMLprim value glimmer_ml_paged_kv_index(value v_block_tables, value v_num_physical_blocks, value v_req_ids,
                                         value v_token_pos, value v_out_slots) {
  CAMLparam5(v_block_tables, v_num_physical_blocks, v_req_ids, v_token_pos, v_out_slots);

  struct caml_ba_array* tables = expect_bigarray(v_block_tables, CAML_BA_INT32, 2, "paged_kv_index: block_tables");
  struct caml_ba_array* req = expect_bigarray(v_req_ids, CAML_BA_INT32, 1, "paged_kv_index: req_ids");
  struct caml_ba_array* pos = expect_bigarray(v_token_pos, CAML_BA_INT32, 1, "paged_kv_index: token_pos");
  struct caml_ba_array* out = expect_bigarray(v_out_slots, CAML_BA_INT64, 1, "paged_kv_index: out_slots");

  const int32_t num_reqs = expect_int32_dim(tables->dim[0], "paged_kv_index: block_tables rows");
  const int32_t max_blocks_per_req = expect_int32_dim(tables->dim[1], "paged_kv_index: block_tables cols");
  const int32_t n_queries = expect_int32_dim(req->dim[0], "paged_kv_index: req_ids length");
  if (pos->dim[0] != req->dim[0] || out->dim[0] != req->dim[0]) {
    caml_invalid_argument("paged_kv_index: req_ids, token_pos and out_slots must have equal length");
  }
  const intnat num_physical_blocks_ml = Long_val(v_num_physical_blocks);
  if (num_physical_blocks_ml < 0 || num_physical_blocks_ml > INT32_MAX) {
    caml_invalid_argument("paged_kv_index: num_physical_blocks");
  }
  const int32_t num_physical_blocks = (int32_t)num_physical_blocks_ml;

  const int32_t* tables_ptr = (const int32_t*)Caml_ba_data_val(v_block_tables);
  const int32_t* req_ptr = (const int32_t*)Caml_ba_data_val(v_req_ids);
  const int32_t* pos_ptr = (const int32_t*)Caml_ba_data_val(v_token_pos);
  int64_t* out_ptr = (int64_t*)Caml_ba_data_val(v_out_slots);

  /* No OCaml values may be touched until the lock is reacquired. */
  caml_release_runtime_system();
  int status = glimmer_paged_kv_index_zero_copy(tables_ptr, num_reqs, max_blocks_per_req, num_physical_blocks,
                                                req_ptr, pos_ptr, n_queries, out_ptr);
  if (status == GLIMMER_ERR_CUDA) {
    /* Memory-mapped Bigarrays (Unix.map_file) may refuse cudaHostRegister; fall back to staging. */
    status = glimmer_paged_kv_index(tables_ptr, num_reqs, max_blocks_per_req, num_physical_blocks, req_ptr, pos_ptr,
                                    n_queries, out_ptr);
  }
  caml_acquire_runtime_system();

  if (status != GLIMMER_OK) caml_failwith(glimmer_last_error());
  CAMLreturn(Val_unit);
}
