// C++ test harness for the glimmer runtime. Exit code 0 iff every check passes.
//
//   * both index paths agree with an independent host reference on random allocator states,
//     including out-of-range queries that must be masked to -1;
//   * slots of distinct requests never collide (runtime witness of `paged_kv_isolation`);
//   * the KV gather matches a host gather exactly;
//   * RAII handles release every byte, including when an allocation throws.
#include "glimmer_runtime.h"
#include "tensor_raii.hpp"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace {

int g_checks = 0;
int g_failures = 0;

void expect(bool ok, const std::string& what) {
  ++g_checks;
  if (!ok) {
    ++g_failures;
    std::fprintf(stderr, "FAIL: %s\n", what.c_str());
  }
}

void expect_ok(int status, const std::string& what) {
  expect(status == GLIMMER_OK, what + " -> status " + std::to_string(status) + " (" + glimmer_last_error() + ")");
}

struct Case {
  std::int32_t num_reqs = 0;
  std::int32_t max_blocks = 0;
  std::int32_t num_phys = 0;
  std::vector<std::int32_t> tables;
  std::vector<std::int32_t> req_ids;
  std::vector<std::int32_t> token_pos;
};

// Disjoint ownership: physical blocks are handed out from one shuffled free list.
Case make_case(std::uint32_t seed, std::int32_t num_reqs, std::int32_t max_blocks, std::int32_t num_phys,
               std::int32_t n_queries) {
  std::mt19937 rng(seed);
  Case c;
  c.num_reqs = num_reqs;
  c.max_blocks = max_blocks;
  c.num_phys = num_phys;
  c.tables.assign(static_cast<std::size_t>(num_reqs) * max_blocks, -1);

  std::vector<std::int32_t> free_list(static_cast<std::size_t>(num_phys));
  std::iota(free_list.begin(), free_list.end(), 0);
  std::shuffle(free_list.begin(), free_list.end(), rng);
  std::size_t next = 0;
  std::uniform_int_distribution<std::int32_t> n_alloc(0, max_blocks);
  for (std::int32_t r = 0; r < num_reqs; ++r) {
    const std::int32_t blocks = n_alloc(rng);
    for (std::int32_t l = 0; l < blocks && next < free_list.size(); ++l) {
      c.tables[static_cast<std::size_t>(r) * max_blocks + l] = free_list[next++];
    }
  }

  std::uniform_int_distribution<std::int32_t> req_dist(-1, num_reqs);
  std::uniform_int_distribution<std::int32_t> pos_dist(-3, max_blocks * glimmer_kv_block_size() + 5);
  c.req_ids.resize(static_cast<std::size_t>(n_queries));
  c.token_pos.resize(static_cast<std::size_t>(n_queries));
  for (std::int32_t i = 0; i < n_queries; ++i) {
    c.req_ids[i] = req_dist(rng);
    c.token_pos[i] = pos_dist(rng);
  }
  return c;
}

std::int64_t reference_slot(const Case& c, std::int32_t req, std::int32_t pos) {
  const std::int32_t bs = glimmer_kv_block_size();
  if (req < 0 || req >= c.num_reqs || pos < 0 || pos / bs >= c.max_blocks) return -1;
  const std::int32_t phys = c.tables[static_cast<std::size_t>(req) * c.max_blocks + pos / bs];
  if (phys < 0 || phys >= c.num_phys) return -1;
  return static_cast<std::int64_t>(phys) * bs + pos % bs;
}

void test_index_paths(std::uint32_t seed) {
  const Case c = make_case(seed, 7, 9, 48, 1031);
  const std::size_t n = c.req_ids.size();
  std::vector<std::int64_t> staged(n, -7);
  std::vector<std::int64_t> zero_copy(n, -7);

  expect_ok(glimmer_paged_kv_index(c.tables.data(), c.num_reqs, c.max_blocks, c.num_phys, c.req_ids.data(),
                                   c.token_pos.data(), static_cast<std::int32_t>(n), staged.data()),
            "staged index seed " + std::to_string(seed));
  expect_ok(glimmer_paged_kv_index_zero_copy(c.tables.data(), c.num_reqs, c.max_blocks, c.num_phys,
                                             c.req_ids.data(), c.token_pos.data(), static_cast<std::int32_t>(n),
                                             zero_copy.data()),
            "zero-copy index seed " + std::to_string(seed));

  std::size_t mismatches = 0;
  std::size_t masked = 0;
  for (std::size_t i = 0; i < n; ++i) {
    const std::int64_t want = reference_slot(c, c.req_ids[i], c.token_pos[i]);
    masked += want == -1;
    mismatches += (staged[i] != want) + (zero_copy[i] != want);
  }
  expect(mismatches == 0, "index paths match reference (seed " + std::to_string(seed) + ", " +
                              std::to_string(mismatches) + " mismatches)");
  expect(masked > 0 && masked < n, "case exercises both masked and valid lanes");

  std::vector<std::set<std::int64_t>> owned(static_cast<std::size_t>(c.num_reqs));
  for (std::size_t i = 0; i < n; ++i) {
    if (staged[i] >= 0) owned[static_cast<std::size_t>(c.req_ids[i])].insert(staged[i]);
  }
  bool disjoint = true;
  for (std::size_t a = 0; a < owned.size(); ++a)
    for (std::size_t b = a + 1; b < owned.size(); ++b)
      for (const std::int64_t s : owned[a]) disjoint = disjoint && owned[b].count(s) == 0;
  expect(disjoint, "slots of distinct requests are disjoint (seed " + std::to_string(seed) + ")");
}

void test_gather(std::uint32_t seed) {
  std::mt19937 rng(seed);
  const std::int32_t num_phys = 11;
  const std::int32_t row = 2 * 128;  // num_kv_heads * head_dim of Muse Glimmer 30B
  const std::int32_t rows_total = num_phys * glimmer_kv_block_size();
  std::vector<float> cache(static_cast<std::size_t>(rows_total) * row);
  std::normal_distribution<float> normal(0.0f, 1.0f);
  for (float& v : cache) v = normal(rng);

  std::uniform_int_distribution<std::int64_t> slot_dist(-2, rows_total + 2);
  std::vector<std::int64_t> slots(97);
  for (std::int64_t& s : slots) s = slot_dist(rng);

  std::vector<float> out(slots.size() * row, -1.0f);
  expect_ok(glimmer_paged_kv_gather(cache.data(), num_phys, row, slots.data(), static_cast<std::int32_t>(slots.size()),
                                    out.data()),
            "gather seed " + std::to_string(seed));

  std::size_t mismatches = 0;
  for (std::size_t q = 0; q < slots.size(); ++q) {
    const bool valid = slots[q] >= 0 && slots[q] < rows_total;
    for (std::int32_t e = 0; e < row; ++e) {
      const float want = valid ? cache[static_cast<std::size_t>(slots[q]) * row + e] : 0.0f;
      mismatches += out[q * row + e] != want;
    }
  }
  expect(mismatches == 0, "gather matches host reference (seed " + std::to_string(seed) + ")");
}

void test_invalid_arguments() {
  std::int64_t out = 0;
  const std::int32_t zero = 0;
  expect(glimmer_paged_kv_index(nullptr, -1, 0, 0, &zero, &zero, 1, &out) == GLIMMER_ERR_INVALID_ARGUMENT,
         "negative num_reqs is rejected");
  expect(std::string(glimmer_last_error()).find("non-negative") != std::string::npos, "error message is reported");
  expect(glimmer_paged_kv_index(nullptr, 0, 0, 0, nullptr, nullptr, 0, nullptr) == GLIMMER_OK,
         "empty query batch is a no-op");
  expect(glimmer_paged_kv_index(nullptr, 0, 0, 4, &zero, &zero, 1, &out) == GLIMMER_OK && out == -1,
         "query against an empty table is masked");
}

void test_raii() {
  const std::int64_t device_before = glimmer::live_device_bytes();
  const std::int64_t pinned_before = glimmer::live_pinned_bytes();
  {
    glimmer::DeviceTensor<float> a(1024);
    glimmer::PinnedHostBuffer<std::int32_t> p(64);
    expect(glimmer::live_device_bytes() == device_before + 4096, "DeviceTensor accounts its bytes");
    expect(glimmer::live_pinned_bytes() == pinned_before + 256, "PinnedHostBuffer accounts its bytes");

    glimmer::DeviceTensor<float> b(std::move(a));
    expect(a.data() == nullptr && a.size() == 0 && b.size() == 1024, "move leaves the source empty");
    expect(glimmer::live_device_bytes() == device_before + 4096, "move does not double-count");

    b = glimmer::DeviceTensor<float>(16);
    expect(glimmer::live_device_bytes() == device_before + 64, "move-assignment frees the old buffer");
  }
  expect(glimmer::live_device_bytes() == device_before, "device bytes return to baseline after scope");
  expect(glimmer::live_pinned_bytes() == pinned_before, "pinned bytes return to baseline after scope");

  bool threw = false;
  try {
    glimmer::DeviceTensor<std::uint8_t> keep(128);
    glimmer::DeviceTensor<std::uint8_t> huge(std::size_t{1} << 62);
  } catch (const glimmer::CudaError& e) {
    threw = e.code() == cudaErrorMemoryAllocation;
  }
  expect(threw, "impossible allocation throws CudaError(cudaErrorMemoryAllocation)");
  expect(glimmer::live_device_bytes() == device_before, "unwinding after a failed allocation frees siblings");
}

}  // namespace

int main() {
  std::printf("glimmer runtime harness (backend: %s)\n", glimmer_backend_name());

  for (std::uint32_t seed = 0; seed < 16; ++seed) test_index_paths(seed);
  for (std::uint32_t seed = 0; seed < 4; ++seed) test_gather(seed);
  test_invalid_arguments();
  test_raii();

  expect(glimmer_live_device_bytes() == 0, "library holds no device memory after all calls");
  expect(glimmer_live_pinned_bytes() == 0, "library holds no pinned memory after all calls");

  if (g_failures != 0) {
    std::printf("%d of %d checks FAILED\n", g_failures, g_checks);
    return 1;
  }
  std::printf("all checks passed (%d)\n", g_checks);
  return 0;
}
