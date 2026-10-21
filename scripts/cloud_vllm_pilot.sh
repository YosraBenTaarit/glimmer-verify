#!/usr/bin/env bash
# One-shot: official Muse Glimmer 30B on vLLM (A100 80GB) + the 2-cell cloud pilot.
#
# Run THIS on the rented Linux GPU box, not on the laptop:
#   git clone https://github.com/YosraBenTaarit/glimmer-verify.git
#   cd glimmer-verify && bash scripts/cloud_vllm_pilot.sh
#
# Requires: NVIDIA GPU with >= 64 GiB VRAM, CUDA, python3, git, curl.
# Env: HF_TOKEN (Hugging Face, to download meta-models/Muse-Glimmer-30B).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODEL_ID="${MODEL_ID:-meta-models/Muse-Glimmer-30B}"
SERVED_MODEL_NAME="${SERVED_MODEL_NAME:-meta-models/Muse-Glimmer-30B}"
MAX_MODEL_LEN="${MAX_MODEL_LEN:-8192}"
GPU_MEM_UTIL="${GPU_MEM_UTIL:-0.90}"
PORT="${PORT:-8000}"
OUT="${OUT:-$ROOT/runs/vllm_cloud_pilot_v1}"
HEALTH_TIMEOUT_S="${HEALTH_TIMEOUT_S:-3600}"

die() { echo "error: $*" >&2; exit 1; }

command -v nvidia-smi >/dev/null || die "nvidia-smi not found (this script is for the GPU box)"
vram_mib=$(nvidia-smi --query-gpu=memory.total --format=csv,noheader,nounits | awk '{s += $1} END {print s + 0}')
if [[ "$vram_mib" -lt 64000 ]]; then
  die "need >= 64 GiB VRAM for BF16 30B (this GPU reports ${vram_mib} MiB). Do not switch to 4-bit if the goal is the Meta stack."
fi
[[ -n "${HF_TOKEN:-}" ]] || die "set HF_TOKEN (Hugging Face write/read token) before downloading weights"

python3 -m venv .venv
# shellcheck disable=SC1091
source .venv/bin/activate
pip install -U pip
pip install -e ".[dev]"
pip install "vllm>=0.6"

if [[ ! -x "$HOME/.elan/bin/lake" ]]; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
(cd src/verification/GlimmerVerify && lake build)

echo "starting vLLM (first launch downloads ~60 GB) ..."
vllm serve "$MODEL_ID" \
  --host 0.0.0.0 --port "$PORT" \
  --served-model-name "$SERVED_MODEL_NAME" \
  --enable-prefix-caching \
  --enable-prompt-tokens-details \
  --max-model-len "$MAX_MODEL_LEN" \
  --gpu-memory-utilization "$GPU_MEM_UTIL" \
  --tensor-parallel-size 1 \
  ${VLLM_EXTRA_ARGS:-} \
  > "$ROOT/vllm.log" 2>&1 &
echo $! > "$ROOT/vllm.pid"

deadline=$((SECONDS + HEALTH_TIMEOUT_S))
until curl -fsS "http://127.0.0.1:${PORT}/health" >/dev/null 2>&1; do
  if ! kill -0 "$(cat "$ROOT/vllm.pid")" 2>/dev/null; then
    tail -n 80 "$ROOT/vllm.log" >&2
    die "vLLM exited; see vllm.log"
  fi
  (( SECONDS < deadline )) || die "vLLM did not become healthy in time"
  sleep 10
done
echo "vLLM healthy on :${PORT}"

export BACKEND=local_server
export LOCAL_SERVER_KIND=vllm
export LOCAL_SERVER_URL="http://127.0.0.1:${PORT}/v1"
export LOCAL_MODEL="$SERVED_MODEL_NAME"
export LOCAL_METRICS_URL="http://127.0.0.1:${PORT}/metrics"
export GLIMMER_NVML=on

python -m src.experiments.matrix experiments/protocols/vllm_cloud_pilot.json --out "$OUT"
python -m src.telemetry.compare_runs "$OUT" --json "$OUT/summary.json" | tee "$OUT/table.md"

tar -C "$ROOT/runs" -czf "$ROOT/vllm_cloud_pilot_results.tar.gz" "$(basename "$OUT")"
echo
echo "DONE. Download vllm_cloud_pilot_results.tar.gz then DESTROY this GPU pod."
echo "Leaving it on burns ~\$1–2 per hour."
