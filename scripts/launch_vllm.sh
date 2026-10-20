#!/usr/bin/env bash
# Serve Muse Glimmer 30B on vLLM with Automatic Prefix Caching, plus Prometheus + Grafana.
#
#   bash scripts/launch_vllm.sh            # everything in docker compose (needs NVIDIA Container Toolkit)
#   bash scripts/launch_vllm.sh --native   # `vllm serve` on the host (pip install vllm); monitoring via compose if docker exists
#   bash scripts/launch_vllm.sh --down     # stop the compose stack
#
# Settings come from .env (see .env.example): MODEL_ID, SERVED_MODEL_NAME, QUANTIZATION, MAX_MODEL_LEN,
# GPU_MEM_UTIL, TP_SIZE, VLLM_EXTRA_ARGS, HF_TOKEN.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COMPOSE=(docker compose -f "$ROOT/docker/docker-compose.yml")
if [[ -f "$ROOT/.env" ]]; then
  set -a
  # shellcheck disable=SC1091
  source "$ROOT/.env"
  set +a
  COMPOSE+=(--env-file "$ROOT/.env")
fi

MODEL_ID="${MODEL_ID:-meta-models/Muse-Glimmer-30B}"
SERVED_MODEL_NAME="${SERVED_MODEL_NAME:-meta-models/Muse-Glimmer-30B}"
MAX_MODEL_LEN="${MAX_MODEL_LEN:-32768}"
GPU_MEM_UTIL="${GPU_MEM_UTIL:-0.90}"
TP_SIZE="${TP_SIZE:-1}"
PORT=8000
HEALTH_URL="http://localhost:${PORT}/health"

die() { echo "error: $*" >&2; exit 1; }

usage() { sed -n '2,9p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

check_vram() {
  if ! command -v nvidia-smi >/dev/null 2>&1; then
    echo "warning: nvidia-smi not found; cannot check VRAM" >&2
    return
  fi
  nvidia-smi --query-gpu=index,name,memory.total --format=csv,noheader
  local total_mib
  total_mib=$(nvidia-smi --query-gpu=memory.total --format=csv,noheader,nounits | head -n "$TP_SIZE" | awk '{s += $1} END {print s + 0}')
  if [[ -z "${QUANTIZATION:-}" && "$MODEL_ID" == "meta-models/Muse-Glimmer-30B" && "$total_mib" -lt 64000 ]]; then
    echo "warning: BF16 weights are ~60 GB but the ${TP_SIZE} GPU(s) used have ${total_mib} MiB." >&2
    echo "         Point MODEL_ID at a 4-bit (AWQ/GPTQ) checkpoint and set QUANTIZATION, or raise TP_SIZE." >&2
  fi
}

wait_healthy() {
  local deadline=$((SECONDS + ${HEALTH_TIMEOUT_S:-3600}))
  echo "waiting for ${HEALTH_URL} (first start downloads ~60 GB of weights) ..."
  until curl -fsS "$HEALTH_URL" >/dev/null 2>&1; do
    if [[ "${1:-}" == "docker" ]] && "${COMPOSE[@]}" ps --status exited --services 2>/dev/null | grep -qx vllm; then
      "${COMPOSE[@]}" logs --tail 80 vllm >&2
      die "vLLM container exited (if the log says the architecture is unsupported, try VLLM_EXTRA_ARGS='--model-impl transformers')"
    fi
    (( SECONDS < deadline )) || die "vLLM did not become healthy in time"
    sleep 10
  done
}

print_endpoints() {
  cat <<EOF

vLLM        http://localhost:${PORT}/v1   (model: ${SERVED_MODEL_NAME})
metrics     http://localhost:${PORT}/metrics
Prometheus  http://localhost:9090
Grafana     http://localhost:3000         (dashboard: glimmer-verify inference)

Agent settings:
  BACKEND=local_server LOCAL_SERVER_KIND=vllm LOCAL_MODEL=${SERVED_MODEL_NAME}
  python -m src.agent.proof_repair_agent
EOF
}

mode=docker
case "${1:-}" in
  "") ;;
  --native) mode=native ;;
  --down) "${COMPOSE[@]}" --profile vllm down; exit 0 ;;
  -h|--help) usage; exit 0 ;;
  *) usage; exit 2 ;;
esac

check_vram

if [[ "$mode" == docker ]]; then
  command -v docker >/dev/null 2>&1 || die "docker not found (use --native)"
  "${COMPOSE[@]}" --profile vllm up -d
  wait_healthy docker
  print_endpoints
  exit 0
fi

command -v vllm >/dev/null 2>&1 || die "vllm not found; pip install vllm (or use docker mode)"
if command -v docker >/dev/null 2>&1; then
  "${COMPOSE[@]}" up -d prometheus grafana || echo "warning: could not start Prometheus/Grafana" >&2
fi

args=(serve "$MODEL_ID"
  --host 0.0.0.0 --port "$PORT"
  --served-model-name "$SERVED_MODEL_NAME"
  --enable-prefix-caching
  --enable-prompt-tokens-details
  --max-model-len "$MAX_MODEL_LEN"
  --gpu-memory-utilization "$GPU_MEM_UTIL"
  --tensor-parallel-size "$TP_SIZE")
[[ -n "${QUANTIZATION:-}" ]] && args+=(--quantization "$QUANTIZATION")
read -r -a extra <<<"${VLLM_EXTRA_ARGS:-}"
args+=(${extra[@]+"${extra[@]}"})

print_endpoints
echo
echo "+ vllm ${args[*]}"
exec vllm "${args[@]}"
