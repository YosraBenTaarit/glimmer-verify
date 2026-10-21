"""Run a factorial experiment (memory × seed × backend) with a frozen protocol.

Each cell writes ``experiment.json`` plus the usual agent artifacts, so
``python -m src.telemetry.compare_runs`` can aggregate them later. The *same*
protocol file is valid on OpenRouter and on a self-hosted vLLM/SGLang stack:
only ``BACKEND`` / ``LOCAL_SERVER_*`` in the environment change.

    python -m src.experiments.matrix experiments/protocols/openrouter_scale.json
    BACKEND=local_server LOCAL_SERVER_KIND=vllm \\
      python -m src.experiments.matrix experiments/protocols/vllm_meta_stack.json
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from itertools import product
from pathlib import Path
from typing import Any, Mapping, Sequence

from ..agent.glimmer_client import load_dotenv_if_present

REPO_ROOT = Path(__file__).resolve().parents[2]


def cells(protocol: Mapping[str, Any]) -> list[dict[str, Any]]:
    axes: Mapping[str, Sequence[Any]] = protocol["axes"]
    keys = list(axes)
    out = []
    for values in product(*(axes[k] for k in keys)):
        out.append(dict(zip(keys, values, strict=True)))
    return out


def cell_env(protocol: Mapping[str, Any], cell: Mapping[str, Any]) -> dict[str, str]:
    env = dict(os.environ)
    shared = protocol.get("shared", {})
    mapping = {
        "max_tokens": "GLIMMER_MAX_TOKENS",
        "reasoning_max_tokens": "GLIMMER_REASONING_MAX_TOKENS",
        "reasoning_effort": "GLIMMER_REASONING_EFFORT",
        "temperature": "GLIMMER_TEMPERATURE",
        "top_p": "GLIMMER_TOP_P",
        "seed": "GLIMMER_SEED",
        "max_retries": "MAX_RETRIES",
        "memory": "AGENT_MEMORY",
        "provider_order": "OPENROUTER_PROVIDER_ORDER",
        "allow_fallbacks": "OPENROUTER_ALLOW_FALLBACKS",
        "model": "OPENROUTER_MODEL",
    }
    for src in (shared, cell):
        for key, value in src.items():
            env_key = mapping.get(key)
            if env_key is None:
                continue
            env[env_key] = "" if value is None else str(value)
    return env


def cell_dir(root: Path, cell: Mapping[str, Any]) -> Path:
    parts = [f"{k}={cell[k]}" for k in sorted(cell)]
    return root / "_".join(parts).replace("/", "-")


def run_cell(protocol: Mapping[str, Any], cell: Mapping[str, Any], out_root: Path, python: str) -> int:
    dest = cell_dir(out_root, cell)
    dest.mkdir(parents=True, exist_ok=True)
    argv = [python, "-u", "-m", "src.agent.proof_repair_agent", "--run-dir", str(dest)]
    tasks = protocol.get("tasks") or []
    if tasks:
        argv += ["--tasks", *tasks]
    if protocol.get("max_retries") is not None:
        argv += ["--max-retries", str(protocol["max_retries"])]
    memory = cell.get("memory") or protocol.get("shared", {}).get("memory")
    if memory:
        argv += ["--memory", str(memory)]
    env = cell_env(protocol, cell)
    with (dest / "agent.log").open("w", encoding="utf-8") as log:
        proc = subprocess.run(argv, cwd=REPO_ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    meta_path = dest / "experiment.json"
    meta = json.loads(meta_path.read_text(encoding="utf-8")) if meta_path.is_file() else {}
    meta.update({"protocol": protocol.get("name"), "cell": dict(cell), "returncode": proc.returncode})
    meta_path.write_text(json.dumps(meta, indent=2), encoding="utf-8")
    return proc.returncode


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("protocol", type=Path)
    p.add_argument("--out", type=Path, default=None)
    p.add_argument("--dry-run", action="store_true", help="print cells and exit")
    args = p.parse_args(argv)
    load_dotenv_if_present()
    protocol = json.loads(args.protocol.read_text(encoding="utf-8"))
    planned = cells(protocol)
    out_root = args.out or (REPO_ROOT / "runs" / str(protocol["name"]))
    print(f"protocol {protocol['name']}: {len(planned)} cell(s) -> {out_root}", file=sys.stderr)
    for cell in planned:
        print(f"  {cell_dir(out_root, cell).name}", file=sys.stderr)
    if args.dry_run:
        return 0
    codes = [run_cell(protocol, cell, out_root, sys.executable) for cell in planned]
    failed = sum(c != 0 for c in codes)
    print(f"finished {len(codes) - failed}/{len(codes)} cells with all tasks proved; "
          f"artifacts in {out_root}", file=sys.stderr)
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
