"""Controlled replay of the conversation prefix that preceded an empty ("collapsed") reply.

In the max4k runs the model sometimes answered with exactly 4 completion tokens, no reasoning and no
content, always after >= 3 truncated attempts in the same conversation. This replays the exact request
that produced such a reply under three conditions, to separate competing explanations:

* ``original``    the request as sent (does the collapse reproduce at all?)
* ``neutral``     truncation feedback reworded without "output token limit ... be more concise"
* ``placeholder`` original feedback, but the empty assistant turns are replaced by a short
                  placeholder (is the model imitating the empty assistant turns in its context?)

    python -m src.experiments.replay_collapse --source runs/frozen_d8874c4/max4k_s1 \
        --task B06 --turn 4 --samples 6 --out runs/repro_collapse
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import dataclasses
import json
import re
import sys
from pathlib import Path
from typing import Any, Sequence

from ..agent.glimmer_client import BackendConfig, GlimmerClient, load_dotenv_if_present
from ..agent.prompts import extract_lean_code

CONDITIONS = ("original", "neutral", "placeholder")
_TRUNC_RE = re.compile(
    r"the response hit the output token limit before a complete ```lean block was produced; be more concise"
)
NEUTRAL_REASON = "no complete ```lean block was received"
PLACEHOLDER = "(This attempt produced no answer.)"


def request_prefix(conversation: dict[str, Any], turn: int) -> list[dict[str, str]]:
    """Messages sent for attempt ``turn``: system, task, then (assistant, feedback) for earlier attempts."""
    messages = conversation["messages"][: 2 * turn]
    if len(messages) != 2 * turn or messages[-1]["role"] != "user":
        raise ValueError(f"conversation has no request for attempt {turn}")
    return [{"role": m["role"], "content": m["content"]} for m in messages]


def apply_condition(messages: Sequence[dict[str, str]], condition: str) -> list[dict[str, str]]:
    out = [dict(m) for m in messages]
    if condition == "neutral":
        for m in out[2:]:
            if m["role"] == "user":
                m["content"] = _TRUNC_RE.sub(NEUTRAL_REASON, m["content"])
    elif condition == "placeholder":
        for m in out[2:]:
            if m["role"] == "assistant" and not m["content"].strip():
                m["content"] = PLACEHOLDER
    elif condition != "original":
        raise ValueError(f"unknown condition {condition!r}")
    return out


def classify(content: str, finish_reason: str | None, completion_tokens: int | None) -> str:
    if finish_reason == "length":
        return "truncated"
    if not content.strip():
        return "empty"
    return "code" if extract_lean_code(content) is not None else "text_without_code"


def run_one(config: BackendConfig, messages: list[dict[str, str]], seed: int) -> dict[str, Any]:
    result = GlimmerClient(dataclasses.replace(config, seed=seed)).chat(messages)
    return {
        "seed": seed,
        "class": classify(result.content, result.finish_reason, result.completion_tokens),
        "finish_reason": result.finish_reason,
        "completion_tokens": result.completion_tokens,
        "reasoning_chars": len(result.reasoning),
        "content_chars": len(result.content),
        "provider": result.provider,
        "served_model": result.served_model,
        "response_id": result.response_id,
        "cost_usd": result.cost_usd,
        "content_head": result.content[:300],
    }


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--source", type=Path, required=True, help="run directory containing tasks/<id>/conversation.json")
    p.add_argument("--task", required=True, help="task id prefix")
    p.add_argument("--turn", type=int, required=True, help="attempt number whose request is replayed")
    p.add_argument("--samples", type=int, default=6, help="samples per condition (seeds 101, 102, ...)")
    p.add_argument("--conditions", nargs="*", default=list(CONDITIONS), choices=CONDITIONS)
    p.add_argument("--workers", type=int, default=6)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args(argv)

    load_dotenv_if_present()
    matches = [d for d in sorted((args.source / "tasks").iterdir()) if d.name.casefold().startswith(args.task.casefold())]
    if len(matches) != 1:
        print(f"--task {args.task!r} matches {len(matches)} task directories", file=sys.stderr)
        return 2
    conversation = json.loads((matches[0] / "conversation.json").read_text(encoding="utf-8"))
    base = request_prefix(conversation, args.turn)
    original_outcome = conversation["attempts"][args.turn - 1]
    config = BackendConfig.from_env()

    jobs = [(c, 101 + i) for c in args.conditions for i in range(args.samples)]
    with cf.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, config, apply_condition(base, c), seed): (c, seed) for c, seed in jobs}
        results = []
        for fut in cf.as_completed(futures):
            condition, seed = futures[fut]
            try:
                row = fut.result()
            except Exception as exc:  # recorded, not fatal: one failed request must not lose the others
                row = {"seed": seed, "class": "request_error", "error": repr(exc)}
            row["condition"] = condition
            results.append(row)
            print(f"{condition:<12} seed {seed}: {row['class']:<18} tokens={row.get('completion_tokens')} "
                  f"cost={row.get('cost_usd')}", file=sys.stderr)

    results.sort(key=lambda r: (CONDITIONS.index(r["condition"]), r["seed"]))
    summary = {
        c: {k: sum(1 for r in results if r["condition"] == c and r["class"] == k)
            for k in ("empty", "truncated", "code", "text_without_code", "request_error")}
        for c in args.conditions
    }
    record = {
        "source": str(matches[0]),
        "task_id": conversation["task_id"],
        "turn": args.turn,
        "original_attempt": {k: original_outcome.get(k) for k in ("outcome", "finish_reason", "completion_tokens")},
        "config": {k: getattr(config, k) for k in ("model", "provider_order", "allow_fallbacks", "temperature",
                                                     "top_p", "max_tokens", "reasoning_effort", "reasoning_max_tokens")},
        "summary": summary,
        "total_cost_usd": sum(r.get("cost_usd") or 0 for r in results),
        "results": results,
    }
    args.out.mkdir(parents=True, exist_ok=True)
    out_file = args.out / f"{conversation['task_id']}_turn{args.turn}.json"
    out_file.write_text(json.dumps(record, indent=2, default=list), encoding="utf-8")
    print(json.dumps({"task": conversation["task_id"], "turn": args.turn, "summary": summary,
                      "cost_usd": round(record["total_cost_usd"], 4), "file": str(out_file)}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
