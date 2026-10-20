"""Dual-backend chat client for Muse Glimmer 30B.

``BACKEND=openrouter`` talks to OpenRouter's OpenAI-compatible API, so the agent runs on a laptop.
``BACKEND=local_server`` talks to a self-hosted vLLM (``:8000/v1``) or SGLang (``:30000/v1``)
server. Both paths stream, so every call yields client-side TTFT and inter-token timings.
"""

from __future__ import annotations

import math
import os
import statistics
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Sequence

OPENROUTER_DEFAULT_BASE_URL = "https://openrouter.ai/api/v1"
OPENROUTER_DEFAULT_MODEL = "meta/muse-glimmer-30b"
LOCAL_DEFAULT_MODEL = "meta-models/Muse-Glimmer-30B"
LOCAL_DEFAULT_URLS = {"vllm": "http://localhost:8000/v1", "sglang": "http://localhost:30000/v1"}

BACKENDS = ("openrouter", "local_server")
SERVER_KINDS = ("vllm", "sglang")
REASONING_EFFORTS = ("minimal", "low", "medium", "high")


class ConfigError(ValueError):
    pass


def load_dotenv_if_present(path: str | os.PathLike[str] | None = None) -> None:
    """Load ``.env`` (repo root by default) without overriding variables already set."""
    dotenv_path = Path(path) if path is not None else Path(__file__).resolve().parents[2] / ".env"
    if not dotenv_path.is_file():
        return
    try:
        from dotenv import load_dotenv
    except ImportError:
        _load_simple_dotenv(dotenv_path)
    else:
        load_dotenv(dotenv_path, override=False)


def _load_simple_dotenv(path: Path) -> None:
    """``KEY=VALUE`` lines, ``#`` comments, optional ``export`` and surrounding quotes; no interpolation."""
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip().removeprefix("export ").strip()
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"":
            value = value[1:-1]
        if key:
            os.environ.setdefault(key, value)


def _metrics_url_from_base(base_url: str) -> str:
    root = base_url.rstrip("/")
    if root.endswith("/v1"):
        root = root[: -len("/v1")]
    return root + "/metrics"


def _optional_float(env: Mapping[str, str], key: str, default: float | None) -> float | None:
    raw = env.get(key, "").strip()
    if not raw:
        return default
    try:
        return float(raw)
    except ValueError as exc:
        raise ConfigError(f"{key}={raw!r} is not a number") from exc


def _optional_int(env: Mapping[str, str], key: str, default: int | None) -> int | None:
    raw = env.get(key, "").strip()
    if not raw:
        return default
    try:
        return int(raw)
    except ValueError as exc:
        raise ConfigError(f"{key}={raw!r} is not an integer") from exc


@dataclass(frozen=True)
class BackendConfig:
    backend: str
    server_kind: str  # "openrouter" | "vllm" | "sglang"
    base_url: str
    api_key: str
    model: str
    metrics_url: str | None
    temperature: float = 0.2
    top_p: float = 0.95
    max_tokens: int = 4096
    seed: int | None = None
    timeout_s: float = 600.0
    max_http_retries: int = 4
    extra_headers: Mapping[str, str] = field(default_factory=dict)
    # OpenRouter only: provider routing. Each provider keeps its own prompt cache (and may serve a different
    # quantization), so load-balancing across providers both defeats prefix caching and confounds results.
    provider_order: tuple[str, ...] = ()
    allow_fallbacks: bool = True
    # OpenRouter only: reasoning tokens count against max_tokens, so an unbounded scratchpad can consume the
    # whole budget and leave no room for the answer (finish_reason="length", empty content).
    reasoning_effort: str | None = None
    reasoning_max_tokens: int | None = None

    @classmethod
    def from_env(cls, env: Mapping[str, str] | None = None) -> "BackendConfig":
        if env is None:
            load_dotenv_if_present()
            env = os.environ
        backend = env.get("BACKEND", "openrouter").strip().lower()
        if backend not in BACKENDS:
            raise ConfigError(f"BACKEND must be one of {BACKENDS}, got {backend!r}")

        sampling = dict(
            temperature=_optional_float(env, "GLIMMER_TEMPERATURE", 0.2),
            top_p=_optional_float(env, "GLIMMER_TOP_P", 0.95),
            max_tokens=_optional_int(env, "GLIMMER_MAX_TOKENS", 4096),
            seed=_optional_int(env, "GLIMMER_SEED", None),
            timeout_s=_optional_float(env, "GLIMMER_REQUEST_TIMEOUT_S", 600.0),
        )

        if backend == "openrouter":
            api_key = env.get("OPENROUTER_API_KEY", "").strip()
            if not api_key:
                raise ConfigError("BACKEND=openrouter requires OPENROUTER_API_KEY")
            headers = {}
            if env.get("OPENROUTER_APP_URL"):
                headers["HTTP-Referer"] = env["OPENROUTER_APP_URL"]
            if env.get("OPENROUTER_APP_TITLE"):
                headers["X-Title"] = env["OPENROUTER_APP_TITLE"]
            order = tuple(p.strip() for p in env.get("OPENROUTER_PROVIDER_ORDER", "").split(",") if p.strip())
            fallbacks = env.get("OPENROUTER_ALLOW_FALLBACKS", "true").strip().lower()
            if fallbacks not in ("true", "false", "1", "0", "yes", "no"):
                raise ConfigError(f"OPENROUTER_ALLOW_FALLBACKS={fallbacks!r} is not a boolean")
            effort = env.get("GLIMMER_REASONING_EFFORT", "").strip().lower() or None
            if effort is not None and effort not in REASONING_EFFORTS:
                raise ConfigError(f"GLIMMER_REASONING_EFFORT must be one of {REASONING_EFFORTS}, got {effort!r}")
            reasoning_max = _optional_int(env, "GLIMMER_REASONING_MAX_TOKENS", None)
            if effort is not None and reasoning_max is not None:
                raise ConfigError("set at most one of GLIMMER_REASONING_EFFORT and GLIMMER_REASONING_MAX_TOKENS")
            if reasoning_max is not None and reasoning_max >= sampling["max_tokens"]:
                raise ConfigError("GLIMMER_REASONING_MAX_TOKENS must be below GLIMMER_MAX_TOKENS to leave room for the answer")
            return cls(
                backend=backend,
                server_kind="openrouter",
                base_url=env.get("OPENROUTER_BASE_URL", "").strip() or OPENROUTER_DEFAULT_BASE_URL,
                api_key=api_key,
                model=env.get("OPENROUTER_MODEL", "").strip() or OPENROUTER_DEFAULT_MODEL,
                metrics_url=None,
                extra_headers=headers,
                provider_order=order,
                allow_fallbacks=fallbacks in ("true", "1", "yes"),
                reasoning_effort=effort,
                reasoning_max_tokens=reasoning_max,
                **sampling,
            )

        kind = env.get("LOCAL_SERVER_KIND", "vllm").strip().lower()
        if kind not in SERVER_KINDS:
            raise ConfigError(f"LOCAL_SERVER_KIND must be one of {SERVER_KINDS}, got {kind!r}")
        base_url = env.get("LOCAL_SERVER_URL", "").strip() or LOCAL_DEFAULT_URLS[kind]
        return cls(
            backend=backend,
            server_kind=kind,
            base_url=base_url,
            api_key=env.get("LOCAL_API_KEY", "").strip() or "EMPTY",
            model=env.get("LOCAL_MODEL", "").strip() or LOCAL_DEFAULT_MODEL,
            metrics_url=env.get("LOCAL_METRICS_URL", "").strip() or _metrics_url_from_base(base_url),
            **sampling,
        )


@dataclass
class ChatCompletionResult:
    content: str
    reasoning: str
    finish_reason: str | None
    response_id: str | None
    prompt_tokens: int | None
    completion_tokens: int | None
    cached_tokens: int | None
    ttft_s: float
    e2e_s: float
    chunk_gaps_s: list[float]
    served_model: str | None = None
    provider: str | None = None
    cost_usd: float | None = None

    @property
    def tpot_s(self) -> float:
        """Mean time per output token after the first, from server-reported token counts."""
        if not self.completion_tokens or self.completion_tokens < 2 or math.isnan(self.ttft_s):
            return float("nan")
        return (self.e2e_s - self.ttft_s) / (self.completion_tokens - 1)

    @property
    def itl_mean_s(self) -> float:
        """Mean gap between streamed chunks (a chunk may carry several tokens on some providers)."""
        return statistics.fmean(self.chunk_gaps_s) if self.chunk_gaps_s else float("nan")

    def itl_quantile_s(self, q: float) -> float:
        if not self.chunk_gaps_s:
            return float("nan")
        ordered = sorted(self.chunk_gaps_s)
        return ordered[min(len(ordered) - 1, int(q * len(ordered)))]

    @property
    def prefix_hit_rate(self) -> float:
        if self.cached_tokens is None or not self.prompt_tokens:
            return float("nan")
        return self.cached_tokens / self.prompt_tokens


def _get(obj: Any, name: str) -> Any:
    if obj is None:
        return None
    if isinstance(obj, Mapping):
        return obj.get(name)
    value = getattr(obj, name, None)
    if value is None:
        extra = getattr(obj, "model_extra", None) or {}
        value = extra.get(name)
    return value


def _reasoning_delta(delta: Any) -> str:
    # vLLM/SGLang reasoning parsers emit `reasoning_content`; OpenRouter emits `reasoning`.
    for name in ("reasoning_content", "reasoning"):
        value = _get(delta, name)
        if isinstance(value, str) and value:
            return value
    return ""


class GlimmerClient:
    """Streaming chat client. One instance per run; it is not shared across threads."""

    def __init__(self, config: BackendConfig) -> None:
        from openai import OpenAI

        self.config = config
        self._client = OpenAI(
            base_url=config.base_url,
            api_key=config.api_key,
            timeout=config.timeout_s,
            max_retries=config.max_http_retries,
            default_headers=dict(config.extra_headers) or None,
        )

    @classmethod
    def from_env(cls) -> "GlimmerClient":
        return cls(BackendConfig.from_env())

    def chat(self, messages: Sequence[Mapping[str, str]]) -> ChatCompletionResult:
        cfg = self.config
        kwargs: dict[str, Any] = dict(
            model=cfg.model,
            messages=[dict(m) for m in messages],
            temperature=cfg.temperature,
            top_p=cfg.top_p,
            max_tokens=cfg.max_tokens,
            stream=True,
            stream_options={"include_usage": True},
        )
        if cfg.seed is not None:
            kwargs["seed"] = cfg.seed
        if cfg.backend == "openrouter":
            extra_body: dict[str, Any] = {"usage": {"include": True}}
            if cfg.provider_order:
                extra_body["provider"] = {"order": list(cfg.provider_order), "allow_fallbacks": cfg.allow_fallbacks}
            if cfg.reasoning_effort is not None:
                extra_body["reasoning"] = {"effort": cfg.reasoning_effort}
            elif cfg.reasoning_max_tokens is not None:
                extra_body["reasoning"] = {"max_tokens": cfg.reasoning_max_tokens}
            kwargs["extra_body"] = extra_body

        content: list[str] = []
        reasoning: list[str] = []
        arrivals: list[float] = []
        usage: Any = None
        finish_reason: str | None = None
        response_id: str | None = None
        served_model: str | None = None
        provider: str | None = None

        t_start = time.perf_counter()
        stream = self._client.chat.completions.create(**kwargs)
        try:
            for chunk in stream:
                now = time.perf_counter()
                response_id = response_id or _get(chunk, "id")
                served_model = served_model or _get(chunk, "model")
                provider = provider or _get(chunk, "provider")
                chunk_usage = _get(chunk, "usage")
                if chunk_usage is not None:
                    usage = chunk_usage
                for choice in _get(chunk, "choices") or []:
                    delta = _get(choice, "delta")
                    text = _get(delta, "content") or ""
                    thought = _reasoning_delta(delta)
                    if text or thought:
                        arrivals.append(now)
                    if text:
                        content.append(text)
                    if thought:
                        reasoning.append(thought)
                    finish_reason = _get(choice, "finish_reason") or finish_reason
        finally:
            close = getattr(stream, "close", None)
            if callable(close):
                close()
        t_end = time.perf_counter()

        details = _get(usage, "prompt_tokens_details")
        cached = _get(details, "cached_tokens")
        cost = _get(usage, "cost")
        return ChatCompletionResult(
            content="".join(content),
            reasoning="".join(reasoning),
            finish_reason=finish_reason,
            response_id=response_id,
            prompt_tokens=_get(usage, "prompt_tokens"),
            completion_tokens=_get(usage, "completion_tokens"),
            cached_tokens=int(cached) if cached is not None else None,
            ttft_s=(arrivals[0] - t_start) if arrivals else float("nan"),
            e2e_s=t_end - t_start,
            chunk_gaps_s=[b - a for a, b in zip(arrivals, arrivals[1:])],
            served_model=served_model,
            provider=provider,
            cost_usd=float(cost) if cost is not None else None,
        )
