import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agent.lean_checker import LeanChecker, LeanToolchainError  # noqa: E402

LEAN_PROJECT = ROOT / "src" / "verification" / "GlimmerVerify"


@pytest.fixture(scope="session")
def lean_checker() -> LeanChecker:
    try:
        checker = LeanChecker(LEAN_PROJECT)
        checker.ensure_built()
    except LeanToolchainError as exc:
        pytest.skip(f"Lean toolchain unavailable: {exc}")
    return checker
