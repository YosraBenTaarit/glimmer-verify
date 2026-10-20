"""Request reconstruction and conditions of the collapse replay experiment (no API calls)."""

import pytest

from src.agent import prompts
from src.experiments.replay_collapse import PLACEHOLDER, apply_condition, classify, request_prefix


def conversation(n_attempts=3):
    messages = [{"role": "system", "content": "sys"}, {"role": "user", "content": "task"}]
    for k in range(1, n_attempts + 1):
        messages += [{"role": "assistant", "content": ""},
                     {"role": "user", "content": prompts.feedback_for_missing_code(k, 9, truncated=True)}]
    messages.append({"role": "assistant", "content": ""})
    return {"messages": messages}


def test_request_prefix_matches_attempt():
    base = request_prefix(conversation(), 4)
    assert [m["role"] for m in base] == ["system", "user"] + ["assistant", "user"] * 3
    with pytest.raises(ValueError):
        request_prefix(conversation(), 6)


def test_conditions_change_only_their_target():
    base = request_prefix(conversation(), 4)
    assert apply_condition(base, "original") == base
    neutral = apply_condition(base, "neutral")
    assert all("be more concise" not in m["content"] for m in neutral)
    assert [m for m in neutral if m["role"] == "assistant"] == [m for m in base if m["role"] == "assistant"]
    placeholder = apply_condition(base, "placeholder")
    assert [m["content"] for m in placeholder if m["role"] == "assistant"] == [PLACEHOLDER] * 3
    assert [m for m in placeholder if m["role"] == "user"] == [m for m in base if m["role"] == "user"]
    assert base[2]["content"] == ""


def test_classify():
    assert classify("", "stop", 4) == "empty"
    assert classify("anything", "length", 4096) == "truncated"
    assert classify("```lean\ntheorem t : True := trivial\n```", "stop", 20) == "code"
    assert classify(PLACEHOLDER, "stop", 10) == "text_without_code"
