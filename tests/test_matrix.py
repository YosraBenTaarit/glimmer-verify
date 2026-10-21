"""Protocol expansion for the factorial runner (no API calls)."""

from src.experiments.matrix import cell_dir, cells


def test_cells_are_the_cartesian_product(tmp_path):
    protocol = {"name": "p", "axes": {"memory": ["append", "last_error"], "seed": [1, 2, 3]}}
    got = cells(protocol)
    assert len(got) == 6
    assert got[0] == {"memory": "append", "seed": 1}
    assert {c["memory"] for c in got} == {"append", "last_error"}
    name = cell_dir(tmp_path, {"memory": "last_error", "seed": 2}).name
    assert "memory=last_error" in name and "seed=2" in name
