from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from moore57.cover import load_seed14, extend_with_new_star_factor
from moore57.constraints import build_extension_instance
from moore57.verify import verify_girth_voltage

STAR = ROOT / "instances/star35/star_factor_heuristic_partial.json"
SEED = ROOT / "instances/seed14/dfs_extend_t10_solution.json"


def test_seed14_girth_voltage():
    cover, _ = load_seed14(STAR, SEED)
    assert cover.N == 14
    res = verify_girth_voltage(cover)
    assert res["tri_bad_count"] == 0
    assert res["square_bad_count"] == 0


def test_extend15_instance_domains():
    base, _ = load_seed14(STAR, SEED)
    cover = extend_with_new_star_factor(base, STAR, 10)
    inst = build_extension_instance(cover)
    assert inst.n == 56
    assert inst.m == 10
    assert inst.unary_allowed.shape == (10, 56, 56)
    assert inst.pair_allowed.shape == (10, 10, 56, 56)
    assert inst.unary_allowed.sum() > 0
