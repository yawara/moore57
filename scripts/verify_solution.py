#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from moore57.cover import load_seed14, extend_with_new_star_factor
from moore57.constraints import build_extension_instance, complete_cover_from_assignment, verify_extension_assignment
from moore57.cnf import parse_dimacs_assignment, assignment_to_Q
from moore57.io import read_json, write_json
from moore57.verify import verify_cover


def load_solution_cover(path: str | Path, star: str | Path, seed: str | Path):
    data = read_json(path)
    if "candidate_candidate" not in data:
        raise ValueError("solution JSON must contain candidate_candidate")
    from moore57.cover import build_anchor_star
    idxs = data.get("idxs", list(range(data["outside_count"])))
    cover, _ = build_anchor_star(star, int(data["outside_count"]), idxs=idxs)
    for key, p in data["candidate_candidate"].items():
        i, j = map(int, key.split("-"))
        cover.add(i, j, p)
    return cover


def main() -> None:
    ap = argparse.ArgumentParser(description="Verify a moore57 solution JSON or solver assignment.")
    ap.add_argument("--solution", default=None, help="solution JSON containing candidate_candidate")
    ap.add_argument("--solver-out", default=None, help="DIMACS solver output with v-lines")
    ap.add_argument("--map", default=None, help="varmap JSON for solver output")
    ap.add_argument("--star", default="instances/star35/star_factor_heuristic_partial.json")
    ap.add_argument("--seed", default="instances/seed14/dfs_extend_t10_solution.json")
    ap.add_argument("--new-factor-index", type=int, default=10)
    ap.add_argument("--out", default="verification.json")
    ap.add_argument("--skip-spectrum", action="store_true")
    ap.add_argument("--sample-c1", action="store_true")
    args = ap.parse_args()

    ext_check = None
    if args.solver_out:
        if not args.map:
            raise SystemExit("--map is required with --solver-out")
        base, _ = load_seed14(args.star, args.seed)
        cover0 = extend_with_new_star_factor(base, args.star, args.new_factor_index)
        inst = build_extension_instance(cover0)
        status, pos = parse_dimacs_assignment(args.solver_out)
        if status != "sat":
            write_json({"ok": False, "status": status, "reason": "solver output is not SAT"}, args.out)
            return
        Q = assignment_to_Q(args.map, pos)
        ext_check = verify_extension_assignment(inst, Q)
        cover = complete_cover_from_assignment(inst, Q)
    elif args.solution:
        cover = load_solution_cover(args.solution, args.star, args.seed)
    else:
        raise SystemExit("provide --solution or --solver-out")

    ver = verify_cover(cover, spectrum=not args.skip_spectrum, c1_full=not args.sample_c1)
    if ext_check is not None:
        ver["extension_assignment"] = ext_check
        ver["ok"] = ver["ok"] and ext_check["ok"]
    write_json(ver, args.out)
    print(f"ok={ver['ok']} wrote {args.out}")


if __name__ == "__main__":
    main()
