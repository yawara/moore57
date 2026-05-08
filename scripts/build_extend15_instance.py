#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from moore57.cover import load_seed14, extend_with_new_star_factor
from moore57.constraints import build_extension_instance
from moore57.cnf import build_extend_cnf
from moore57.io import write_json


def main() -> None:
    ap = argparse.ArgumentParser(description="Build the 14->15 block extension instance and optional CNF.")
    ap.add_argument("--star", default="instances/star35/star_factor_heuristic_partial.json")
    ap.add_argument("--seed", default="instances/seed14/dfs_extend_t10_solution.json")
    ap.add_argument("--new-factor-index", type=int, default=10, help="star factor index for the new outside block")
    ap.add_argument("--instance", default="instances/seed14/instance_extend15.json")
    ap.add_argument("--cnf", default=None)
    ap.add_argument("--map", default=None)
    args = ap.parse_args()

    base, idxs = load_seed14(args.star, args.seed)
    cover = extend_with_new_star_factor(base, args.star, args.new_factor_index)
    inst = build_extension_instance(cover)
    unary_total = int(inst.unary_allowed.sum())
    unary_bad = int(inst.unary_allowed.size - unary_total)
    pair_bad = 0
    for i in range(inst.m):
        for j in range(i + 1, inst.m):
            pair_bad += int((~inst.pair_allowed[i, j]).sum())
    data = {
        "format": "moore57_extend_instance_v1",
        "model": "extend_one_block",
        "sheet_size": inst.n,
        "existing_fibers": base.N,
        "total_fibers_after_extension": cover.N,
        "new_fiber": inst.new,
        "unknown_fibers": inst.vars,
        "star_file": args.star,
        "seed_file": args.seed,
        "new_factor_index": args.new_factor_index,
        "base_idxs": idxs,
        "stats": {
            "num_unknown_perms": inst.m,
            "bool_cells_total": inst.m * inst.n * inst.n,
            "unary_allowed_cells": unary_total,
            "unary_forbidden_cells": unary_bad,
            "pair_forbidden_templates": pair_bad,
            "rowwise_pair_forbidden_clauses_upper_bound": pair_bad * inst.n,
        },
    }
    write_json(data, args.instance)
    print(f"wrote instance metadata: {args.instance}")
    print(data["stats"])
    if args.cnf:
        map_path = args.map or str(Path(args.cnf).with_suffix(".varmap.json"))
        res = build_extend_cnf(inst, args.cnf, map_path)
        print(f"wrote CNF: {res.cnf_path}")
        print(f"wrote varmap: {res.map_path}")
        print(res.stats)


if __name__ == "__main__":
    main()
