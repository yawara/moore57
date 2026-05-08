#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from moore57.cover import load_seed14, extend_with_new_star_factor, save_solution
from moore57.constraints import build_extension_instance, complete_cover_from_assignment, verify_extension_assignment
from moore57.io import write_json
from moore57.verify import verify_cover


def main() -> None:
    try:
        from ortools.sat.python import cp_model
    except Exception as e:
        raise SystemExit("OR-Tools is not installed. Install with `pip install ortools`.") from e

    ap = argparse.ArgumentParser(description="Solve extend15 with OR-Tools CP-SAT.")
    ap.add_argument("--star", default="instances/star35/star_factor_heuristic_partial.json")
    ap.add_argument("--seed", default="instances/seed14/dfs_extend_t10_solution.json")
    ap.add_argument("--new-factor-index", type=int, default=10)
    ap.add_argument("--out-dir", default="results/runs/cpsat_extend15")
    ap.add_argument("--time-limit", type=float, default=3600)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--skip-spectrum", action="store_true")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    base, idxs = load_seed14(args.star, args.seed)
    cover0 = extend_with_new_star_factor(base, args.star, args.new_factor_index)
    inst = build_extension_instance(cover0)
    m, n = inst.m, inst.n
    model = cp_model.CpModel()
    x = {}
    for vi in range(m):
        for a in range(n):
            lits = []
            for b in range(n):
                if inst.unary_allowed[vi, a, b]:
                    lit = model.NewBoolVar(f"x_{vi}_{a}_{b}")
                    x[(vi, a, b)] = lit
                    lits.append(lit)
            model.AddExactlyOne(lits)
        for b in range(n):
            lits = [x[(vi, a, b)] for a in range(n) if (vi, a, b) in x]
            model.AddExactlyOne(lits)
    for vi in range(m):
        for vj in range(vi + 1, m):
            bad = (~inst.pair_allowed[vi, vj]).nonzero()
            for a in range(n):
                for b, c in zip(bad[0], bad[1]):
                    if (vi, a, int(b)) in x and (vj, a, int(c)) in x:
                        model.AddBoolOr([x[(vi, a, int(b))].Not(), x[(vj, a, int(c))].Not()])

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_search_workers = args.workers
    t0 = time.time()
    status = solver.Solve(model)
    dt = time.time() - t0
    status_name = solver.StatusName(status).lower()
    summary = {
        "status": status_name,
        "model": "extend15_cpsat",
        "resources": {"wall_seconds": dt},
        "solver": {"name": "ortools_cp_sat", "workers": args.workers, "time_limit": args.time_limit},
        "stats": {"branches": solver.NumBranches(), "conflicts": solver.NumConflicts(), "wall_time": solver.WallTime()},
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        import numpy as np
        Q = -np.ones((m, n), dtype=np.int16)
        for vi in range(m):
            for a in range(n):
                for b in range(n):
                    lit = x.get((vi, a, b))
                    if lit is not None and solver.Value(lit):
                        Q[vi, a] = b
        ext_check = verify_extension_assignment(inst, Q)
        full = complete_cover_from_assignment(inst, Q)
        sol_path = out_dir / "solution.json"
        save_solution(full, sol_path, meta={"cpsat": summary, "extension_check": ext_check}, idxs=idxs + [args.new_factor_index])
        ver = verify_cover(full, spectrum=not args.skip_spectrum, c1_full=True)
        ver_path = out_dir / "verification.json"
        write_json(ver, ver_path)
        summary["output"] = {"solution": str(sol_path), "verification": str(ver_path)}
        summary["verification_ok"] = bool(ver["ok"] and ext_check["ok"])
    write_json(summary, out_dir / "summary.json")
    print(f"status={status_name} summary={out_dir / 'summary.json'}")


if __name__ == "__main__":
    main()
