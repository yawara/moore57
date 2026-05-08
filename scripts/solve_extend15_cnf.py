#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import shlex
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from moore57.cover import load_seed14, extend_with_new_star_factor, save_solution
from moore57.constraints import build_extension_instance, complete_cover_from_assignment, verify_extension_assignment
from moore57.cnf import build_extend_cnf, parse_dimacs_assignment, assignment_to_Q
from moore57.io import write_json
from moore57.verify import verify_cover


def main() -> None:
    ap = argparse.ArgumentParser(description="Generate and optionally solve the extend15 CNF.")
    ap.add_argument("--star", default="instances/star35/star_factor_heuristic_partial.json")
    ap.add_argument("--seed", default="instances/seed14/dfs_extend_t10_solution.json")
    ap.add_argument("--new-factor-index", type=int, default=10)
    ap.add_argument("--cnf", required=True)
    ap.add_argument("--map", default=None)
    ap.add_argument("--solver", default=None, help="solver executable, e.g. kissat or cadical")
    ap.add_argument("--solver-args", default="", help="extra solver args as a shell-like string")
    ap.add_argument("--out-dir", default="results/runs/manual_extend15")
    ap.add_argument("--no-solve", action="store_true")
    ap.add_argument("--skip-spectrum", action="store_true")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    base, idxs = load_seed14(args.star, args.seed)
    cover = extend_with_new_star_factor(base, args.star, args.new_factor_index)
    inst = build_extension_instance(cover)
    map_path = args.map or str(Path(args.cnf).with_suffix(".varmap.json"))
    build = build_extend_cnf(inst, args.cnf, map_path)
    summary = {
        "status": "built",
        "model": "extend15",
        "seed": args.seed,
        "star": args.star,
        "new_factor_index": args.new_factor_index,
        "cnf": str(args.cnf),
        "varmap": str(map_path),
        "cnf_stats": build.stats,
    }
    if args.no_solve or not args.solver:
        write_json(summary, out_dir / "summary.json")
        print(f"CNF built. summary={out_dir / 'summary.json'}")
        return

    cmd = [args.solver] + shlex.split(args.solver_args) + [str(args.cnf)]
    t0 = time.time()
    proc = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    dt = time.time() - t0
    (out_dir / "stdout.log").write_text(proc.stdout, encoding="utf-8")
    (out_dir / "stderr.log").write_text(proc.stderr, encoding="utf-8")
    solver_out = out_dir / "solver.out"
    solver_out.write_text(proc.stdout, encoding="utf-8")
    status, pos = parse_dimacs_assignment(solver_out)
    summary.update({
        "status": status,
        "solver": {"command": cmd, "returncode": proc.returncode},
        "resources": {"wall_seconds": dt},
    })
    if status == "sat":
        Q = assignment_to_Q(map_path, pos)
        ext_check = verify_extension_assignment(inst, Q)
        full = complete_cover_from_assignment(inst, Q)
        sol_path = out_dir / "solution.json"
        save_solution(full, sol_path, meta={"solver": summary["solver"], "extension_check": ext_check}, idxs=idxs + [args.new_factor_index])
        ver = verify_cover(full, spectrum=not args.skip_spectrum, c1_full=True)
        ver_path = out_dir / "verification.json"
        write_json(ver, ver_path)
        summary["output"] = {"solution": str(sol_path), "verification": str(ver_path)}
        summary["verification_ok"] = bool(ver["ok"] and ext_check["ok"])
    write_json(summary, out_dir / "summary.json")
    print(f"status={status} summary={out_dir / 'summary.json'}")


if __name__ == "__main__":
    main()
