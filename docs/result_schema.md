# Result schema

Each run directory should contain a `summary.json` with the following fields where possible.

```json
{
  "status": "sat | unsat | unknown | built",
  "model": "extend15",
  "seed": "instances/seed14/dfs_extend_t10_solution.json",
  "star": "instances/star35/star_factor_heuristic_partial.json",
  "new_factor_index": 10,
  "cnf": "results/runs/.../extend15.cnf",
  "varmap": "results/runs/.../extend15.varmap.json",
  "cnf_stats": {},
  "solver": {
    "name": "kissat",
    "command": ["kissat", "extend15.cnf"],
    "returncode": 10
  },
  "resources": {
    "wall_seconds": 0.0,
    "memory_mb": null
  },
  "output": {
    "solution": "solution.json",
    "verification": "verification.json",
    "proof": null
  },
  "verification_ok": true
}
```

For UNSAT runs, include a proof if the solver can emit one:

```text
proof.frat.zst
proof_check.log
```

For UNKNOWN runs, include any partial assignment or conflict report if available.
