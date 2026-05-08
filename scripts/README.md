# scripts

This directory is reserved for executable tooling around the `extend15` experiment.

Planned commands:

```bash
python scripts/build_extend15_instance.py --cnf results/runs/extend15/extend15.cnf --map results/runs/extend15/extend15.varmap.json
python scripts/verify_solution.py --solver-out results/runs/extend15/solver.out --map results/runs/extend15/extend15.varmap.json --out results/runs/extend15/verification.json
```

The current PR establishes the repository contract and Claude Code instructions first. Solver generators, verifiers, and seed artifacts should be added under this directory and `src/moore57/`.
