# How to run external solvers

## CNF + Kissat

```bash
mkdir -p results/runs/kissat_extend15
python scripts/build_extend15_instance.py \
  --cnf results/runs/kissat_extend15/extend15.cnf \
  --map results/runs/kissat_extend15/extend15.varmap.json
kissat results/runs/kissat_extend15/extend15.cnf \
  > results/runs/kissat_extend15/solver.out \
  2> results/runs/kissat_extend15/stderr.log
python scripts/verify_solution.py \
  --solver-out results/runs/kissat_extend15/solver.out \
  --map results/runs/kissat_extend15/extend15.varmap.json \
  --out results/runs/kissat_extend15/verification.json
```

## CNF + CaDiCaL

```bash
cadical results/runs/cadical_extend15/extend15.cnf \
  > results/runs/cadical_extend15/solver.out
```

## CP-SAT

OR-Tools support is planned as a second backend. For proof-oriented runs, prefer CNF plus a SAT solver that can emit DRAT/FRAT.

## Notes

* If SAT, always run the independent verifier.
* If UNSAT, prefer solvers that emit DRAT/FRAT and commit the proof plus checker log.
* A timeout should be recorded as `unknown`, not as evidence of UNSAT.
