# moore57

Computation scaffolding for local-cover SAT/CSP experiments related to a possible Moore graph with

\[
(v,k,\lambda,\mu)=(3250,57,0,1).
\]

The code here focuses on the permutation-cover formulation around a fixed vertex. The first target is the **14-block to 15-block extension problem**:

* start from a verified 14-fiber local witness;
* append one more outside fiber, with its anchor edges fixed by the 4-anchor star certificate;
* solve for the 10 missing permutations from the new fiber to the existing outside fibers;
* enforce the local triangle/square-free voltage constraints, equivalently the partial row-Latin constraints.

This does **not** prove nonexistence of the degree-57 Moore graph by itself. It is a test instance aimed at finding, or ruling out, a 15-block local extension of a specific 14-block seed.

## Quick start

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e .
```

Build the CNF:

```bash
python scripts/build_extend15_instance.py \
  --cnf results/runs/extend15/extend15.cnf \
  --map results/runs/extend15/extend15.varmap.json
```

Run an external SAT solver, for example Kissat:

```bash
kissat results/runs/extend15/extend15.cnf > results/runs/extend15/solver.out
```

Decode and verify the solver output:

```bash
python scripts/verify_solution.py \
  --solver-out results/runs/extend15/solver.out \
  --map results/runs/extend15/extend15.varmap.json \
  --out results/runs/extend15/verification.json
```

## Current PR status

This branch adds the initial repository contract, documentation, and Claude Code instructions. The intended next step is to add or regenerate the concrete 14-block seed artifacts and full CNF generator/verifier, then run external solvers under `results/runs/`.

## Result policy

For each solver run, commit small structured summaries into `results/runs/<run-name>/`:

```text
summary.json
stdout.log / stderr.log or solver.out
solution.json          # SAT only
verification.json      # SAT only
proof.frat.zst         # UNSAT only, if available
proof_check.log        # UNSAT only, if available
```

A SAT solution is not considered useful until an independent verifier accepts it. An UNSAT result is not considered proof-grade unless a DRAT/FRAT proof has been independently checked.
