# CLAUDE.md

This repository contains experimental tooling for the degree-57, diameter-2 Moore graph problem. Treat the repository as a computational research workspace, not as production software.

## Mathematical context

A hypothetical graph has parameters:

- vertices: 3250
- degree: 57
- diameter: 2
- strongly regular parameters: `(3250, 57, 0, 1)`

The code works with the local block/cover formulation. Fix a vertex `x`. Its distance-2 layer decomposes into 57 fibers `B_i`, each of size 56. Edges between distinct fibers are perfect matchings represented by permutations `P[i][j]` of `{0, ..., 55}`.

## Current computational target

The main current target is the `14 -> 15` block extension problem:

```text
existing fibers: 0..13
new fiber:       14
unknown perms:   P[14][i] for i = 4..13
```

The generated CNF contains:

- permutation constraints for each unknown matching
- unary forbidden cells from existing length-2 and length-3 paths
- binary nogoods for triangle/square fixed-point obstructions

A SAT result is only useful if the produced assignment passes an independent verifier.

## Commands

Recommended setup:

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e .
pip install -r requirements.txt
```

Generate CNF:

```bash
mkdir -p results/runs/extend15
python scripts/build_extend15_instance.py \
  --cnf results/runs/extend15/extend15.cnf \
  --map results/runs/extend15/extend15.varmap.json
```

Run an external SAT solver, for example:

```bash
kissat results/runs/extend15/extend15.cnf \
  > results/runs/extend15/solver.out \
  2> results/runs/extend15/stderr.log
```

Verify a SAT witness:

```bash
python scripts/verify_solution.py \
  --solver-out results/runs/extend15/solver.out \
  --map results/runs/extend15/extend15.varmap.json \
  --out results/runs/extend15/verification.json
```

Run tests:

```bash
pytest -q
```

## Development rules

- Keep solver code and independent verification code separate.
- Do not treat solver output as evidence unless it is independently verified.
- Put large generated files under `results/runs/<run-name>/`.
- Commit small structured summaries such as `summary.json`, `verification.json`, and selected logs.
- Do not commit huge CNF, proof, or raw solver logs unless deliberately needed as an artifact.
- Keep mathematical derivations in `docs/` and executable code in `src/moore57/` or `scripts/`.
- When adding new constraints, update `docs/model_extend15.md` or create a new model document.

## Result interpretation

- `SAT`: verify the witness, then use it as a seed for `16`-block extension.
- `UNSAT`: preserve the solver proof if available, verify it externally, and analyze the proof/core before claiming a mathematical obstruction.
- `UNKNOWN`: save the best partial assignment and conflict summary if possible.

## Style

Use plain Python with type hints where practical. Prefer explicit permutation arrays over opaque object-heavy abstractions. Keep file formats JSON-compatible so results can be inspected and re-used by other agents.
