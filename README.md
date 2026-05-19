# The Moore 57

[![Lean Action CI](https://github.com/yawara/moore57/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/yawara/moore57/actions/workflows/lean_action_ci.yml)

A Lean 4 / Mathlib project for the automorphism-group restrictions of the
hypothetical Moore graph of degree 57:

```text
Γ = SRG(3250, 57, 0, 1).
```

The published GitHub Pages tracker is the best entry point for the current
status:

<https://yawara.github.io/moore57/>

It tracks the 35 candidate values of `|Aut(Γ)|`, the 103 finite groups across
those orders, what is already excluded by the Macaj-Siran / Makhnev-Paduchikh
paper route, and which cases are now closed by Lean formalization in this
repository.

## Current Lean-Certified Closures

This project currently gives unconditional Lean proofs excluding the full group
orders `22`, `38`, and `110`.

| Order | Main Lean theorem | File |
| --- | --- | --- |
| `22` | `no_Order22_group_acts_on_Moore57` | [`Moore57/Order22OnMoore57/GroupAction.lean`](Moore57/Order22OnMoore57/GroupAction.lean) |
| `38` | `Moore57_no_order38_structure` | [`Moore57/D19OnMoore57/NoGo.lean`](Moore57/D19OnMoore57/NoGo.lean) |
| `110` | `no_Order110_group_acts_on_Moore57` | [`Moore57/Order22OnMoore57/GroupAction.lean`](Moore57/Order22OnMoore57/GroupAction.lean) |

The order-38 closure combines the two possible groups of order 38:

```lean
theorem no_D19_acts_on_Moore57_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] :
    ¬ Nonempty (D19ActsOnMoore57 V Γ)

theorem no_C38_acts_on_Moore57_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] :
    ¬ Nonempty (C38ActsOnMoore57 V Γ)
```

The D19 theorem was the original central target of the repository. It is now
assembled in [`Moore57/D19OnMoore57/NoGo.lean`](Moore57/D19OnMoore57/NoGo.lean),
not in the older `Moore57/Phases/` path.

## What Is In This Repository

- `Moore57/D19OnMoore57/`: the D19 proof, including the E7 projection,
  character decomposition, rotation-character constancy, and final
  adjacent-moved contradiction.
- `Moore57/C38OnMoore57/`: the cyclic order-38 case.
- `Moore57/Order22OnMoore57/`: the order-22 proof and the order-110 Sylow
  reduction to order 22.
- `Moore57/Papers/`: paper-structured Lean files mirroring Higman,
  Aschbacher, Makhnev-Paduchikh, Cameron, and Macaj-Siran. These pages include
  both proved wrappers and explicit deferred placeholders; see the status pages
  under `docs/papers/`.
- `proofs/`: natural-language proof writeups used to guide the Lean work.
- `docs/`: the static GitHub Pages tracker published at
  <https://yawara.github.io/moore57/>.

## Axiom Check

The main closure theorems are checked by
[`Moore57/AxiomsCheck.lean`](Moore57/AxiomsCheck.lean). The check uses
`Lean.collectAxioms` and allows only:

- Lean / Mathlib standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Compiler-generated `native_decide` axioms used for finite numeric
  decidability goals.

A regression causes `lake build` to fail. CI also rejects `sorry` and `admit`
in proof positions.

To re-run the axiom gate:

```sh
lake build Moore57.AxiomsCheck
```

## Build

```sh
lake build
```

The project is large, so a cold build can take a while; incremental rebuilds
are much faster.

## Contributing

Open cases are listed on the tracker:

<https://yawara.github.io/moore57/contribute.html>

Useful contributions include natural-language proofs for an open candidate
order, Lean formalizations of those arguments, finite-group / GAP checks, and
review of the paper-structured formalization.

## AI-Assisted Development

The formalization was developed with substantial assistance from ChatGPT,
Codex, and Claude Code. Correctness is guaranteed by the Lean kernel and the
axiom allowlist check above, not by any AI tool. ChatGPT/Codex transcripts are
archived under `logs/chatgpt/`.

## Citing This Repository

This repository contains research artifacts. If you refer to them in an
academic paper, please cite the author, affiliation, repository URL, and the
version or release you used, if applicable.

Suggested citation:

Yawara ISHIDA, A.I.System Research, Inc. *The Moore 57*. Git repository,
https://github.com/yawara/moore57.
