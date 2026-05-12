# The Moore 57

[![Lean Action CI](https://github.com/yawara/moore57/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/yawara/moore57/actions/workflows/lean_action_ci.yml)

A Lean 4 / Mathlib formalization of the non-existence of the dihedral group
`D₁₉` as a subgroup of `Aut(Γ)` for the hypothetical Moore graph
`Γ = SRG(3250, 57, 0, 1)` of degree 57.

## Main theorem

[`Moore57/Phases/FinalAssembly.lean`](Moore57/Phases/FinalAssembly.lean):

```lean
theorem no_D19_acts_on_Moore57_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] :
    ¬ Nonempty (D19ActsOnMoore57 V Γ)
```

The proof is **unconditional**: no `sorry`, no `admit`, no user-defined
`axiom`, no `opaque`.

## CI guarantee that the proof is unconditional

CI enforces that the main theorem depends only on the following axioms:

* Lean / Mathlib standard: `propext`, `Classical.choice`, `Quot.sound`.
* Compiler-generated `native_decide` axioms (names containing
  `._native.native_decide.ax_`), used to discharge ZMod-19 numeric
  decidability goals.

Implementation: [`Moore57/AxiomsCheck.lean`](Moore57/AxiomsCheck.lean) is
elaborated as part of `lake build`. It runs `Lean.collectAxioms` on the main
theorem and throws an elaboration error if any axiom outside the allowlist
appears. A regression therefore causes `lake build` (and CI) to fail.

CI additionally runs a fast-fail grep for `sorry` / `admit` in proof
positions before invoking `lake build`.

## Building locally

```sh
lake build
```

The library is approximately 500 Lean files (~83k lines) and a full build
takes 10-20 minutes on a modern machine.

To re-verify the axiom guarantee independently:

```sh
lake build Moore57.AxiomsCheck
```

This prints an `axioms check OK: …` info message if successful.

## Citing this repository

This repository contains research artifacts. If you refer to them in an
academic paper, please cite the author, affiliation, repository URL, and the
version or release you used, if applicable.

Suggested citation:

Yawara ISHIDA, A.I.System Research, Inc. *The Moore 57*. Git repository,
https://github.com/yawara/moore57.
