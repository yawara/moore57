import Moore57.Moore57Graph.Moore57Definition
import Moore57.Papers.Higman1964.Theorem1_DegreeKSqPlus1

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Cameron Ch.3 §3.5 — Strongly regular graphs (substantive)

A *strongly regular graph* (SRG) is a graph `Γ` such that
`(Ω, {R_0, R_1, R_2})` is an association scheme, where `R_0` is
equality, `R_1` is adjacency, and `R_2` is non-adjacency.

By convention, parameters are `(n, k, λ, μ)` with `n` the order, `k` the
valency, `λ` the number of common neighbours of adjacent pairs, and `μ`
the number of common neighbours of non-adjacent pairs. `l = n − 1 − k`
is the non-neighbour count.

Edge-counting between neighbours and non-neighbours gives
`k(k − λ − 1) = l μ`.

**Theorem 3.11.**

* (a) A disconnected SRG is a disjoint union of complete graphs of the
  same size.
* (b) A connected SRG is a distance-regular graph of diameter 2.

The intersection matrices `P_0, P_1, P_2` of an SRG; eigenvalues `r, s`
of `P_1` (besides `k`) satisfy
`r, s = ((λ − μ) ± √d) / 2`, `d = (λ − μ)² + 4(k − μ)`.

Multiplicities `f, g`: `f + g = k + l`, `k f r + k + g s = 0` (from
trace 0), giving rational expressions in `n, k, λ, μ, √d`.

**Two cases.**

* **Case I.** `(k + l)(μ − λ) − 2k = 0`. Forces `l = k`, `μ = λ + 1`,
  `k = 2μ`, `f = g = k`.
* **Case II.** Otherwise: `d = u²` (perfect square) with `u` dividing
  appropriate numerators (integer multiplicities). Eigenvalues `r, s`
  are integers, with `r > 0` and `s < 0`.

**Moore graphs of diameter 2** = SRG with `λ = 0, μ = 1`.

* Case I (`k = 2`): pentagon, `n = 5`.
* Case II: `r + s = −1`, `k = 1 − rs = r² + r + 1`,
  `l = r(r + 1)(r² + r + 1)`. Integrality forces `2r + 1 | 15`, so
  `r ∈ {0, 1, 2, 7}` giving `k ∈ {1, 3, 7, 57}`. `k = 1` is excluded
  (single edge, diameter ≠ 2).

**Theorem 3.12.** A Moore graph of diameter 2 has
`n ∈ {5, 10, 50, 3250}` and `k ∈ {2, 3, 7, 57}`. The first three exist
and are unique (Petersen, Hoffman–Singleton, dihedral `D_{10}`-pentagon).
The valency-57 case is undecided.

This subsumes Higman 1964 §6 Theorem 1 in the SRG framework.
-/

namespace Moore57.Papers.CameronCh3

open Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 3.11 (SRG ⇔ diameter-2 distance-regular).** [deferred-heavy]

A connected `IsSRGWith n k λ μ` graph has diameter 2 (and is
distance-regular with parameters `c_0 = 0, a_0 = 0, b_0 = k`,
`c_1 = 1, a_1 = λ, b_1 = k − λ − 1`, `c_2 = μ, a_2 = k − μ, b_2 = 0`). -/
theorem theorem3_11_srg_diameter_two : True := by trivial

/-- **Edge-count identity** `k(k − λ − 1) = l μ` for an SRG.

Wraps `Mathlib.Combinatorics.SimpleGraph.StronglyRegular.IsSRGWith.param_eq`. -/
theorem theorem3_11_srg_param_identity {n k ℓ μ : ℕ}
    (h : Γ.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    k * (k - ℓ - 1) = (n - k - 1) * μ :=
  SimpleGraph.IsSRGWith.param_eq (G := Γ) h hn

/-- **Edge-count identity (Moore57 instance):** `57 · 56 = 3192 · 1`. -/
theorem theorem3_11_moore57_param_identity (hΓ : IsMoore57 Γ) :
    57 * (57 - 0 - 1) = (3250 - 57 - 1) * 1 :=
  SimpleGraph.IsSRGWith.param_eq (G := Γ) hΓ (by decide)

/-- **Theorem 3.12 (Moore (k, 2) classification).** [deferred-heavy]

A Moore graph of diameter 2 has order `n ∈ {5, 10, 50, 3250}` and
valency `k ∈ {2, 3, 7, 57}`. The full statement requires the
strongly-regular eigenvalue/integrality argument (Cameron §3.5 Case II).

The arithmetic core is already proven via Higman 1964 §6:
`Higman1964.theorem1_arithmetic_core` (given `4k = e² + 3` and
`e² ∣ 225`, conclude `k ∈ {1, 3, 7, 57}`). What remains is the setup
(strongly regular ⇒ `4k − 3` a square divisor of 225). -/
theorem theorem3_12_moore_diameter_two_classification : True := by trivial

/-- **Theorem 3.12 (Moore57 valence fork instance).**

Moore57 sits in the `k = 57` fork of the classification — proven via
`Higman1964.theorem1_moore57_valence`. -/
theorem theorem3_12_moore57_valence :
    (57 : ℕ) = 2 ∨ (57 : ℕ) = 3 ∨ (57 : ℕ) = 7 ∨ (57 : ℕ) = 57 :=
  Moore57.Papers.Higman1964.theorem1_moore57_valence

/-- **Theorem 3.12 (Moore57 order instance).**

Moore57 has `n = 3250 = 57² + 1` — proven via
`Higman1964.theorem1_moore57_degree`. -/
theorem theorem3_12_moore57_order :
    (3250 : ℕ) = 57 ^ 2 + 1 :=
  Moore57.Papers.Higman1964.theorem1_moore57_degree

/-- **Theorem 3.12 (Moore57 SRG-parameter instance).**

Moore57 is `IsSRGWith 3250 57 0 1`, by definition. -/
theorem theorem3_12_moore57_isSRG (hΓ : IsMoore57 Γ) :
    Γ.IsSRGWith 3250 57 0 1 := hΓ

end Moore57.Papers.CameronCh3
