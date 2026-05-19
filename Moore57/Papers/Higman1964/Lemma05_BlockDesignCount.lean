import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 5 (§3, Block-design count)

> For the rank-3 block design `A` with parameters `(n, k, λ, μ, l)`,
>
> `μ · l = k · (k − λ − 1)`.

**Proof sketch.** Fix a block `B = Δ*(b)` in `A`. Count pairs `(A, a)`
with `A` a block `≠ B` and `a ∈ A ∩ B`:
* The `k` blocks through `b` (other than `B`) each meet `B` in `λ` points.
* The `l` blocks not through `b` each meet `B` in `μ` points.
* Each of the `k` points on `B` lies on `k − 1` blocks `≠ B`.

Hence `λk + μl = k(k − 1)`, giving `μl = k(k − λ − 1)`.

**Corollary 1** (to Lemma 5). If `|G|` is odd, `λ = μ = (k − 1) / 2`.

**Corollary 2.** The conditions
* (a) `G` primitive and `k ≤ l`,
* (b) `μ = 0`,
* (c) `λ = k − 1`,
are equivalent.

**Corollary 3.** `G` is primitive iff `μ ∉ {0, k}`.

For the Moore57 application: rank-3 with `n = 3250 = 57² + 1`, `k = 57`,
`l = 3192`, so `μ · 3192 = 57 · (57 − 0 − 1) = 57 · 56 = 3192`, hence
`μ = 1`. Combined with `λ = 0` (this is exactly the strong (0, 1) /
Moore graph condition).

[skeleton]
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 5 (μl = k(k − λ − 1)).** [skeleton] -/
theorem lem5_block_design_count : True := by trivial

/-- **Corollary 2** (`μ = 0 ⇔ G primitive and k ≤ l ⇔ λ = k − 1`). [skeleton] -/
theorem cor2_lem5_mu_zero_iff_primitive : True := by trivial

/-- **Corollary 3** (`G primitive ⇔ μ ∉ {0, k}`). [skeleton] -/
theorem cor3_lem5_primitive_iff_mu_nontrivial : True := by trivial

end Moore57.Papers.Higman1964
