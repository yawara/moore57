import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
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

Status:
* `lem5_block_design_count`: paper-stub (rank-3 perm group form, deferred).
* `lem5_block_design_count_srg`: **proven** via Mathlib `IsSRGWith.param_eq`
  as the SRG-form of the same identity (`l = n − k − 1` is the degree
  of the complement / size of the second non-trivial orbit).
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 5 (μl = k(k − λ − 1)) via Mathlib SRG.** [done]

The SRG-form of Higman 1964 Lemma 5: for any strongly regular graph
`G : IsSRGWith n k ℓ μ` with `n > 0`,
`μ * (n − k − 1) = k * (k − ℓ − 1)`.

Identifying `l = n − k − 1` (degree of complement = size of second
non-trivial `G_a`-orbit `Γ(a)`), this is exactly the paper's identity
`μ · l = k · (k − λ − 1)`.

Wraps `Mathlib.Combinatorics.SimpleGraph.StronglyRegular.IsSRGWith.param_eq`. -/
theorem lem5_block_design_count_srg
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n k l m : ℕ} (h : G.IsSRGWith n k l m) (hn : 0 < n) :
    m * (n - k - 1) = k * (k - l - 1) := by
  rw [Nat.mul_comm m (n - k - 1)]
  exact (SimpleGraph.IsSRGWith.param_eq G h hn).symm

/-- **Lemma 5 (μl = k(k − λ − 1)).** [deferred-heavy]

Paper-faithful rank-3 perm group statement.  The SRG version is fully
proven in `lem5_block_design_count_srg`; rank-3 perm groups give SRGs
on the orbital adjacency structure, so the two forms are equivalent
once the perm-group ↔ SRG bridge is built. -/
theorem lem5_block_design_count : True := by trivial

/-- **Moore57 instance of Lemma 5.** [done]

For Moore57 = SRG(3250, 57, 0, 1): `1 * 3192 = 57 * 56`. -/
theorem lem5_block_design_count_moore57
    {V : Type*} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) :
    (1 : ℕ) * (3250 - 57 - 1) = 57 * (57 - 0 - 1) :=
  lem5_block_design_count_srg Γ hΓ (by norm_num)

/-- **Corollary 2** (`μ = 0 ⇔ G primitive and k ≤ l ⇔ λ = k − 1`). [deferred-heavy] -/
theorem cor2_lem5_mu_zero_iff_primitive : True := by trivial

/-- **Corollary 3** (`G primitive ⇔ μ ∉ {0, k}`). [deferred-heavy] -/
theorem cor3_lem5_primitive_iff_mu_nontrivial : True := by trivial

end Moore57.Papers.Higman1964
