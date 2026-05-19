import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp

/-!
# Indicator-vector quadratic forms and PSD lemmas

Foundational layer for spectral / Mohar-style bounds on graphs.

* `indicatorFn S` : the `𝕜`-valued indicator vector `χ_S : V → 𝕜`.
* `dotProduct_indicatorFn_mulVec` : `χ_S^T M χ_S = ∑_{v∈S} ∑_{w∈S} M v w`.
* `dotProduct_indicatorFn_self` : `χ_S · χ_S = |S|`.
* `dotProduct_indicatorFn_mulVec_nonneg_of_isSymm_idempotent`
  : for `E : Matrix V V ℚ` symmetric and idempotent, `χ_S^T E χ_S ≥ 0`.

This file deliberately stays graph-agnostic.  Specializations for the
Moore57 spectral projectors live in `Moore57Graph/E7Matrix/MoharBound.lean`.
-/

namespace Moore57

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `𝕜`-valued indicator (characteristic function) of `S ⊆ V`. -/
def indicatorFn {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (S : Finset V) : V → 𝕜 :=
  fun v => if v ∈ S then 1 else 0

omit [Fintype V] in
@[simp] theorem indicatorFn_apply_mem {𝕜 : Type*} [Zero 𝕜] [One 𝕜]
    {S : Finset V} {v : V} (h : v ∈ S) :
    (indicatorFn S : V → 𝕜) v = 1 := by
  unfold indicatorFn; rw [if_pos h]

omit [Fintype V] in
@[simp] theorem indicatorFn_apply_not_mem {𝕜 : Type*} [Zero 𝕜] [One 𝕜]
    {S : Finset V} {v : V} (h : v ∉ S) :
    (indicatorFn S : V → 𝕜) v = 0 := by
  unfold indicatorFn; rw [if_neg h]

variable {𝕜 : Type*} [CommSemiring 𝕜]

/-- **Quadratic-form double-counting**:
`χ_S^T M χ_S = ∑_{v ∈ S} ∑_{w ∈ S} M v w`. -/
theorem dotProduct_indicatorFn_mulVec
    (M : Matrix V V 𝕜) (S : Finset V) :
    dotProduct (indicatorFn S : V → 𝕜) (M.mulVec (indicatorFn S)) =
      ∑ v ∈ S, ∑ w ∈ S, M v w := by
  classical
  have hSfilter : (Finset.univ : Finset V).filter (· ∈ S) = S :=
    Finset.filter_univ_mem S
  -- Expand outer dotProduct.
  unfold dotProduct
  -- Inner expression: rewrite using `mul_ite` to push indicator-1 outside.
  have hinner : ∀ v : V, (indicatorFn S : V → 𝕜) v *
      (M.mulVec (indicatorFn S)) v =
      if v ∈ S then (M.mulVec (indicatorFn S)) v else 0 := by
    intro v; unfold indicatorFn; split_ifs with h
    · rw [one_mul]
    · rw [zero_mul]
  simp_rw [hinner]
  rw [← Finset.sum_filter, hSfilter]
  -- Goal: ∑ v ∈ S, (M.mulVec χ_S) v = ∑ v ∈ S, ∑ w ∈ S, M v w
  refine Finset.sum_congr rfl (fun v _ => ?_)
  unfold mulVec dotProduct
  have hinner2 : ∀ w : V, M v w * (indicatorFn S : V → 𝕜) w =
      if w ∈ S then M v w else 0 := by
    intro w; unfold indicatorFn; split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  simp_rw [hinner2]
  rw [← Finset.sum_filter, hSfilter]

/-- `χ_S · χ_S = |S|` (as an element of `𝕜`). -/
theorem dotProduct_indicatorFn_self (S : Finset V) :
    dotProduct (indicatorFn S : V → 𝕜) (indicatorFn S) = (S.card : 𝕜) := by
  classical
  have hSfilter : (Finset.univ : Finset V).filter (· ∈ S) = S :=
    Finset.filter_univ_mem S
  unfold dotProduct
  have h : ∀ v : V, (indicatorFn S : V → 𝕜) v * (indicatorFn S : V → 𝕜) v =
      if v ∈ S then (1 : 𝕜) else 0 := by
    intro v; unfold indicatorFn; split_ifs with h
    · rw [one_mul]
    · rw [zero_mul]
  simp_rw [h]
  rw [← Finset.sum_filter, hSfilter, Finset.sum_const, Nat.smul_one_eq_cast]

/-- **PSD for symmetric idempotents**: if `E : Matrix V V ℚ` is symmetric and
idempotent, then `χ_S^T E χ_S ≥ 0`.

Proof: `χ^T E χ = χ^T E E χ = (vecMul χ E) · (E χ) = (Eᵀ χ) · (E χ) = (E χ) · (E χ)
= ∑ ((E χ) v)² ≥ 0`. -/
theorem dotProduct_indicatorFn_mulVec_nonneg_of_isSymm_idempotent
    (E : Matrix V V ℚ) (hsymm : E.IsSymm) (hidem : E * E = E)
    (S : Finset V) :
    0 ≤ dotProduct (indicatorFn S : V → ℚ) (E.mulVec (indicatorFn S)) := by
  classical
  -- Establish `χ^T E χ = (E χ) · (E χ)` via idempotence + symmetry.
  have heE : (E.mulVec (indicatorFn S : V → ℚ)) =
      (E * E).mulVec (indicatorFn S) := by rw [hidem]
  have hkey : dotProduct (indicatorFn S : V → ℚ) (E.mulVec (indicatorFn S)) =
      dotProduct (E.mulVec (indicatorFn S : V → ℚ)) (E.mulVec (indicatorFn S)) := by
    calc dotProduct (indicatorFn S : V → ℚ) (E.mulVec (indicatorFn S))
        = dotProduct (indicatorFn S : V → ℚ)
            ((E * E).mulVec (indicatorFn S)) := by rw [heE]
      _ = dotProduct (indicatorFn S : V → ℚ)
            (E.mulVec (E.mulVec (indicatorFn S))) := by rw [← mulVec_mulVec]
      _ = dotProduct ((indicatorFn S : V → ℚ) ᵥ* E)
            (E.mulVec (indicatorFn S)) := dotProduct_mulVec _ E _
      _ = dotProduct (Eᵀ.mulVec (indicatorFn S : V → ℚ))
            (E.mulVec (indicatorFn S)) := by rw [mulVec_transpose]
      _ = dotProduct (E.mulVec (indicatorFn S : V → ℚ))
            (E.mulVec (indicatorFn S)) := by rw [hsymm.eq]
  rw [hkey]
  unfold dotProduct
  exact Finset.sum_nonneg (fun v _ => mul_self_nonneg _)

end Moore57
