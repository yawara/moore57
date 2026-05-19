import Moore57.Moore57Graph.E7Matrix.SpectralDecomposition
import Moore57.Foundations.GraphTheory.InducedTrace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mohar's inequality / expander mixing for Moore57

For any vertex subset `S` of a Moore57 strongly regular graph,
```
−8 + |S|/50  ≤  Tr(S)  ≤  7 + |S|/65,
```
where `Tr(S)` is the induced trace `(∑ deg_{Γ[S]}) / |S|` (rational).

## Proof (spectral / expander-mixing)

Write `χ = χ_S : V → ℚ`, the indicator vector of `S`.

1. **Bridge** (Foundations):
   `inducedDegreeSum Γ S = χ^T A χ` (Mathlib `Matrix.dotProduct`).
2. **Spectral expansion**:
   `A = 57·E_57 + 7·E_7 − 8·E_-8` (from `adjMatrix_eq_spectral_decomp`).
3. **Quadratic forms on projectors**: setting
   `α := χ^T E_7 χ`, `β := χ^T E_-8 χ`,
   - `χ^T E_57 χ = |S|² / 3250` (since `E_57 = (1/3250)·J`),
   - `α ≥ 0`, `β ≥ 0` (PSD: each `E_λ` is symmetric idempotent),
   - `|S|²/3250 + α + β = χ^T (E_57+E_7+E_-8) χ = χ^T χ = |S|`,
   - so `α + β = |S|(3250 − |S|)/3250`.
4. **Algebra**:
   `χ^T A χ = 57·|S|²/3250 + 7α − 8β`.
   * Upper: `χ^T A χ ≤ 57·|S|²/3250 + 7(|S|(3250−|S|)/3250) = |S|²/65 + 7|S|`,
     so `Tr(S) ≤ |S|/65 + 7`.
   * Lower: `χ^T A χ ≥ 57·|S|²/3250 − 8(|S|(3250−|S|)/3250) = |S|²/50 − 8|S|`,
     so `Tr(S) ≥ |S|/50 − 8`.

Heavy spectral machinery: this file uses the existing `E7Matrix`/`E57Matrix`/
`EMinus8Matrix` infrastructure in `Moore57Graph/E7Matrix/SpectralDecomposition`.
-/

namespace Moore57

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Symmetry of spectral projectors -/

omit [Fintype V] [DecidableEq V] in
/-- `J = allOnesMatrix V` is symmetric. -/
theorem allOnesMatrix_isSymm : (allOnesMatrix V).IsSymm := by
  ext v w; simp [allOnesMatrix]

omit [DecidableEq V] in
/-- `E_57 = (1/3250) • J` is symmetric. -/
theorem E57Matrix_isSymm : (E57Matrix V).IsSymm := by
  unfold E57Matrix Matrix.IsSymm
  rw [Matrix.transpose_smul]
  rw [show (allOnesMatrix V)ᵀ = allOnesMatrix V from allOnesMatrix_isSymm]

omit [Fintype V] in
/-- `E_7` is symmetric. -/
theorem E7Matrix_isSymm : (E7Matrix Γ).IsSymm := by
  unfold E7Matrix Matrix.IsSymm
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul,
      Matrix.transpose_add, Matrix.transpose_smul,
      SimpleGraph.transpose_adjMatrix, Matrix.transpose_one,
      show (allOnesMatrix V)ᵀ = allOnesMatrix V from allOnesMatrix_isSymm]

/-- `E_{-8} = I − E_7 − E_57` is symmetric. -/
theorem EMinus8Matrix_isSymm : (EMinus8Matrix Γ).IsSymm := by
  unfold EMinus8Matrix Matrix.IsSymm
  rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_one,
      show (E7Matrix Γ)ᵀ = E7Matrix Γ from E7Matrix_isSymm,
      show (E57Matrix V)ᵀ = E57Matrix V from E57Matrix_isSymm]

/-! ### Quadratic forms on spectral projectors -/

/-- `χ_S^T J χ_S = |S|²`. -/
theorem dotProduct_indicatorFn_allOnesMatrix_mulVec (S : Finset V) :
    dotProduct (indicatorFn S : V → ℚ)
        ((allOnesMatrix V).mulVec (indicatorFn S)) =
      ((S.card : ℚ)) ^ 2 := by
  classical
  rw [dotProduct_indicatorFn_mulVec]
  -- ∑ v ∈ S, ∑ w ∈ S, allOnesMatrix v w = ∑ v ∈ S, ∑ w ∈ S, 1 = |S|² (in ℚ)
  have hentry : ∀ v w : V, (allOnesMatrix V) v w = (1 : ℚ) := by
    intro v w; rfl
  simp_rw [hentry]
  rw [Finset.sum_const, Finset.sum_const]
  rw [Nat.smul_one_eq_cast, nsmul_eq_mul]
  ring

/-- `χ_S^T E_57 χ_S = |S|²/3250` (general; `E_57 = (1/3250)·J`). -/
theorem dotProduct_indicatorFn_E57Matrix_mulVec (S : Finset V) :
    dotProduct (indicatorFn S : V → ℚ)
        ((E57Matrix V).mulVec (indicatorFn S)) =
      ((S.card : ℚ)) ^ 2 / 3250 := by
  classical
  unfold E57Matrix
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_indicatorFn_allOnesMatrix_mulVec]
  ring

/-- `χ_S^T E_7 χ_S ≥ 0` (PSD specialization). -/
theorem dotProduct_indicatorFn_E7Matrix_mulVec_nonneg
    (hΓ : IsMoore57 Γ) (S : Finset V) :
    0 ≤ dotProduct (indicatorFn S : V → ℚ)
        ((E7Matrix Γ).mulVec (indicatorFn S)) :=
  dotProduct_indicatorFn_mulVec_nonneg_of_isSymm_idempotent
    (E7Matrix Γ) E7Matrix_isSymm
    (E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ) S

/-- `χ_S^T E_-8 χ_S ≥ 0` (PSD specialization). -/
theorem dotProduct_indicatorFn_EMinus8Matrix_mulVec_nonneg
    (hΓ : IsMoore57 Γ) (S : Finset V) :
    0 ≤ dotProduct (indicatorFn S : V → ℚ)
        ((EMinus8Matrix Γ).mulVec (indicatorFn S)) :=
  dotProduct_indicatorFn_mulVec_nonneg_of_isSymm_idempotent
    (EMinus8Matrix Γ) EMinus8Matrix_isSymm
    (EMinus8Matrix_mul_EMinus8Matrix_eq_EMinus8Matrix hΓ) S

/-! ### Spectral expansion of `χ_S^T A χ_S` -/

/-- Resolution of identity, applied to `χ`:
`|S|²/3250 + χ^T E_7 χ + χ^T E_-8 χ = |S|`.

Independent of Moore57 hypothesis (uses only `E_57 + E_7 + E_-8 = I`,
which follows from the definition `EMinus8 = 1 − E_7 − E_57`). -/
theorem dotProduct_indicatorFn_spectral_sum (S : Finset V) :
    ((S.card : ℚ)) ^ 2 / 3250 +
      dotProduct (indicatorFn S : V → ℚ) ((E7Matrix Γ).mulVec (indicatorFn S)) +
      dotProduct (indicatorFn S : V → ℚ)
        ((EMinus8Matrix Γ).mulVec (indicatorFn S)) =
      (S.card : ℚ) := by
  classical
  -- LHS factors as `χ^T (E_57 + E_7 + EMinus8) χ = χ^T 1 χ = χ · χ = |S|`.
  have hsum := E57_plus_E7_plus_EMinus8_eq_one (V := V) (Γ := Γ)
  have hchi_self : dotProduct (indicatorFn S : V → ℚ) (indicatorFn S) =
      (S.card : ℚ) := dotProduct_indicatorFn_self S
  have hE57 : dotProduct (indicatorFn S : V → ℚ)
      ((E57Matrix V).mulVec (indicatorFn S)) = ((S.card : ℚ)) ^ 2 / 3250 :=
    dotProduct_indicatorFn_E57Matrix_mulVec S
  -- Express the spectral identity through χ.
  have key : dotProduct (indicatorFn S : V → ℚ)
      ((E57Matrix V + E7Matrix Γ + EMinus8Matrix Γ).mulVec (indicatorFn S)) =
      (S.card : ℚ) := by
    rw [hsum, one_mulVec]
    exact hchi_self
  rw [add_mulVec, add_mulVec, dotProduct_add, dotProduct_add] at key
  rw [hE57] at key
  exact key

/-- Spectral expansion of `χ^T A χ` (dot-product form):
`χ^T A χ = 57·(χ^T E_57 χ) + 7·(χ^T E_7 χ) − 8·(χ^T E_-8 χ)`. -/
theorem dotProduct_indicatorFn_adjMatrix_eq_spectral
    (hΓ : IsMoore57 Γ) (S : Finset V) :
    dotProduct (indicatorFn S : V → ℚ)
        ((Γ.adjMatrix ℚ).mulVec (indicatorFn S)) =
      57 * dotProduct (indicatorFn S : V → ℚ)
        ((E57Matrix V).mulVec (indicatorFn S)) +
      7 * dotProduct (indicatorFn S : V → ℚ)
        ((E7Matrix Γ).mulVec (indicatorFn S)) -
      8 * dotProduct (indicatorFn S : V → ℚ)
        ((EMinus8Matrix Γ).mulVec (indicatorFn S)) := by
  classical
  rw [adjMatrix_eq_spectral_decomp hΓ]
  -- Bilinearity: distribute mulVec, then distribute dotProduct.
  rw [sub_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec]
  rw [dotProduct_sub, dotProduct_add,
      dotProduct_smul, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]

/-! ### Mohar's inequality -/

/-- **Mohar / expander mixing for Moore57** (rearranged form, before division):
```
|S|²/50 − 8·|S| ≤ inducedDegreeSum Γ S ≤ |S|²/65 + 7·|S|
```
(both bounds in `ℚ`).
-/
theorem inducedDegreeSum_bounds (hΓ : IsMoore57 Γ) (S : Finset V) :
    ((S.card : ℚ)) ^ 2 / 50 - 8 * (S.card : ℚ) ≤ (inducedDegreeSum Γ S : ℚ) ∧
      (inducedDegreeSum Γ S : ℚ) ≤ ((S.card : ℚ)) ^ 2 / 65 + 7 * (S.card : ℚ) := by
  classical
  set k : ℚ := (S.card : ℚ) with hk
  set α : ℚ := dotProduct (indicatorFn S : V → ℚ)
    ((E7Matrix Γ).mulVec (indicatorFn S)) with hα
  set β : ℚ := dotProduct (indicatorFn S : V → ℚ)
    ((EMinus8Matrix Γ).mulVec (indicatorFn S)) with hβ
  -- Sum identity: k²/3250 + α + β = k.
  have hsum : k ^ 2 / 3250 + α + β = k :=
    dotProduct_indicatorFn_spectral_sum S
  -- PSD: α ≥ 0, β ≥ 0.
  have hα_nn : 0 ≤ α := dotProduct_indicatorFn_E7Matrix_mulVec_nonneg hΓ S
  have hβ_nn : 0 ≤ β := dotProduct_indicatorFn_EMinus8Matrix_mulVec_nonneg hΓ S
  -- Spectral expansion bridged with inducedDegreeSum.
  have hE57 : dotProduct (indicatorFn S : V → ℚ)
      ((E57Matrix V).mulVec (indicatorFn S)) = k ^ 2 / 3250 := by
    rw [dotProduct_indicatorFn_E57Matrix_mulVec]
  have hexp : (inducedDegreeSum Γ S : ℚ) = 57 * k ^ 2 / 3250 + 7 * α - 8 * β := by
    rw [← dotProduct_indicatorFn_adjMatrix_mulVec,
        dotProduct_indicatorFn_adjMatrix_eq_spectral hΓ, hE57,
        ← hα, ← hβ]
    ring
  refine ⟨?_, ?_⟩
  · -- Lower: inducedDegreeSum ≥ k²/50 - 8k.
    -- Substitute β = k − k²/3250 − α; combined with α ≥ 0 this gives
    -- inducedDegreeSum = k²/50 + 15α − 8k ≥ k²/50 − 8k.
    have hβ_eq : β = k - k ^ 2 / 3250 - α := by linarith
    have h_id : (inducedDegreeSum Γ S : ℚ) = k ^ 2 / 50 + 15 * α - 8 * k := by
      rw [hexp, hβ_eq]; ring
    linarith
  · -- Upper: inducedDegreeSum ≤ k²/65 + 7k.
    have hα_eq : α = k - k ^ 2 / 3250 - β := by linarith
    have h_id : (inducedDegreeSum Γ S : ℚ) = k ^ 2 / 65 + 7 * k - 15 * β := by
      rw [hexp, hα_eq]; ring
    linarith

/-- **Mohar trace bounds for Moore57** (final form):
for any nonempty vertex subset `S`,
`−8 + |S|/50 ≤ inducedTrace Γ S ≤ 7 + |S|/65`. -/
theorem mohar_trace_bounds
    (hΓ : IsMoore57 Γ) {S : Finset V} (hS : S.Nonempty) :
    -8 + (S.card : ℚ) / 50 ≤ inducedTrace Γ S ∧
      inducedTrace Γ S ≤ 7 + (S.card : ℚ) / 65 := by
  classical
  unfold inducedTrace
  have hk_pos : (0 : ℚ) < (S.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  obtain ⟨hlow, hupp⟩ := inducedDegreeSum_bounds hΓ S
  refine ⟨?_, ?_⟩
  · -- Lower: -8 + k/50 ≤ (inducedDegreeSum)/k.
    rw [le_div_iff₀ hk_pos]
    have h_exp : (-8 + (S.card : ℚ) / 50) * (S.card : ℚ) =
        (S.card : ℚ) ^ 2 / 50 - 8 * (S.card : ℚ) := by ring
    linarith
  · -- Upper: (inducedDegreeSum)/k ≤ 7 + k/65.
    rw [div_le_iff₀ hk_pos]
    have h_exp : (7 + (S.card : ℚ) / 65) * (S.card : ℚ) =
        (S.card : ℚ) ^ 2 / 65 + 7 * (S.card : ℚ) := by ring
    linarith

end Moore57
