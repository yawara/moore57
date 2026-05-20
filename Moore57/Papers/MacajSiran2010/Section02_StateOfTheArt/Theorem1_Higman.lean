import Moore57.Moore57Graph.HigmanTrace.Congruence
import Moore57.Foundations.Representation.PermutationRepresentationCharacter
import Moore57.Moore57Graph.E7Matrix.SpectralDecomposition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Theorem 1 (Higman trace identity)

> Let Γ be a Moore (57, 2)-graph with adjacency matrix `A`. Let `V₀, V₁, V₂`
> be the eigenspaces of `A` for eigenvalues 57, 7, −8 respectively. Let `X`
> be an automorphism group of Γ and let `χ₀, χ₁, χ₂` be characters of the
> restriction of `X` onto `V₀, V₁, V₂`. Set `a_i(x) = |{v : d(v, vx) = i}|`.
> Then
> ```
> (χ₀(x), χ₁(x), χ₂(x))ᵀ = Q (a₀(x), a₁(x), a₂(x))ᵀ
> ```
> with `Q = P⁻¹` and explicit `P, Q` matrices.

We expose three scalar consequences of the matrix identity, each provable
from the existing spectral-projection infrastructure:

* `thm1_chi0`  — `χ₀(σ) = 1`.
* `thm1_chi1_formula` — `χ₁(σ) = (8 a₀(σ) + a₁(σ) − 65) / 15`
  (= the paper's row-1 component of `Q · (a₀,a₁,a₂)ᵀ`).
* `thm1_chi2_formula` — `χ₂(σ) = (7 a₀(σ) − a₁(σ) + 50) / 15`. [deferred-heavy]
  Derivable from `tr(P_σ) = a₀` and `E_57 + E_7 + E_-8 = I`.
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 1 (χ₀ component).** `χ₀(σ) = trace(E_57 · P_σ) = 1`. -/
theorem thm1_chi0 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    Matrix.trace (E57Matrix V * permMatrix σ) = 1 :=
  trace_E57Matrix_mul_permMatrix hΓ σ

/-- **Theorem 1 (χ₁ component).**
For any automorphism `σ` of Γ, `χ₁(σ) = (1/15)(8 a₀(σ) + a₁(σ) − 65)`. -/
theorem thm1_chi1_formula (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    Matrix.trace (E7Matrix Γ * permMatrix σ) =
      (8 * (fixedVertexCount σ : ℚ) + (adjacentMovedCount Γ σ : ℚ) - 65) / 15 :=
  hΓ.higman_trace_formula σ

/-- **Theorem 1 (χ₂ component).** `χ₂(σ) = (1/15)(7 a₀(σ) − a₁(σ) + 50)`. -/
theorem thm1_chi2_formula (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    Matrix.trace (EMinus8Matrix Γ * permMatrix σ) =
      (7 * (fixedVertexCount σ : ℚ) - (adjacentMovedCount Γ σ : ℚ) + 50) / 15 := by
  -- χ_0 + χ_1 + χ_2 = trace(P_σ) = fixedVertexCount σ
  have hdecomp := trace_decomp_via_spectral (Γ := Γ) σ 1
  simp only [pow_one] at hdecomp
  have htraceP : Matrix.trace (permMatrix σ) = (fixedVertexCount σ : ℚ) :=
    trace_permMatrix_eq_fixedVertexCount σ
  have hchi0 : Matrix.trace (E57Matrix V * permMatrix σ) = 1 :=
    trace_E57Matrix_mul_permMatrix hΓ σ
  have hchi1 := hΓ.higman_trace_formula σ
  linarith [hdecomp, htraceP, hchi0, hchi1]

/-! ### Inverse formulas: `aᵢ` as ℤ-linear combinations of `χⱼ`

The paper's matrix identity `(χ₀, χ₁, χ₂)ᵀ = Q (a₀, a₁, a₂)ᵀ` with `Q = P⁻¹`
inverts to `(a₀, a₁, a₂)ᵀ = P (χ₀, χ₁, χ₂)ᵀ`, where

```
P = ⎛   1     1     1  ⎞
    ⎜  57     7    −8  ⎟
    ⎝ 3192   −8     7  ⎠
```

This `P` is read off from the spectral decomposition
`A = 57·E_57 + 7·E_7 + (−8)·E_{−8}` plus the trivial identities
`I = E_57 + E_7 + E_{−8}` and `J = 3250·E_57` (since `tr(J·P_σ) = |V| = 3250`).
-/

/-- **Theorem 1 inverse, a₀ row.** `a₀(σ) = χ₀(σ) + χ₁(σ) + χ₂(σ)`.

Proof: pure trace decomposition `tr P_σ = tr((E_57+E_7+E_{−8})·P_σ)`. -/
theorem thm1_a0_eq_chi_sum (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    (fixedVertexCount σ : ℚ) =
      Matrix.trace (E57Matrix V * permMatrix σ) +
      Matrix.trace (E7Matrix Γ * permMatrix σ) +
      Matrix.trace (EMinus8Matrix Γ * permMatrix σ) := by
  have hdecomp := trace_decomp_via_spectral (Γ := Γ) σ 1
  simp only [pow_one] at hdecomp
  have htraceP : Matrix.trace (permMatrix σ) = (fixedVertexCount σ : ℚ) :=
    trace_permMatrix_eq_fixedVertexCount σ
  linarith [hdecomp, htraceP]

/-- **Theorem 1 inverse, a₁ row.** `a₁(σ) = 57·χ₀(σ) + 7·χ₁(σ) − 8·χ₂(σ)`.

Proof: from `A = 57·E_57 + 7·E_7 − 8·E_{−8}`,
`tr(A·P_σ) = 57·tr(E_57·P_σ) + 7·tr(E_7·P_σ) − 8·tr(E_{−8}·P_σ)`,
and `tr(A·P_σ) = a₁(σ)` by
`trace_adjMatrix_mul_permMatrix_eq_adjacentMovedCount`. -/
theorem thm1_a1_eq_chi_combination (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    (adjacentMovedCount Γ σ : ℚ) =
      57 * Matrix.trace (E57Matrix V * permMatrix σ) +
      7 * Matrix.trace (E7Matrix Γ * permMatrix σ) +
      (-8) * Matrix.trace (EMinus8Matrix Γ * permMatrix σ) := by
  have hA : Γ.adjMatrix ℚ =
      (57 : ℚ) • E57Matrix V + (7 : ℚ) • E7Matrix Γ - (8 : ℚ) • EMinus8Matrix Γ :=
    adjMatrix_eq_spectral_decomp hΓ
  have htrAP : Matrix.trace (Γ.adjMatrix ℚ * permMatrix σ) =
      (adjacentMovedCount Γ σ : ℚ) :=
    trace_adjMatrix_mul_permMatrix_eq_adjacentMovedCount Γ σ
  rw [← htrAP, hA]
  simp [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  ring

/-- **Theorem 1 inverse, a₂ row.** `a₂(σ) = 3192·χ₀(σ) − 8·χ₁(σ) + 7·χ₂(σ)`.

Where `a₂(σ) := |V| − a₀(σ) − a₁(σ)` is the count of vertices at distance
2 (diameter 2 ⟹ every vertex is at distance 0, 1, or 2 from its image).

Derivation: combine `a₀ = χ₀ + χ₁ + χ₂` (Theorem 1 a₀ row) and
`a₁ = 57·χ₀ + 7·χ₁ − 8·χ₂` (a₁ row) and `|V| = 3250`:
`a₂ = 3250 − (χ₀ + χ₁ + χ₂) − (57·χ₀ + 7·χ₁ − 8·χ₂) = 3192 − 8·χ₁ + 7·χ₂`.
Using `χ₀ = 1` (which is true for all `σ`), this becomes
`3192·χ₀ − 8·χ₁ + 7·χ₂`. -/
theorem thm1_a2_eq_chi_combination (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    ((Fintype.card V : ℚ) - (fixedVertexCount σ : ℚ) - (adjacentMovedCount Γ σ : ℚ)) =
      3192 * Matrix.trace (E57Matrix V * permMatrix σ) +
      (-8) * Matrix.trace (E7Matrix Γ * permMatrix σ) +
      7 * Matrix.trace (EMinus8Matrix Γ * permMatrix σ) := by
  have hchi0 : Matrix.trace (E57Matrix V * permMatrix σ) = 1 :=
    trace_E57Matrix_mul_permMatrix hΓ σ
  have ha0 := thm1_a0_eq_chi_sum hΓ σ hσ
  have ha1 := thm1_a1_eq_chi_combination hΓ σ hσ
  rw [hΓ.card]; push_cast
  linear_combination -ha0 - ha1 - 3250 * hchi0

end Moore57.Papers.MacajSiran2010.S2
