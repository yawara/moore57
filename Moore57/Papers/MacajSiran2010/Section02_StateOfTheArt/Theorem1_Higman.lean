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

end Moore57.Papers.MacajSiran2010.S2
