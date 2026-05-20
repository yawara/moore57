import Moore57.Moore57Graph.E7Matrix.SpectralDecomposition
import Moore57.Moore57Graph.Moore57Definition
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Moore57 spectral characters `χ₀`, `χ₁`, `χ₂`

This file packages the three spectral-projection traces

```
χ₀(σ) := tr(E_57   · permMatrix σ)        -- 57-eigenspace projection
χ₁(σ) := tr(E_7    · permMatrix σ)        --  7-eigenspace projection
χ₂(σ) := tr(E_{-8} · permMatrix σ)        -- −8-eigenspace projection
```

as named functions `Equiv.Perm V → ℚ` and proves the basic
character-style identities:

* `chi0 σ = 1` for any `σ : Equiv.Perm V` on a Moore57 graph
  (`chi0_eq_one`).
* Sum `χ₀ + χ₁ + χ₂ = a₀ = fixedVertexCount` (`chi_sum_eq_fixedVertexCount`).
* Conjugation invariance `χⱼ(τστ⁻¹) = χⱼ(σ)` when `τ ∈ Aut(Γ)`
  (`chi0_conj`, `chi1_conj`, `chi2_conj`).

These are the Mačaj–Širáň §4 "character system" components, used to express
the path-count functions `a₀, a₁, a₂` as ℤ-linear combinations of the
spectral characters (see
`Moore57.Papers.MacajSiran2010.S2.thm1_a{0,1,2}_eq_chi_combination`).

Tier B note: the link to `Representation.character` of the corresponding
subrepresentations of `permutationRepresentation` (i.e., the spectral
restriction to `range E_λ`) is left for a future commit; see the existing
`TraceIntegrality.lean` for the partial pattern.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Definitions -/

/-- `χ₀(σ) := tr(E_57 · P_σ)` — spectral projection onto the 57-eigenspace. -/
noncomputable def chi0 (σ : Equiv.Perm V) : ℚ :=
  Matrix.trace (E57Matrix V * permMatrix σ)

/-- `χ₁(σ) := tr(E_7 · P_σ)` — spectral projection onto the 7-eigenspace. -/
noncomputable def chi1 (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : ℚ :=
  Matrix.trace (E7Matrix Γ * permMatrix σ)

/-- `χ₂(σ) := tr(E_{-8} · P_σ)` — spectral projection onto the −8-eigenspace. -/
noncomputable def chi2 (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : ℚ :=
  Matrix.trace (EMinus8Matrix Γ * permMatrix σ)

/-! ### Basic identities -/

/-- `χ₀(σ) = 1` for any permutation on a Moore57 graph.

This is a *uniform* identity: it does not require `σ` to be a graph
automorphism.  See `trace_E57Matrix_mul_permMatrix`. -/
theorem chi0_eq_one (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    chi0 (V := V) σ = 1 :=
  trace_E57Matrix_mul_permMatrix hΓ σ

/-- Character-sum identity: `χ₀(σ) + χ₁(σ) + χ₂(σ) = a₀(σ)`. -/
theorem chi_sum_eq_fixedVertexCount (σ : Equiv.Perm V) :
    chi0 (V := V) σ + chi1 Γ σ + chi2 Γ σ = (fixedVertexCount σ : ℚ) := by
  show Matrix.trace (E57Matrix V * permMatrix σ) +
        Matrix.trace (E7Matrix Γ * permMatrix σ) +
        Matrix.trace (EMinus8Matrix Γ * permMatrix σ) = (fixedVertexCount σ : ℚ)
  have hdecomp := trace_decomp_via_spectral (Γ := Γ) σ 1
  simp only [pow_one] at hdecomp
  have htraceP : Matrix.trace (permMatrix σ) = (fixedVertexCount σ : ℚ) :=
    trace_permMatrix_eq_fixedVertexCount σ
  linarith [hdecomp, htraceP]

/-! ### Conjugation invariance

For a graph automorphism `τ : Equiv.Perm V` of `Γ`, the spectral projection
matrices commute with `permMatrix τ`.  Combining this commutation with the
cyclic property of the trace shows that each spectral character
`χⱼ` is constant on conjugacy classes within `Aut(Γ)`.
-/

/-- The Moore57 project's `permMatrix` is a true homomorphism (because it uses
the inverse convention `σ.symm.toPEquiv.toMatrix`).  Helper for
`trace_E_mul_permMatrix_conj`. -/
private lemma permMatrix_hom_mul (σ τ : Equiv.Perm V) :
    (permMatrix (σ * τ) : Matrix V V ℚ) = permMatrix σ * permMatrix τ := by
  change Equiv.Perm.permMatrix ℚ ((σ * τ)⁻¹) =
      Equiv.Perm.permMatrix ℚ σ⁻¹ * Equiv.Perm.permMatrix ℚ τ⁻¹
  rw [mul_inv_rev, Matrix.permMatrix_mul]

private lemma permMatrix_hom_one :
    (permMatrix (1 : Equiv.Perm V) : Matrix V V ℚ) = 1 := by
  change Equiv.Perm.permMatrix ℚ ((1 : Equiv.Perm V)⁻¹) = 1
  simp

private lemma trace_E_mul_permMatrix_conj
    (E : Matrix V V ℚ) (σ τ : Equiv.Perm V)
    (hcomm : E * permMatrix τ = permMatrix τ * E) :
    Matrix.trace (E * permMatrix (τ * σ * τ⁻¹)) =
      Matrix.trace (E * permMatrix σ) := by
  classical
  have hστ : (permMatrix (τ * σ * τ⁻¹) : Matrix V V ℚ) =
      permMatrix τ * permMatrix σ * permMatrix τ⁻¹ := by
    rw [permMatrix_hom_mul, permMatrix_hom_mul]
  have hτinv : (permMatrix τ⁻¹ : Matrix V V ℚ) * permMatrix τ = 1 := by
    rw [← permMatrix_hom_mul, inv_mul_cancel, permMatrix_hom_one]
  rw [hστ]
  -- Goal: tr (E * (Mτ * Mσ * Mτ⁻¹)) = tr (E * Mσ)
  -- Step 1: left-associate to get (((E * Mτ) * Mσ) * Mτ⁻¹)
  simp only [← mul_assoc]
  -- Step 2: apply hcomm to swap E with Mτ on the leftmost product
  rw [hcomm]
  -- Step 3: trace cyclic property — move Mτ⁻¹ from end to start
  rw [Matrix.trace_mul_comm]
  -- Step 4: left-associate again and reduce Mτ⁻¹ * Mτ = 1
  simp only [← mul_assoc, hτinv, Matrix.one_mul]

/-- `χ₀` is invariant under conjugation by any permutation.
(`E_57` commutes with every permutation matrix, so this needs no
automorphism hypothesis.) -/
theorem chi0_conj (σ τ : Equiv.Perm V) :
    chi0 (V := V) (τ * σ * τ⁻¹) = chi0 (V := V) σ := by
  unfold chi0
  exact trace_E_mul_permMatrix_conj (E := E57Matrix V) σ τ
    (E57Matrix_mul_permMatrix_eq_permMatrix_mul_E57Matrix τ)

/-- `χ₁` is invariant under conjugation by graph automorphisms. -/
theorem chi1_conj (σ τ : Equiv.Perm V)
    (hτ : ∀ v w, Γ.Adj v w ↔ Γ.Adj (τ v) (τ w)) :
    chi1 Γ (τ * σ * τ⁻¹) = chi1 Γ σ := by
  unfold chi1
  exact trace_E_mul_permMatrix_conj (E := E7Matrix Γ) σ τ
    (E7Matrix_mul_permMatrix_eq_permMatrix_mul_E7Matrix Γ τ hτ)

/-- `χ₂` is invariant under conjugation by graph automorphisms. -/
theorem chi2_conj (σ τ : Equiv.Perm V)
    (hτ : ∀ v w, Γ.Adj v w ↔ Γ.Adj (τ v) (τ w)) :
    chi2 Γ (τ * σ * τ⁻¹) = chi2 Γ σ := by
  unfold chi2
  exact trace_E_mul_permMatrix_conj (E := EMinus8Matrix Γ) σ τ
    (EMinus8Matrix_mul_permMatrix_eq_permMatrix_mul_EMinus8Matrix τ hτ)

/-! ### Bridge to the path-count interpretation -/

/-- `χ₁(σ)` formula in `a₀, a₁` for Moore57: paper §2 Thm 1 row 1. -/
theorem chi1_formula (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    chi1 Γ σ = (8 * (fixedVertexCount σ : ℚ) + (adjacentMovedCount Γ σ : ℚ) - 65) / 15 :=
  hΓ.higman_trace_formula σ

/-- `a₁(σ) = 57·χ₀(σ) + 7·χ₁(σ) − 8·χ₂(σ)` (paper §2 Thm 1 inverse, a₁ row). -/
theorem adjacentMovedCount_eq_chi_combination
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) :
    (adjacentMovedCount Γ σ : ℚ) =
      57 * chi0 (V := V) σ + 7 * chi1 Γ σ + (-8) * chi2 Γ σ := by
  have hA : Γ.adjMatrix ℚ =
      (57 : ℚ) • E57Matrix V + (7 : ℚ) • E7Matrix Γ - (8 : ℚ) • EMinus8Matrix Γ :=
    adjMatrix_eq_spectral_decomp hΓ
  have htrAP : Matrix.trace (Γ.adjMatrix ℚ * permMatrix σ) =
      (adjacentMovedCount Γ σ : ℚ) :=
    trace_adjMatrix_mul_permMatrix_eq_adjacentMovedCount Γ σ
  unfold chi0 chi1 chi2
  rw [← htrAP, hA]
  simp [Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  ring

end Moore57
