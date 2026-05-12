import Moore57.Moore57Graph.E7Matrix.PermutationCommutation
import Moore57.D19OnMoore57.E7Projection.ProjectionTraceBridge
import Moore57.D19OnMoore57.E7Projection.ProjectionRepresentationSkeleton
import Moore57.Foundations.LinearAlgebra.InvolutionTrace

/-!
# E7-projection trace integrality for an involutive Moore57 automorphism (Tier 2)

For an involutive automorphism `σ : Equiv.Perm V` of a Moore57 graph,
`Matrix.trace (E7Matrix Γ * permMatrix σ)` is an integer. The proof uses

* `E7Matrix Γ` is idempotent (`E7Matrix_toLin'_isIdempotentElem`);
* `permMatrix σ` commutes with `E7Matrix Γ` (since σ is an automorphism);
* the restriction of `(permMatrix σ).toLin'` to the range of `E7Matrix.toLin'`
  is well-defined and squares to the identity when σ² = 1;
* `Moore57.LinearMap.exists_int_trace_of_involutive` gives the trace as an integer;
* `trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace` bridges the
  linear-map trace and the matrix trace.

This abstract version is used by both the existing D₁₉ reflection pipeline
and the upcoming C₃₈ argument.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- For any involutive automorphism `σ` of a Moore57 graph,
`Matrix.trace (E7Matrix Γ * permMatrix σ)` is an integer. -/
theorem aut_involution_E7_trace_int
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ) :
    ∃ z : ℤ, Matrix.trace (E7Matrix Γ * permMatrix σ) = (z : ℚ) := by
  classical
  -- The range of the E7 projection (an `ℚ`-submodule of `V → ℚ`).
  let W := LinearMap.range (E7Matrix Γ).toLin'
  -- The commutation `E7Matrix.toLin' ∘ (permMatrix σ).toLin' =
  -- (permMatrix σ).toLin' ∘ E7Matrix.toLin'`.
  have hcomm :
      Commute (E7Matrix Γ).toLin' (permMatrix σ).toLin' :=
    E7Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut
  -- The range is invariant under `(permMatrix σ).toLin'`.
  have hmaps :
      ∀ x ∈ W, (permMatrix σ).toLin' x ∈ W := by
    intro x hx
    exact ((Module.End.mem_invtSubmodule_iff_mapsTo
      (f := (permMatrix σ).toLin')).mp
        ((LinearMap.IsIdempotentElem.commute_iff
          (E7Matrix_toLin'_isIdempotentElem hΓ)
          (T := (permMatrix σ).toLin')).mp hcomm).1) hx
  -- Restrict `(permMatrix σ).toLin'` to `W`.
  let f : W →ₗ[ℚ] W := (permMatrix σ).toLin'.restrict hmaps
  -- Show `f * f = 1` using σ involutive.
  have hσ_sq : σ * σ = 1 := by
    ext v
    simpa using hinv v
  have hperm_sq : permMatrix σ * permMatrix σ = (1 : Matrix V V ℚ) := by
    rw [← moore57_permMatrix_mul, hσ_sq, moore57_permMatrix_one]
  have hlin_sq :
      (permMatrix σ).toLin' * (permMatrix σ).toLin' = 1 := by
    rw [Module.End.mul_eq_comp, ← matrix_toLin'_mul, hperm_sq, Matrix.toLin'_one]
    rfl
  have hsq : f * f = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hf2 :
        ((f * f) x : V → ℚ) = (permMatrix σ).toLin' ((permMatrix σ).toLin' x.1) := rfl
    have hone : ((1 : (W →ₗ[ℚ] W)) x : V → ℚ) = x.1 := rfl
    rw [hf2, hone]
    have := congr_arg (fun g => g x.1) hlin_sq
    simpa using this
  -- Apply the abstract integer-trace lemma for involutive endomorphisms.
  obtain ⟨z, hz⟩ := Moore57.LinearMap.exists_int_trace_of_involutive f hsq
  refine ⟨z, ?_⟩
  rw [← hz]
  exact (trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace hΓ σ haut).symm

end Moore57
