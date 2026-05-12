import Moore57.Moore57Graph.E7Matrix.Idempotent
import Moore57.Moore57Graph.E7Matrix.MatrixLinearMapBridge
import Moore57.Foundations.LinearAlgebra.ProjectionTrace
import Moore57.D19OnMoore57.Action.D19Action

/-!
# Trace bridge for the E7 projection range

This file combines the Moore57 `E7Matrix` idempotence, the matrix-to-linear-map
bridge, and the projection trace lemma.  The result is the concrete character
identity for the action restricted to the range of the `E7` projection.
-/

namespace Moore57

section HigmanTrace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The `E7Matrix` is idempotent after transport through `Matrix.toLin'`. -/
theorem E7Matrix_toLin'_isIdempotentElem (hΓ : IsMoore57 Γ) :
    IsIdempotentElem (E7Matrix Γ).toLin' := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← matrix_toLin'_mul,
    E7Matrix_mul_E7Matrix_eq_E7Matrix hΓ]

/-- Restricting a permutation matrix to the range of the idempotent `E7`
projection has trace equal to the concrete Moore57 Higman trace. -/
theorem trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    LinearMap.trace ℚ (LinearMap.range (E7Matrix Γ).toLin')
        ((permMatrix σ).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix σ).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (E7Matrix_toLin'_isIdempotentElem hΓ)
                (T := (permMatrix σ).toLin')).mp
                (E7Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut)).1) hx)) =
      Matrix.trace (E7Matrix Γ * permMatrix σ) := by
  have hcomm :
      Commute (E7Matrix Γ).toLin' (permMatrix σ).toLin' :=
    E7Matrix_toLin'_commute_permMatrix_toLin' Γ σ haut
  rw [Moore57.LinearMap.trace_restrict_range_eq_trace_comp_of_isIdempotentElem
    (p := (E7Matrix Γ).toLin') (f := (permMatrix σ).toLin')
    (E7Matrix_toLin'_isIdempotentElem hΓ) hcomm]
  rw [show (E7Matrix Γ).toLin' ∘ₗ (permMatrix σ).toLin' =
      (E7Matrix Γ * permMatrix σ).toLin' by
        rw [matrix_toLin'_mul]]
  exact trace_E7Matrix_mul_permMatrix_toLin'_eq_matrix_trace Γ σ

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- D19 specialization of the `E7` projection-range trace bridge. -/
theorem trace_restrict_E7Range_smulEquiv_toLin'_eq_matrix_trace
    (g : DihedralGroup 19) :
    LinearMap.trace ℚ (LinearMap.range (E7Matrix Γ).toLin')
        ((permMatrix (h.smulEquiv g)).toLin'.restrict (by
          intro x hx
          exact ((Module.End.mem_invtSubmodule_iff_mapsTo
            (f := (permMatrix (h.smulEquiv g)).toLin')).mp
              ((LinearMap.IsIdempotentElem.commute_iff
                (E7Matrix_toLin'_isIdempotentElem h.isMoore)
                (T := (permMatrix (h.smulEquiv g)).toLin')).mp
                (E7Matrix_toLin'_commute_permMatrix_toLin' Γ (h.smulEquiv g)
                  (by
                    intro v w
                    exact h.smul_adj g v w))).1) hx)) =
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) :=
  trace_restrict_E7Range_permMatrix_toLin'_eq_matrix_trace h.isMoore
    (h.smulEquiv g) (by
      intro v w
      exact h.smul_adj g v w)

end D19ActsOnMoore57

end HigmanTrace

end Moore57
