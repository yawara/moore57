import Moore57.D19OnMoore57.E7Projection.ProjectionCharacterBridge
import Moore57.Foundations.LinearAlgebra.InvolutionTrace

/-!
# Reflection trace integrality

This file connects the mathlib linear-algebra involution trace lemma to the
concrete E7 projection trace used by the D19 reflection pipeline.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- If a D19 element squares to the identity, then the E7 projection character
at that element is an integer. -/
theorem exists_int_e7ProjectionRepresentation_character_of_sq_eq_one
    (h : D19ActsOnMoore57 V Γ) {g : DihedralGroup 19}
    (hg : g * g = 1) :
    ∃ z : ℤ, h.e7ProjectionRepresentation.character g = (z : ℚ) := by
  have hsq :
      h.e7ProjectionRepresentation g * h.e7ProjectionRepresentation g = 1 := by
    rw [← map_mul, hg, map_one]
  simpa [Representation.character] using
    Moore57.LinearMap.exists_int_trace_of_involutive
      (h.e7ProjectionRepresentation g) hsq

/-- The concrete E7 matrix trace of a D19 reflection is an integer. -/
theorem exists_int_E7Matrix_mul_permMatrix_reflection_trace
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    ∃ z : ℤ,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr k))) =
        (z : ℚ) := by
  obtain ⟨z, hz⟩ :=
    h.exists_int_e7ProjectionRepresentation_character_of_sq_eq_one
      (g := DihedralGroup.sr k) (by rw [DihedralGroup.sr_mul_self])
  refine ⟨z, ?_⟩
  rw [← h.e7ProjectionRepresentation_character_eq_matrix_trace]
  exact hz

end D19ActsOnMoore57

end Moore57
