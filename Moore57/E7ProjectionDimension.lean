import Moore57.E7ProjectionCharacterBridge
import Moore57.D19LinearCharacterDimension

/-!
# Dimension of the E7 projection representation

The concrete E7 range representation has dimension `1729`; this follows from
mathlib's `Representation.char_one` and the already-proved Higman trace at the
identity.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The range of the `E7Matrix` projection has dimension `1729`. -/
theorem finrank_E7Range_eq_1729 (h : D19ActsOnMoore57 V Γ) :
    Module.finrank ℚ (LinearMap.range (E7Matrix Γ).toLin') = 1729 := by
  have hchar := h.e7ProjectionRepresentation_character_eq_matrix_trace (1 : DihedralGroup 19)
  rw [Representation.char_one, h.smulEquiv_one, h.isMoore.trace_E7Matrix_one] at hchar
  exact_mod_cast hchar

/-- The concrete E7 projection representation has dimension `1729`. -/
theorem finrank_e7ProjectionRepresentation_eq_1729 (h : D19ActsOnMoore57 V Γ) :
    Module.finrank ℚ (LinearMap.range (E7Matrix Γ).toLin') = 1729 :=
  h.finrank_E7Range_eq_1729

end D19ActsOnMoore57

end Moore57
