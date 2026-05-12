import Moore57.D19OnMoore57.E7Projection.ProjectionCharacterBridge
import Moore57.D19OnMoore57.Misc.Minus8ProjectionRepresentation
import Moore57.D19OnMoore57.D19Core.RepresentationMathlibCharacterTools

/-!
# Trace boundary bridge for the E7 and minus-8 projection representations

This file converts concrete matrix-trace boundary data into the mathlib-facing
character boundary structures used by the D19 representation pipeline.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19CharacterClassBoundary

/-- Build the E7 character-class boundary from concrete projection trace
values. -/
def ofE7ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ)) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma where
  dimension := dimension
  rotation_value := by
    intro d hd
    rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
    exact rotation_trace d hd
  reflection_zero := by
    rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
    exact reflection_zero_trace

end D19CharacterClassBoundary

namespace D19CharacterValueBoundary

/-- Build the minus-8 character-value boundary from concrete complementary
projection trace values. -/
def ofMinus8ProjectionTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (A B C : ℕ)
    (one_trace :
      Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
        (A : ℚ) + (B : ℚ) + 18 * (C : ℚ))
    (rotation_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ))
    (reflection_zero_trace :
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (A : ℚ) - (B : ℚ)) :
    D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C where
  one_value := by
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    exact one_trace
  rotation_value := by
    intro d hd
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    exact rotation_trace d hd
  reflection_zero := by
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    exact reflection_zero_trace

end D19CharacterValueBoundary

end Moore57
