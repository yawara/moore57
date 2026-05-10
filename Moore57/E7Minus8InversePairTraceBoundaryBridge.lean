import Moore57.GroupTheory.Dihedral19CharacterValueReduction
import Moore57.E7Minus8TraceBoundaryBridge

/-!
# Inverse-pair trace boundary bridge for E7 and minus-8

This file packages concrete projection trace data where nontrivial rotation
obligations have been reduced to one representative from each inverse pair.
The trace data is first converted to mathlib character data for the concrete
projection representations, then expanded by D19 character conjugacy.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Trace-level E7 boundary data with rotations reduced to inverse pairs. -/
structure E7ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ) (alpha beta gamma : ℕ) where
  dimension : alpha + beta + 18 * gamma = 1729
  rotation_pair_trace :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) ∨
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
          (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ)
  reflection_zero_trace :
    Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
      (alpha : ℚ) - (beta : ℚ)

/-- Trace-level minus-8 boundary data with rotations reduced to inverse pairs. -/
structure Minus8ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ) (A B C : ℕ) where
  one_trace :
    Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
        Matrix.trace (E7Matrix Γ *
          permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
      (A : ℚ) + (B : ℚ) + 18 * (C : ℚ)
  rotation_pair_trace :
    ∀ d : ZMod 19, d ≠ 0 →
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.r d))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ) ∨
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
          (A : ℚ) + (B : ℚ) - (C : ℚ)
  reflection_zero_trace :
    Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
        Matrix.trace (E7Matrix Γ *
          permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
      (A : ℚ) - (B : ℚ)

namespace E7ProjectionInversePairTraceBoundary

/-- Convert inverse-pair E7 trace data to inverse-pair character data. -/
def toCharacterClassInversePairBoundary
    {h : D19ActsOnMoore57 V Γ} {alpha beta gamma : ℕ}
    (boundary : E7ProjectionInversePairTraceBoundary h alpha beta gamma) :
    D19CharacterClassInversePairBoundary
      h.e7ProjectionRepresentation alpha beta gamma where
  dimension := boundary.dimension
  rotation_pair := {
    pair_value := by
      intro d hd
      rcases boundary.rotation_pair_trace d hd with htrace | htrace
      · left
        rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
      · right
        rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
  }
  reflection_zero := by
    rw [h.e7ProjectionRepresentation_character_eq_matrix_trace]
    exact boundary.reflection_zero_trace

/-- Expand inverse-pair E7 trace data to the existing class-boundary API. -/
def toCharacterClassBoundary
    {h : D19ActsOnMoore57 V Γ} {alpha beta gamma : ℕ}
    (boundary : E7ProjectionInversePairTraceBoundary h alpha beta gamma) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma :=
  boundary.toCharacterClassInversePairBoundary.toClassBoundary

end E7ProjectionInversePairTraceBoundary

namespace Minus8ProjectionInversePairTraceBoundary

/-- Convert inverse-pair minus-8 trace data to inverse-pair character data. -/
def toCharacterValueInversePairBoundary
    {h : D19ActsOnMoore57 V Γ} {A B C : ℕ}
    (boundary : Minus8ProjectionInversePairTraceBoundary h A B C) :
    D19CharacterValueInversePairBoundary
      h.minus8ProjectionRepresentation A B C where
  one_value := by
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    exact boundary.one_trace
  rotation_pair := {
    pair_value := by
      intro d hd
      rcases boundary.rotation_pair_trace d hd with htrace | htrace
      · left
        rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
      · right
        rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
        exact htrace
  }
  reflection_zero := by
    rw [h.minus8ProjectionRepresentation_character_eq_matrix_trace]
    exact boundary.reflection_zero_trace

/-- Expand inverse-pair minus-8 trace data to the existing value-boundary API. -/
def toCharacterValueBoundary
    {h : D19ActsOnMoore57 V Γ} {A B C : ℕ}
    (boundary : Minus8ProjectionInversePairTraceBoundary h A B C) :
    D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C :=
  boundary.toCharacterValueInversePairBoundary.toValueBoundary

end Minus8ProjectionInversePairTraceBoundary

namespace D19CharacterClassBoundary

/-- Build the E7 class boundary from explicit inverse-pair projection traces. -/
def ofE7ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (dimension : alpha + beta + 18 * gamma = 1729)
    (rotation_pair_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.r d))) =
            (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ) ∨
          Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
            (alpha : ℚ) + (beta : ℚ) - (gamma : ℚ))
    (reflection_zero_trace :
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (alpha : ℚ) - (beta : ℚ)) :
    D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma :=
  (E7ProjectionInversePairTraceBoundary.toCharacterClassBoundary
    ({ dimension := dimension
       rotation_pair_trace := rotation_pair_trace
       reflection_zero_trace := reflection_zero_trace } :
      E7ProjectionInversePairTraceBoundary h alpha beta gamma))

end D19CharacterClassBoundary

namespace D19CharacterValueBoundary

/-- Build the minus-8 value boundary from explicit inverse-pair projection traces. -/
def ofMinus8ProjectionInversePairTraceBoundary
    (h : D19ActsOnMoore57 V Γ)
    (A B C : ℕ)
    (one_trace :
      Matrix.trace (permMatrix (h.smulEquiv (1 : DihedralGroup 19))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (1 : DihedralGroup 19))) =
        (A : ℚ) + (B : ℚ) + 18 * (C : ℚ))
    (rotation_pair_trace :
      ∀ d : ZMod 19, d ≠ 0 →
        Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r d))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r d))) =
            (A : ℚ) + (B : ℚ) - (C : ℚ) ∨
          Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) - 1 -
            Matrix.trace (E7Matrix Γ *
              permMatrix (h.smulEquiv (DihedralGroup.r (-d)))) =
            (A : ℚ) + (B : ℚ) - (C : ℚ))
    (reflection_zero_trace :
      Matrix.trace (permMatrix (h.smulEquiv (DihedralGroup.sr 0))) - 1 -
          Matrix.trace (E7Matrix Γ *
            permMatrix (h.smulEquiv (DihedralGroup.sr 0))) =
        (A : ℚ) - (B : ℚ)) :
    D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C :=
  (Minus8ProjectionInversePairTraceBoundary.toCharacterValueBoundary
    ({ one_trace := one_trace
       rotation_pair_trace := rotation_pair_trace
       reflection_zero_trace := reflection_zero_trace } :
      Minus8ProjectionInversePairTraceBoundary h A B C))

end D19CharacterValueBoundary

end Moore57
