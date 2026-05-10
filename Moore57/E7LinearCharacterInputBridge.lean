import Moore57.E7ProjectionDimension
import Moore57.D19RepresentationMathlibCharacterTools

/-!
# E7 projection representation to D19 linear-character input

This file connects the concrete `E7` projection representation to the existing
mathlib-facing D19 character constructors.  After this bridge, the remaining
E7 representation-theoretic obligation is exactly the D19 class-character
boundary for `h.e7ProjectionRepresentation`.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19LinearCharacterInput

/-- Build the full `D19LinearCharacterInput` from class-boundary data for the
concrete `E7` projection representation. -/
noncomputable def ofE7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    D19LinearCharacterInput h :=
  ofRepresentationCharacterClassBoundary (h := h)
    h.e7ProjectionRepresentation alpha beta gamma
    h.finrank_E7Range_eq_1729
    (fun g => (h.e7ProjectionRepresentation_character_eq_matrix_trace g).symm)
    characterClass reflection minus8_trivial_nonneg minus8_sign_nonneg

end D19LinearCharacterInput

/-- Component-boundary version of
`D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary`. -/
theorem representationCharacterComponentsBoundary_of_E7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofE7ProjectionCharacterClassBoundary h
      alpha beta gamma characterClass reflection
      minus8_trivial_nonneg minus8_sign_nonneg)
    |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

end Moore57
