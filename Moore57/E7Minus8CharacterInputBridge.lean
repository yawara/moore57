import Moore57.E7LinearCharacterInputBridge
import Moore57.Minus8ProjectionRepresentation
import Moore57.D19LinearCharacterMinus8

/-!
# E7 and minus-8 character-boundary bridge

The `E7` and `(-8)` projection representations now exist as mathlib
representations.  This file packages the remaining character-boundary
assumptions into the exact `D19LinearCharacterInput` record consumed downstream.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- A D19 value-boundary for the concrete `(-8)` projection representation is
exactly the complementary trace character used in the older pipeline. -/
theorem minus8_trace_eq_d19Linear_of_characterValueBoundary
    (h : D19ActsOnMoore57 V Γ) (A B C : ℕ)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C) :
    ∀ g : DihedralGroup 19,
      Matrix.trace (permMatrix (h.smulEquiv g)) - 1 -
          Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter A B C g : ℚ) := by
  intro g
  rw [← h.minus8ProjectionRepresentation_character_eq_matrix_trace g]
  exact minus8Values.character_eq_d19Linear g

/-- An E7 class-boundary gives the old concrete `h7` trace character. -/
theorem e7_trace_eq_d19Linear_of_characterClassBoundary
    (h : D19ActsOnMoore57 V Γ) (alpha beta gamma : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma) :
    ∀ g : DihedralGroup 19,
      Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
        (d19LinearCharacter alpha beta gamma g : ℚ) := by
  intro g
  rw [← h.e7ProjectionRepresentation_character_eq_matrix_trace g]
  exact e7Class.character_eq_d19Linear h.finrank_E7Range_eq_1729 g

/-- The reflection equation `α - β = 33` follows from the E7 class-boundary
once the standard reflection counts are known. -/
theorem reflection_eq_of_E7_characterClassBoundary
    (h : D19ActsOnMoore57 V Γ) (alpha beta gamma : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    {d : ZMod 19}
    (ha0 : fixedVertexCount (h.smulEquiv (DihedralGroup.sr d)) = 56)
    (ha1 : adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr d)) = 112) :
    (alpha : ℤ) - (beta : ℤ) = 33 :=
  h.reflection_eq_of_linear_character alpha beta gamma
    (h.e7_trace_eq_d19Linear_of_characterClassBoundary alpha beta gamma e7Class)
    ha0 ha1

/-- The `(-8)` class-boundary supplies the non-negativity bounds on the E7
multiplicities once the standard reflection and rotation fixed counts are
known. -/
theorem alpha_beta_gamma_le_of_E7_minus8_characterBoundaries
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    alpha ≤ 113 ∧ beta ≤ 58 ∧ gamma ≤ 171 :=
  h.alpha_beta_gamma_le_of_eigenspace_characters alpha beta gamma A B C
    (h.e7_trace_eq_d19Linear_of_characterClassBoundary alpha beta gamma e7Class)
    (h.minus8_trace_eq_d19Linear_of_characterValueBoundary A B C minus8Values)
    hreflection_a0 hrotation_a0

namespace D19LinearCharacterInput

/-- Build `D19LinearCharacterInput` from class-boundary data for the concrete
E7 projection representation and value-boundary data for the concrete
`(-8)` projection representation.  The remaining non-character inputs are the
standard reflection and rotation fixed-count facts. -/
noncomputable def ofE7AndMinus8CharacterBoundaries
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma A B C : ℕ)
    (e7Class :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (minus8Values :
      D19CharacterValueBoundary h.minus8ProjectionRepresentation A B C)
    {dt : ZMod 19}
    (hreflection_a0 :
      fixedVertexCount (h.smulEquiv (DihedralGroup.sr dt)) = 56)
    (hreflection_a1 :
      adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr dt)) = 112)
    (hrotation_a0 :
      ∀ d : ZMod 19, d ≠ 0 →
        fixedVertexCount (h.smulEquiv (DihedralGroup.r d)) = 1) :
    D19LinearCharacterInput h := by
  have hreflection :
      (alpha : ℤ) - (beta : ℤ) = 33 :=
    h.reflection_eq_of_E7_characterClassBoundary alpha beta gamma e7Class
      hreflection_a0 hreflection_a1
  have hbounds :=
    h.alpha_beta_gamma_le_of_E7_minus8_characterBoundaries
      alpha beta gamma A B C e7Class minus8Values
      hreflection_a0 hrotation_a0
  exact
    ofE7ProjectionCharacterClassBoundary h alpha beta gamma e7Class
      hreflection hbounds.1 hbounds.2.1

end D19LinearCharacterInput

end D19ActsOnMoore57

end Moore57
