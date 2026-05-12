import Moore57.D19OnMoore57.E7Projection.E7Minus8CharacterInputBridge

/-!
# Consequences of the E7 projection character bridges

This file keeps the representation-side reduction in theorem-wrapper form:
once the remaining obligations are stated as mathlib character boundaries for
the concrete `E7` and `(-8)` projection representations, the downstream
`D19LinearCharacterInput` exists.
-/

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19LinearCharacterInput

/-- E7 projection class-character data, plus the three arithmetic side
conditions already expected downstream, produces a linear-character input. -/
theorem nonempty_ofE7ProjectionCharacterClassBoundary
    (h : D19ActsOnMoore57 V Γ)
    (alpha beta gamma : ℕ)
    (characterClass :
      D19CharacterClassBoundary h.e7ProjectionRepresentation alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    Nonempty (D19LinearCharacterInput h) :=
  ⟨ofE7ProjectionCharacterClassBoundary h
    alpha beta gamma characterClass reflection
    minus8_trivial_nonneg minus8_sign_nonneg⟩

/-- Character-boundary data for the concrete `E7` and `(-8)` projection
representations produces a linear-character input once the standard fixed-count
facts are supplied. -/
theorem nonempty_ofE7AndMinus8CharacterBoundaries
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
    Nonempty (D19LinearCharacterInput h) :=
  ⟨ofE7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C e7Class minus8Values
    hreflection_a0 hreflection_a1 hrotation_a0⟩

end D19LinearCharacterInput

/-- Component-boundary consequence of the concrete `E7` and `(-8)` projection
character boundaries. -/
theorem representationCharacterComponentsBoundary_of_E7AndMinus8CharacterBoundaries
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
    RepresentationCharacterComponentsBoundary h :=
  (D19LinearCharacterInput.ofE7AndMinus8CharacterBoundaries h
    alpha beta gamma A B C e7Class minus8Values
    hreflection_a0 hreflection_a1 hrotation_a0)
    |>.representationCharacterComponentsBoundary

end D19ActsOnMoore57

end Moore57
