import Moore57.D19OnMoore57.Final.D19FinalLinearCountReflectionBase

/-!
# Final D19 base-selection inputs from fixed-set cardinality

This file supplies a `Fintype.card` variant of
`D19FinalLinearCountReflectionBaseInputs`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, cardinality
one of the rotation-one fixed subtype, downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCardReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- The fixed subtype for rotation by `1` has cardinality one. -/
  rotationOne_fixed_card : Fintype.card (fixedVertexSet (h.rotation 1)) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCardReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert fixed-subtype cardinality `1` to the exact fixed-count base
boundary. -/
noncomputable def toD19FinalLinearCountReflectionBaseInputs
    (data : D19FinalLinearCardReflectionBaseInputs h) :
    D19FinalLinearCountReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      data.rotationOne_fixed_card
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the cardinality presentation down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCardReflectionBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearCountReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, fixed-cardinality, reflection-copy base inputs
cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCardReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearCountReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearCountReflectionBaseInputs⟩

end D19FinalLinearCardReflectionBaseInputs

end Moore57
