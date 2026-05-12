import Moore57.D19OnMoore57.Final.LinearUniqueReflectionBase
import Moore57.D19OnMoore57.Rotation.FixedCountUnique

/-!
# Final D19 base-selection inputs from exact fixed count

This file replaces the unique fixed-point field in
`D19FinalLinearUniqueReflectionBaseInputs` by the exact fixed count
`fixedVertexCount (h.rotation 1) = 1`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a full linear-character witness, exact
rotation-one fixed count, downstream base-selection input, and a
reflection-copy adjacent-moved partition. -/
structure D19FinalLinearCountReflectionBaseInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Pairwise-disjoint selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionInput h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCountReflectionBaseInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Exact fixed count `1` supplies the unique-fixed base-input boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionBaseInputs
    (data : D19FinalLinearCountReflectionBaseInputs h) :
    D19FinalLinearUniqueReflectionBaseInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed :=
    h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
      data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the exact-count presentation down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountReflectionBaseInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionBaseInputs.toD19FinalInputs

/-- Final linear-character, exact-count, reflection-copy base inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountReflectionBaseInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionBaseInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionBaseInputs⟩

end D19FinalLinearCountReflectionBaseInputs

end Moore57
