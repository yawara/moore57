import Moore57.D19OnMoore57.Final.D19FinalLinearUniqueReflection
import Moore57.D19OnMoore57.Rotation.RotationFixedCountUnique

/-!
# Final D19 inputs from an exact fixed count and reflection copy

This file packages the final constructive input boundary when the rotation-one
fixed side is supplied as the exact count `1`, and the adjacent-moved side is
supplied by a reflection-copy witness.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final linear-character inputs using the exact fixed count
`fixedVertexCount (h.rotation 1) = 1` and a reflection-copy adjacent-moved
partition. -/
structure D19FinalLinearCountReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has exactly one fixed vertex. -/
  rotationOne_fixed_count : fixedVertexCount (h.rotation 1) = 1
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCountReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert exact fixed count `1` to the unique-fixed reflection boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19FinalLinearUniqueReflectionInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed :=
    h.existsUnique_rotation_one_fixed_of_fixedVertexCount_eq_one
      data.rotationOne_fixed_count
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget to the existing linear-character and unique-fixed constructive
boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs
    |>.toD19ConstructiveFinalLinearUniqueInputs

/-- Forget to the constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19ConstructiveFinalInputs

/-- Forget to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCountReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearUniqueReflectionInputs.toD19FinalInputs

/-- Final linear-character, exact-count, reflection-copy inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCountReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearUniqueReflectionInputs.not_nonempty h
    ⟨data.toD19FinalLinearUniqueReflectionInputs⟩

end D19FinalLinearCountReflectionInputs

/-- Variant of the final linear-character reflection-copy inputs where the
fixed side is supplied as cardinality one of the fixed subtype. -/
structure D19FinalLinearCardReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- The fixed subtype for rotation by `1` has cardinality one. -/
  rotationOne_fixed_card : Fintype.card (fixedVertexSet (h.rotation 1)) = 1
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearCardReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert fixed-subtype cardinality `1` to the exact-count reflection
boundary. -/
noncomputable def toD19FinalLinearCountReflectionInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19FinalLinearCountReflectionInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_fixed_count := by
    simpa [fixedVertexCount_eq_card_fixedVertexSet] using
      data.rotationOne_fixed_card
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Convert fixed-subtype cardinality `1` to the unique-fixed reflection
boundary. -/
noncomputable def toD19FinalLinearUniqueReflectionInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19FinalLinearUniqueReflectionInputs h :=
  data.toD19FinalLinearCountReflectionInputs.toD19FinalLinearUniqueReflectionInputs

/-- Forget to the existing linear-character and unique-fixed constructive
boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h :=
  data.toD19FinalLinearCountReflectionInputs
    |>.toD19ConstructiveFinalLinearUniqueInputs

/-- Forget to the constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19FinalLinearCountReflectionInputs.toD19ConstructiveFinalInputs

/-- Forget to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearCardReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19FinalLinearCountReflectionInputs.toD19FinalInputs

/-- Final linear-character, fixed-cardinality, reflection-copy inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearCardReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19FinalLinearCountReflectionInputs.not_nonempty h
    ⟨data.toD19FinalLinearCountReflectionInputs⟩

end D19FinalLinearCardReflectionInputs

end Moore57
