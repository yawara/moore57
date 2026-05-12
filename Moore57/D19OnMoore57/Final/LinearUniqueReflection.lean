import Moore57.D19OnMoore57.D19Core.ConstructiveFinalLinearUnique
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCopyCriteria

/-!
# Final D19 inputs from a linear character, unique fixed point, and reflection copy

This file packages the final constructive input boundary in the common case
where the two-copy adjacent-moved partition is supplied by a reflection-copy
witness.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final constructive inputs using a full linear-character witness, a unique
fixed point for rotation by `1`, and a reflection-copy adjacent-moved
partition. -/
structure D19FinalLinearUniqueReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearUniqueReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the reflection-copy presentation to the existing linear-character
and unique-fixed constructive boundary. -/
noncomputable def toD19ConstructiveFinalLinearUniqueInputs
    (data : D19FinalLinearUniqueReflectionInputs h) :
    D19ConstructiveFinalLinearUniqueInputs h where
  linearCharacter := data.linearCharacter
  rotationOne_unique_fixed := data.rotationOne_unique_fixed
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toTwoCopyPartition38Witness

/-- Forget the reflection-copy, linear-character, and unique-fixed witnesses
down to the constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearUniqueReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalLinearUniqueInputs.toD19ConstructiveFinalInputs

/-- Forget the reflection-copy, linear-character, and unique-fixed witnesses
down to the final input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearUniqueReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalLinearUniqueInputs.toD19FinalInputs

/-- Final linear-character, unique-fixed, reflection-copy inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearUniqueReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalLinearUniqueInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalLinearUniqueInputs⟩

end D19FinalLinearUniqueReflectionInputs

end Moore57
