import Moore57.D19OnMoore57.LinearCharacter.D19LinearCharacterInput
import Moore57.D19OnMoore57.D19Core.D19ConstructiveFinalUnique

/-!
# Constructive final D19 inputs from a linear character and unique fixed point

This file packages the final constructive input boundary when the character
input is supplied as a full D19 linear-character equality and the fixed-count
input is supplied by a unique fixed point of rotation by `1`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final inputs using a full linear-character witness and a
unique fixed point for rotation by `1`.

The full linear-character witness is forgotten to the representation-character
input consumed by `D19ConstructiveFinalUniqueInputs`. -/
structure D19ConstructiveFinalLinearUniqueInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character equality for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Rotation by `1` has a unique fixed vertex. -/
  rotationOne_unique_fixed : ∃! v : V, h.rotation 1 v = v
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalLinearUniqueInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the full linear-character witness to the unique-fixed final
constructive boundary. -/
noncomputable def toD19ConstructiveFinalUniqueInputs
    (data : D19ConstructiveFinalLinearUniqueInputs h) :
    D19ConstructiveFinalUniqueInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  rotationOne_unique_fixed := data.rotationOne_unique_fixed
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the linear-character and unique-fixed witnesses down to the
constructive final input boundary. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19ConstructiveFinalLinearUniqueInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalUniqueInputs.toD19ConstructiveFinalInputs

/-- Forget the linear-character and unique-fixed witnesses down to the final
input boundary. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalLinearUniqueInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalUniqueInputs.toD19FinalInputs

/-- Constructive final linear-character plus unique-fixed inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalLinearUniqueInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalUniqueInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalUniqueInputs⟩

end D19ConstructiveFinalLinearUniqueInputs

end Moore57
