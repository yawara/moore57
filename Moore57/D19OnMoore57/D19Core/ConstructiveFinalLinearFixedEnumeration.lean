import Moore57.D19OnMoore57.LinearCharacter.Input
import Moore57.D19OnMoore57.D19Core.ConstructiveFinalFixedEnumeration

/-!
# Constructive final D19 inputs with linear character and fixed enumeration

This file combines the full linear-character input with the fixed-point
enumeration boundary.  The linear-character witness is reduced to the
representation-character input consumed by
`D19ConstructiveFinalFixedEnumerationInputs`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final input record whose character input is supplied as a
full D19 linear-character equality and whose fixed-count bound is supplied by
an explicit enumeration of the rotation-one fixed vertices. -/
structure D19ConstructiveFinalLinearFixedEnumerationInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalLinearFixedEnumerationInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the full linear-character input and fixed-point enumeration into
the split final character input. -/
def toD19FinalCharacterInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19FinalCharacterInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedUpperBound := data.fixedEnumeration.toRotationFixedUpperBoundInput

/-- Forget the linear-character boundary down to the fixed-enumeration final
input record. -/
def toD19ConstructiveFinalFixedEnumerationInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19ConstructiveFinalFixedEnumerationInputs h where
  representation := data.linearCharacter.toD19RepresentationCharacterInput
  fixedEnumeration := data.fixedEnumeration
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the linear-character and fixed-enumeration boundaries down to the
constructive final input record. -/
def toD19ConstructiveFinalInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalFixedEnumerationInputs.toD19ConstructiveFinalInputs

/-- Forget the constructive boundaries all the way to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalLinearFixedEnumerationInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalFixedEnumerationInputs.toD19FinalInputs

/-- Constructive final inputs with linear character and fixed-point
enumeration cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalLinearFixedEnumerationInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalFixedEnumerationInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalFixedEnumerationInputs⟩

end D19ConstructiveFinalLinearFixedEnumerationInputs

end Moore57
