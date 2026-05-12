import Moore57.D19OnMoore57.D19Core.ConstructiveFinalLinearFixedEnumeration
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCopyCriteria

/-!
# Final D19 inputs from linear character, fixed enumeration, and reflection copies

This file packages the final contradiction input where the character side is a
full linear-character equality, the fixed-vertex bound is supplied by an
explicit rotation-one fixed enumeration, and the adjacent-moved partition is
given by the reflection-copy criterion.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using the linear-character criterion, an explicit
fixed-point enumeration, an orbit-base enumeration, and a reflection-copy
adjacent-moved partition. -/
structure D19FinalLinearFixedEnumerationReflectionInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Full D19 linear-character witness for the trace representation. -/
  linearCharacter : D19ActsOnMoore57.D19LinearCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Reflection-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedReflectionCopyPartition38Witness h orbitBase.base

namespace D19FinalLinearFixedEnumerationReflectionInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the reflection-copy adjacent-moved boundary to the two-copy final
input with linear character and fixed-point enumeration. -/
noncomputable def toD19ConstructiveFinalLinearFixedEnumerationInputs
    (data : D19FinalLinearFixedEnumerationReflectionInputs h) :
    D19ConstructiveFinalLinearFixedEnumerationInputs h where
  linearCharacter := data.linearCharacter
  fixedEnumeration := data.fixedEnumeration
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toTwoCopyPartition38Witness

/-- Forget the specialized boundaries down to constructive final inputs. -/
noncomputable def toD19ConstructiveFinalInputs
    (data : D19FinalLinearFixedEnumerationReflectionInputs h) :
    D19ConstructiveFinalInputs h :=
  data.toD19ConstructiveFinalLinearFixedEnumerationInputs.toD19ConstructiveFinalInputs

/-- Forget all specialized boundaries down to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19FinalLinearFixedEnumerationReflectionInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalLinearFixedEnumerationInputs.toD19FinalInputs

/-- Final inputs in the linear-character, fixed-enumeration, reflection-copy
form cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalLinearFixedEnumerationReflectionInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalLinearFixedEnumerationInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalLinearFixedEnumerationInputs⟩

end D19FinalLinearFixedEnumerationReflectionInputs

end Moore57
