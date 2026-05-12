import Moore57.D19OnMoore57.D19Core.D19ConstructiveFinalInputs
import Moore57.D19OnMoore57.Fixed.FixedUpperBoundEnumeration

/-!
# Constructive final D19 inputs with fixed-point enumeration

This file refines `D19ConstructiveFinalInputs` by replacing the fixed-count
part of the final character input with an explicit enumeration of the
rotation-one fixed vertices.  The representation-character input remains
separate from the geometric fixed-count bound.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Constructive final input record whose fixed-count bound is supplied by an
explicit finite enumeration of the vertices fixed by `h.rotation 1`.

The old bundled `TraceCharacterData` is not needed for the fixed-count part:
the field `fixedEnumeration` is converted to `RotationFixedUpperBoundInput`
independently. -/
structure D19ConstructiveFinalFixedEnumerationInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and rotation character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Explicit finite cover of the rotation-one fixed vertices, of size at
  most nineteen. -/
  fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h
  /-- Constructive enumeration of the selected 56 moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Constructive two-copy adjacent-moved partition over the selected bases. -/
  adjacentMoved :
    AdjacentMovedTwoCopyPartition38Witness h orbitBase.base

namespace D19ConstructiveFinalFixedEnumerationInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the representation input and fixed-point enumeration into the
split final character input. -/
def toD19FinalCharacterInputs
    (data : D19ConstructiveFinalFixedEnumerationInputs h) :
    D19FinalCharacterInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedEnumeration.toRotationFixedUpperBoundInput

/-- Forget the fixed-point enumeration boundary down to the existing
constructive final input record. -/
def toD19ConstructiveFinalInputs
    (data : D19ConstructiveFinalFixedEnumerationInputs h) :
    D19ConstructiveFinalInputs h where
  character := data.toD19FinalCharacterInputs
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved

/-- Forget the fixed-point enumeration boundary all the way to final inputs. -/
noncomputable def toD19FinalInputs
    (data : D19ConstructiveFinalFixedEnumerationInputs h) :
    D19FinalInputs h :=
  data.toD19ConstructiveFinalInputs.toD19FinalInputs

/-- Constructive final inputs with fixed-point enumeration cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19ConstructiveFinalFixedEnumerationInputs h) := by
  rintro ⟨data⟩
  exact D19ConstructiveFinalInputs.not_nonempty h
    ⟨data.toD19ConstructiveFinalInputs⟩

/-- Convenience constructor using old bundled `TraceCharacterData` only for
the representation-character input.  The fixed-count upper bound is supplied
independently by `fixedEnumeration`. -/
noncomputable def ofTraceCharacterDataRepresentation
    (h : D19ActsOnMoore57 V Γ)
    (hold : TraceCharacterData Γ h.rotation h.a1)
    (fixedEnumeration : D19ActsOnMoore57.RotationOneFixedEnumeration h)
    (orbitBase : OrbitBaseSelectionEnumeration h)
    (adjacentMoved :
      AdjacentMovedTwoCopyPartition38Witness h orbitBase.base) :
    D19ConstructiveFinalFixedEnumerationInputs h where
  representation :=
    D19ActsOnMoore57.D19RepresentationCharacterInput.ofTraceCharacterData
      h hold
  fixedEnumeration := fixedEnumeration
  orbitBase := orbitBase
  adjacentMoved := adjacentMoved

end D19ConstructiveFinalFixedEnumerationInputs

end Moore57
