import Moore57.D19OnMoore57.Final.D19FinalRepresentationUpperBoundAvoidanceSplit
import Moore57.D19OnMoore57.Orbit.OrbitBaseSelectionCarrierCriteria
import Moore57.D19OnMoore57.Orbit.OrbitBaseSelectionEnumeration

/-!
# Final D19 inputs from carrier-style base-selection witnesses

This file gives final-boundary wrappers whose selected rotation-orbit bases are
provided by the more constructive carrier, witness, and enumeration interfaces,
then converted to the downstream `OrbitBaseSelectionInput` used by the split
avoidance boundary.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final D19 input package using a constructive base-selection witness instead
of storing the downstream `OrbitBaseSelectionInput` directly. -/
structure D19FinalRepresentationUpperBoundAvoidanceWitnessInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Constructive witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionWitness h
  /-- Split avoidance-based adjacent-moved witness over the input produced from
  the constructive base-selection witness. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput

namespace D19FinalRepresentationUpperBoundAvoidanceWitnessInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the witness-based final boundary to the split final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceSplitInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase.toInput
  adjacentMoved := data.adjacentMoved

/-- Convert the witness-based final boundary to the avoidance final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceInputs

/-- Forget the witness presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs.toD19FinalInputs

/-- Final witness-based, split avoidance adjacent-moved inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceWitnessInputs

/-- Final D19 input package using a bounded carrier witness instead of storing
the downstream `OrbitBaseSelectionInput` directly. -/
structure D19FinalRepresentationUpperBoundAvoidanceCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Bounded carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCarrierWitness h
  /-- Split avoidance-based adjacent-moved witness over the input produced from
  the carrier witness. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput

namespace D19FinalRepresentationUpperBoundAvoidanceCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the carrier-based final boundary to the witness-based boundary. -/
noncomputable def toWitnessInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase.toWitness
  adjacentMoved := by
    simpa [OrbitBaseSelectionCarrierWitness.toInput] using data.adjacentMoved

/-- Convert the carrier-based final boundary to the split final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceSplitInputs h :=
  data.toWitnessInputs.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs

/-- Convert the carrier-based final boundary to the avoidance final boundary.
-/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceInputs

/-- Forget the carrier presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs.toD19FinalInputs

/-- Final carrier-based, split avoidance adjacent-moved inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceCarrierInputs

/-- Final D19 input package using an explicit coordinate enumeration for the
selected moved rotation orbits. -/
structure D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic multiplicities and nontrivial rotation
  character values. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Coarse upper bound for nontrivial rotation fixed vertices. -/
  fixedUpperBound : D19ActsOnMoore57.RotationFixedUpperBoundInput h
  /-- Coordinate enumeration of the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionEnumeration h
  /-- Split avoidance-based adjacent-moved witness over the input produced from
  the coordinate enumeration. -/
  adjacentMoved :
    AdjacentMovedReflectionAvoidanceSplit38Witness h orbitBase.toInput

namespace D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the enumeration-based final boundary to the witness-based boundary.
-/
noncomputable def toWitnessInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceWitnessInputs h where
  representation := data.representation
  fixedUpperBound := data.fixedUpperBound
  orbitBase := data.orbitBase.toWitness
  adjacentMoved := by
    simpa [OrbitBaseSelectionEnumeration.toInput] using data.adjacentMoved

/-- Convert the enumeration-based final boundary to the split final boundary.
-/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceSplitInputs h :=
  data.toWitnessInputs.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs

/-- Convert the enumeration-based final boundary to the avoidance final
boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs
    |>.toD19FinalRepresentationUpperBoundAvoidanceInputs

/-- Forget the enumeration presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs.toD19FinalInputs

/-- Final enumeration-based, split avoidance adjacent-moved inputs cannot
exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceSplitInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceSplitInputs⟩

end D19FinalRepresentationUpperBoundAvoidanceEnumerationInputs

end Moore57
