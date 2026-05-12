import Moore57.D19OnMoore57.D19Core.RepresentationCharacterFromData
import Moore57.D19OnMoore57.Final.RepresentationUpperBoundAvoidanceCarrier
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionFixedPartCriteria
import Moore57.D19OnMoore57.Orbit.BaseSelectionCarrierCriteria
import Moore57.D19OnMoore57.Rotation.FixedUpperBoundFromData

/-!
# Final D19 inputs from trace core, rotation-one fixed count, and fixed residual carrier data

This file provides a thinner final-boundary wrapper around the existing carrier
final boundary.  It asks for trace core data directly, only the rotation-one
fixed-count upper bound, a carrier base-selection witness, and the canonical
rotation-fixed residual-side adjacent-moved witness.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Thin final D19 input package using trace core data, the rotation-one fixed
count upper bound, a carrier base selection, and the canonical rotation-fixed
residual-side adjacent-moved witness. -/
structure D19FinalTraceRotationOneFixedPartCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- The fixed-count bound only for rotation by `1`. -/
  rotationOneFixedCount_le_nineteen :
    fixedVertexCount (h.rotation 1) ≤ 19
  /-- Bounded carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCarrierWitness h
  /-- Canonical rotation-fixed residual-side adjacent-moved witness over the
  input produced from the carrier witness. -/
  adjacentMoved :
    AdjacentMovedReflectionFixedPartCriteria38Witness h orbitBase.toInput

namespace D19FinalTraceRotationOneFixedPartCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the thin trace/fixed-part carrier boundary to the existing carrier
final boundary. -/
noncomputable def toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs
    (data : D19FinalTraceRotationOneFixedPartCarrierInputs h) :
    D19FinalRepresentationUpperBoundAvoidanceCarrierInputs h where
  representation :=
    D19ActsOnMoore57.D19RepresentationCharacterInput.ofTraceCharacterCoreData
      data.traceCore
  fixedUpperBound :=
    D19ActsOnMoore57.RotationFixedUpperBoundInput.of_rotation_one_le_nineteen
      data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  adjacentMoved := data.adjacentMoved.toAvoidanceSplit38Witness

/-- Forget the thin trace/fixed-part carrier presentation down to the final
input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalTraceRotationOneFixedPartCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs.toD19FinalInputs

/-- Thin trace/fixed-part carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalTraceRotationOneFixedPartCarrierInputs h) := by
  rintro ⟨data⟩
  exact D19FinalRepresentationUpperBoundAvoidanceCarrierInputs.not_nonempty h
    ⟨data.toD19FinalRepresentationUpperBoundAvoidanceCarrierInputs⟩

end D19FinalTraceRotationOneFixedPartCarrierInputs

end Moore57
