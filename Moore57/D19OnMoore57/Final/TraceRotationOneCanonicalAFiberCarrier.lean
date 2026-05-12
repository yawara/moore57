import Moore57.D19OnMoore57.Final.TraceRotationOneFixedPartCarrier
import Moore57.D19OnMoore57.AdjacentMoved.ReflectionCanonicalAFiberCriteria
import Moore57.D19OnMoore57.Orbit.BaseSelectionCarrierAvoidance

/-!
# Final D19 inputs from trace core, rotation-one fixed count, carrier data, and A-fibers

This file packages the latest thin final boundary through the already proved
trace/fixed-part carrier boundary.  The residual side is supplied in the
canonical rotation-fixed plus A-fiber form, then forgotten to the fixed-part
carrier criterion.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Thin final D19 input package using trace core data, only the rotation-one
fixed-count bound, a carrier base selection, and the canonical fixed/A-fiber
adjacent-moved witness over the carrier-produced input. -/
structure D19FinalTraceRotationOneCanonicalAFiberCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- The fixed-count bound only for rotation by `1`. -/
  rotationOneFixedCount_le_nineteen :
    fixedVertexCount (h.rotation 1) ≤ 19
  /-- Bounded carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCarrierWitness h
  /-- Canonical rotation-fixed residual side with an A-fiber moving side, over
  the input produced from the carrier witness. -/
  adjacentMoved :
    AdjacentMovedReflectionCanonicalAFiberCriteria38Witness.{u, uP}
      h orbitBase.toInput

namespace D19FinalTraceRotationOneCanonicalAFiberCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the canonical fixed/A-fiber residual presentation to the fixed-part
carrier final boundary. -/
noncomputable def toD19FinalTraceRotationOneFixedPartCarrierInputs
    (data : D19FinalTraceRotationOneCanonicalAFiberCarrierInputs h) :
    D19FinalTraceRotationOneFixedPartCarrierInputs h where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  adjacentMoved :=
    { k := data.adjacentMoved.k
      fixedUpperBound :=
        D19ActsOnMoore57.RotationFixedUpperBoundInput.of_rotation_one_le_nineteen
          data.rotationOneFixedCount_le_nineteen
      reflection_not_mem_orbitFamilyUnion :=
        data.adjacentMoved.reflection_not_mem_orbitFamilyUnion
      residual_contribution := by
        intro d hd
        rw [data.adjacentMoved.moving_eq_aFiber]
        exact data.adjacentMoved.residual_contribution d hd }

/-- Forget the canonical fixed/A-fiber carrier presentation down to the final
input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalTraceRotationOneCanonicalAFiberCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneFixedPartCarrierInputs.toD19FinalInputs

/-- Thin trace/canonical-A-fiber carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalTraceRotationOneCanonicalAFiberCarrierInputs h) := by
  rintro ⟨data⟩
  exact D19FinalTraceRotationOneFixedPartCarrierInputs.not_nonempty h
    ⟨data.toD19FinalTraceRotationOneFixedPartCarrierInputs⟩

end D19FinalTraceRotationOneCanonicalAFiberCarrierInputs

/-- Variant that keeps the reflected-base avoidance condition in carrier form
and supplies only the canonical A-fiber residual-side data separately. -/
structure D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- The fixed-count bound only for rotation by `1`. -/
  rotationOneFixedCount_le_nineteen :
    fixedVertexCount (h.rotation 1) ≤ 19
  /-- Bounded carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCarrierWitness h
  /-- Reflected-base avoidance stated directly against the carrier. -/
  reflectedAvoidance :
    OrbitBaseSelectionCarrierReflectedAvoidance h orbitBase
  /-- A coordinate system for the A-side fibers. -/
  coords : AFiberCoordinates.{u, uP} Γ
  /-- The A-side fiber indices used in the moving residual. -/
  indices : Finset (ZMod 19)
  /-- The moving residual complement is exactly the selected A-fiber union. -/
  moving_eq_aFiber :
    rotationOneMovingResidualPart h orbitBase.toInput reflectedAvoidance.k =
      coords.fiberUnion indices
  /-- The fixed/A-fiber split contributes `38` for every nontrivial rotation
  offset. -/
  residual_contribution :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ((rotationOneFixedResidualPart h orbitBase.toInput
          reflectedAvoidance.k).filter fun y =>
          Γ.Adj y (h.rotation d y)).card +
        ((coords.fiberUnion indices).filter fun y =>
          Γ.Adj y (h.rotation d y)).card =
        38

namespace D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the carrier-form reflected-avoidance variant to the canonical
fixed/A-fiber carrier boundary. -/
noncomputable def toCanonicalAFiberCarrierInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs
        h) :
    D19FinalTraceRotationOneCanonicalAFiberCarrierInputs h where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  adjacentMoved :=
    { k := data.reflectedAvoidance.k
      reflection_not_mem_orbitFamilyUnion :=
        data.reflectedAvoidance.reflected_base_not_mem_toInput_orbitFamilyUnion
      coords := data.coords
      indices := data.indices
      moving_eq_aFiber := data.moving_eq_aFiber
      residual_contribution := data.residual_contribution }

/-- Convert the carrier-form reflected-avoidance variant to the fixed-part
carrier final boundary. -/
noncomputable def toD19FinalTraceRotationOneFixedPartCarrierInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs
        h) :
    D19FinalTraceRotationOneFixedPartCarrierInputs h :=
  data.toCanonicalAFiberCarrierInputs
    |>.toD19FinalTraceRotationOneFixedPartCarrierInputs

/-- Forget the carrier-form reflected-avoidance presentation down to the final
input record. -/
noncomputable def toD19FinalInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs
        h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneFixedPartCarrierInputs.toD19FinalInputs

/-- The carrier-form reflected-avoidance final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs
        h) := by
  rintro ⟨data⟩
  exact D19FinalTraceRotationOneCanonicalAFiberCarrierInputs.not_nonempty h
    ⟨data.toCanonicalAFiberCarrierInputs⟩

end D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs

end Moore57
