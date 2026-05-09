import Moore57.D19FinalTraceRotationOneCanonicalCarrier
import Moore57.CanonicalCarrierReflectedAvoidance

/-!
# Final D19 inputs with canonical carrier avoidance

This file adds a thin final boundary whose reflected avoidance is stated
directly for the canonical carrier witness, then forgets it to the existing
canonical-carrier final boundary.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final inputs whose orbit-base carrier and reflected avoidance are both
stated directly in canonical-carrier form. -/
structure D19FinalTraceRotationOneCanonicalAvoidanceCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- The fixed-count bound only for rotation by `1`. -/
  rotationOneFixedCount_le_nineteen :
    fixedVertexCount (h.rotation 1) ≤ 19
  /-- Canonical carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCanonicalCarrierWitness h
  /-- Reflected-base avoidance stated directly against the canonical carrier. -/
  reflectedAvoidance :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h orbitBase
  /-- A coordinate system for the A-side fibers. -/
  coords : AFiberCoordinates.{u, uP} Γ
  /-- The A-side fiber indices used in the moving residual. -/
  indices : Finset (ZMod 19)
  /-- The moving residual complement is exactly the selected A-fiber union. -/
  moving_eq_aFiber :
    rotationOneMovingResidualPart h orbitBase.toCarrierWitness.toInput
        reflectedAvoidance.k =
      coords.fiberUnion indices
  /-- A-fiber-only contribution data replacing the split contribution field. -/
  contribution :
    AFiberOnlyContribution38Data h orbitBase.toCarrierWitness.toInput
      reflectedAvoidance.k (coords.fiberUnion indices)

namespace D19FinalTraceRotationOneCanonicalAvoidanceCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget canonical reflected avoidance to the carrier-reflected-avoidance
boundary. -/
noncomputable def toD19FinalTraceRotationOneCanonicalCarrierInputs
    (data : D19FinalTraceRotationOneCanonicalAvoidanceCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalCarrierInputs h
    where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance.toCarrierReflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  contribution := data.contribution

/-- Forget the canonical-avoidance carrier presentation down to the final input
record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalTraceRotationOneCanonicalAvoidanceCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalCarrierInputs.toD19FinalInputs

/-- The canonical-avoidance carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceRotationOneCanonicalAvoidanceCarrierInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalCarrierInputs⟩

end D19FinalTraceRotationOneCanonicalAvoidanceCarrierInputs

end Moore57
