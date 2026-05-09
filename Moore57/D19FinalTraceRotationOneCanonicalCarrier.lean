import Moore57.D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrier
import Moore57.OrbitBaseSelectionCarrierCanonical

/-!
# Final D19 inputs with canonical carrier data

This file adds a thin final boundary that uses the canonical carrier witness
directly, then forgets it to the general carrier boundary.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final inputs whose orbit-base carrier is the canonical orbit-family union. -/
structure D19FinalTraceRotationOneCanonicalCarrierInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- The fixed-count bound only for rotation by `1`. -/
  rotationOneFixedCount_le_nineteen :
    fixedVertexCount (h.rotation 1) ≤ 19
  /-- Canonical carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCanonicalCarrierWitness h
  /-- Reflected-base avoidance stated against the induced carrier witness. -/
  reflectedAvoidance :
    OrbitBaseSelectionCarrierReflectedAvoidance h orbitBase.toCarrierWitness
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

namespace D19FinalTraceRotationOneCanonicalCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the canonical carrier witness to the general carrier boundary. -/
noncomputable def
    toD19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs
    (data : D19FinalTraceRotationOneCanonicalCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs h
    where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase.toCarrierWitness
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  contribution := data.contribution

/-- Forget the canonical carrier presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalTraceRotationOneCanonicalCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs
    |>.toD19FinalInputs

/-- The canonical carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalTraceRotationOneCanonicalCarrierInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs⟩

end D19FinalTraceRotationOneCanonicalCarrierInputs

end Moore57
