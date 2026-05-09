import Moore57.D19FinalTraceRotationOneCanonicalAFiberContributionCarrier
import Moore57.AFiberContributionOnlyCriteria

/-!
# Final D19 inputs with A-fiber-only contribution data

This file adds a thin final boundary that keeps the carrier/reflected-avoidance
shape, but replaces the fixed/A-fiber split contribution data by contribution
data carried only on the A-fiber side.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Carrier/reflected-avoidance final inputs whose contribution is provided
only through the A-fiber side. -/
structure D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs
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
    rotationOneMovingResidualPart h orbitBase.toInput
        reflectedAvoidance.k =
      coords.fiberUnion indices
  /-- A-fiber-only contribution data replacing the split contribution field. -/
  contribution :
    AFiberOnlyContribution38Data h orbitBase.toInput
      reflectedAvoidance.k (coords.fiberUnion indices)

namespace D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the A-fiber-only contribution presentation to the split-contribution
carrier boundary. -/
noncomputable def
    toD19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs h
    where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  contribution := data.contribution.toFixedAFiberContribution38Data

/-- Forget the A-fiber-only contribution carrier presentation down to the final
input record. -/
noncomputable def toD19FinalInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs
    |>.toD19FinalInputs

/-- The A-fiber-only contribution carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs
        h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs⟩

end D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs

end Moore57
