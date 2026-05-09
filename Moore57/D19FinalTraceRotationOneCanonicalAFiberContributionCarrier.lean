import Moore57.D19FinalTraceRotationOneCanonicalAFiberCarrier
import Moore57.AFiberContributionDecomposition

/-!
# Final D19 inputs with split fixed/A-fiber contribution data

This file adds a thin final boundary that keeps the carrier/reflected-avoidance
shape, but replaces the direct residual contribution equation by
`FixedAFiberContribution38Data`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Carrier/reflected-avoidance final inputs whose residual contribution is
provided through split fixed/A-fiber contribution data. -/
structure D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs
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
  /-- Split fixed/A-fiber contribution data replacing the direct residual
  contribution field. -/
  contribution :
    FixedAFiberContribution38Data h orbitBase.toInput
      reflectedAvoidance.k (coords.fiberUnion indices)

namespace D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the split contribution presentation to the existing carrier-form
reflected-avoidance boundary. -/
noncomputable def
    toD19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs h
    where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  residual_contribution := data.contribution.residual_contribution

/-- Forget the split-contribution carrier presentation down to the final input
record. -/
noncomputable def toD19FinalInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs
    |>.toD19FinalInputs

/-- The split-contribution carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalAFiberCarrierReflectedAvoidanceInputs⟩

end D19FinalTraceRotationOneCanonicalAFiberContributionCarrierInputs

end Moore57
