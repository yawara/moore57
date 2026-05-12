import Moore57.D19OnMoore57.Final.TraceRotationOneCanonicalAvoidanceCarrier
import Moore57.D19OnMoore57.Final.TraceRotationOneCanonicalAFiberCardCarrier
import Moore57.D19OnMoore57.Final.TraceRotationOneCanonicalInclusionCarrier
import Moore57.D19OnMoore57.AFiber.OnlyContributionConstant

/-!
# Final D19 inputs with hybrid canonical boundary data

This file adds the current thinnest final boundary combining:

* canonical orbit-base carrier data,
* canonical reflected avoidance,
* moving/A-fiber identification in mutual-inclusion form, and
* the direct A-fiber filtered cardinality statement `38`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Hybrid final inputs: canonical carrier and reflected avoidance are kept at
the boundary, the moving residual is identified with the selected A-fiber union
by inclusions, and the A-fiber contribution is supplied by the direct
cardinality statement `38`. -/
structure D19FinalTraceRotationOneHybridBoundaryInputs
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
  /-- The moving residual complement is contained in the selected A-fiber union. -/
  moving_subset_aFiber :
    rotationOneMovingResidualPart h orbitBase.toCarrierWitness.toInput
        reflectedAvoidance.k ⊆
      coords.fiberUnion indices
  /-- The selected A-fiber union is contained in the moving residual complement. -/
  aFiber_subset_moving :
    coords.fiberUnion indices ⊆
      rotationOneMovingResidualPart h orbitBase.toCarrierWitness.toInput
        reflectedAvoidance.k
  /-- The concrete A-fiber-side filtered cardinality is `38` for every nonzero
  rotation step. -/
  aFiber_card_eq_thirtyEight :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38

namespace D19FinalTraceRotationOneHybridBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- The inclusion-form hypotheses recover the moving/A-fiber equality expected
by the existing A-fiber-cardinality carrier boundary. -/
theorem moving_eq_aFiber
    (data : D19FinalTraceRotationOneHybridBoundaryInputs h) :
    rotationOneMovingResidualPart h data.orbitBase.toCarrierWitness.toInput
        data.reflectedAvoidance.k =
      data.coords.fiberUnion data.indices :=
  Finset.Subset.antisymm
    data.moving_subset_aFiber
    data.aFiber_subset_moving

/-- Forget the hybrid canonical boundary to the existing A-fiber-cardinality
carrier boundary. -/
noncomputable def toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs
    (data : D19FinalTraceRotationOneHybridBoundaryInputs h) :
    D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs h
    where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase.toCarrierWitness
  reflectedAvoidance := data.reflectedAvoidance.toCarrierReflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := by
    simpa using data.moving_eq_aFiber
  aFiber_card_eq_thirtyEight := data.aFiber_card_eq_thirtyEight

/-- Forget the hybrid canonical boundary presentation down to the final input
record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalTraceRotationOneHybridBoundaryInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs
    |>.toD19FinalInputs

/-- The hybrid canonical boundary final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalTraceRotationOneHybridBoundaryInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs⟩

end D19FinalTraceRotationOneHybridBoundaryInputs

end Moore57
