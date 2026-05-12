import Moore57.D19OnMoore57.Final.TraceRotationOneCanonicalAFiberOnlyContributionCarrier
import Moore57.D19OnMoore57.AFiber.OnlyContributionConstant

/-!
# Final D19 inputs with A-fiber cardinality data

This file adds a thin final boundary that keeps the carrier/reflected-avoidance
shape, but replaces the A-fiber contribution record by the concrete filtered
cardinality statement on the A-fiber side.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Carrier/reflected-avoidance final inputs whose A-fiber contribution is
provided only as the concrete filtered cardinality `38` for every nonzero
rotation step. -/
structure D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs
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
  /-- The concrete A-fiber-side filtered cardinality is `38` for every nonzero
  rotation step. -/
  aFiber_card_eq_thirtyEight :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38

namespace D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Package the concrete A-fiber-cardinality statement as A-fiber-only
contribution data. -/
noncomputable def
    toD19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs h
    where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  contribution :=
    { aFiberContribution :=
        fixedAFiberAFiberCard h (data.coords.fiberUnion data.indices)
      aFiber_contribution := by
        intro d hd
        rfl
      aFiber_eq_thirtyEight := data.aFiber_card_eq_thirtyEight }

/-- Forget the A-fiber-cardinality carrier presentation down to the final input
record. -/
noncomputable def toD19FinalInputs
    (data :
      D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs
    |>.toD19FinalInputs

/-- The A-fiber-cardinality carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalAFiberOnlyContributionCarrierInputs⟩

end D19FinalTraceRotationOneCanonicalAFiberCardCarrierInputs

end Moore57
