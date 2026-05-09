import Moore57.D19FinalTraceRotationOneHybridBoundary
import Moore57.TraceCoreCharacterBoundary
import Moore57.RotationOneFixedBoundBoundary
import Moore57.AFiberCardinalityBoundary

/-!
# Final D19 inputs with exposed hybrid boundary records

This file is the thin final entry point over the current hybrid boundary.  It
keeps trace-core, rotation-one fixed-bound, and A-fiber cardinality assumptions
in their already exposed boundary records, then forgets those packages to the
current hybrid input record.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Exposed hybrid final inputs: the raw trace-core, rotation-one fixed-bound,
and A-fiber cardinality fields of the current hybrid boundary are replaced by
their dedicated final-boundary records. -/
structure D19FinalExposedHybridBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Final-boundary trace core for the representation-character side. -/
  traceCore : D19ActsOnMoore57.TraceCoreCharacterBoundary h
  /-- Packaged final-boundary fixed-count assumption for rotation by `1`. -/
  fixedBound : D19ActsOnMoore57.RotationOneFixedBoundBoundaryInput h
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
  /-- Packaged final-boundary A-fiber-side filtered cardinality statement. -/
  aFiberCardinality :
    AFiberCardinality38Boundary h coords indices

namespace D19FinalExposedHybridBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- The inclusion-form hypotheses recover the moving/A-fiber equality expected
by lower final boundaries. -/
theorem moving_eq_aFiber
    (data : D19FinalExposedHybridBoundaryInputs h) :
    rotationOneMovingResidualPart h data.orbitBase.toCarrierWitness.toInput
        data.reflectedAvoidance.k =
      data.coords.fiberUnion data.indices :=
  Finset.Subset.antisymm
    data.moving_subset_aFiber
    data.aFiber_subset_moving

/-- Forget the exposed boundary packages to the current hybrid final boundary. -/
noncomputable def toD19FinalTraceRotationOneHybridBoundaryInputs
    (data : D19FinalExposedHybridBoundaryInputs h) :
    D19FinalTraceRotationOneHybridBoundaryInputs h where
  traceCore := data.traceCore.toTraceCharacterCoreData
  rotationOneFixedCount_le_nineteen :=
    data.fixedBound.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_subset_aFiber := data.moving_subset_aFiber
  aFiber_subset_moving := data.aFiber_subset_moving
  aFiber_card_eq_thirtyEight :=
    data.aFiberCardinality.card_eq_thirtyEight

/-- Build the exposed boundary presentation from the current hybrid final
boundary by packaging its remaining raw fields. -/
noncomputable def ofD19FinalTraceRotationOneHybridBoundaryInputs
    (data : D19FinalTraceRotationOneHybridBoundaryInputs h) :
    D19FinalExposedHybridBoundaryInputs h where
  traceCore :=
    D19ActsOnMoore57.TraceCoreCharacterBoundary.ofTraceCharacterCoreData
      data.traceCore
  fixedBound :=
    { rotationOneFixedCount_le_nineteen :=
        data.rotationOneFixedCount_le_nineteen }
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_subset_aFiber := data.moving_subset_aFiber
  aFiber_subset_moving := data.aFiber_subset_moving
  aFiberCardinality :=
    AFiberCardinality38Boundary.of_card_eq_thirtyEight
      data.aFiber_card_eq_thirtyEight

/-- Forget the exposed hybrid presentation down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalExposedHybridBoundaryInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneHybridBoundaryInputs
    |>.toD19FinalInputs

/-- Exposed hybrid final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19FinalExposedHybridBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneHybridBoundaryInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneHybridBoundaryInputs⟩

/-- Any exposed hybrid input gives a current hybrid input. -/
theorem nonempty_to_hybrid :
    Nonempty (D19FinalExposedHybridBoundaryInputs.{u, uP} h) →
      Nonempty (D19FinalTraceRotationOneHybridBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact ⟨data.toD19FinalTraceRotationOneHybridBoundaryInputs⟩

/-- Any current hybrid input can be repackaged as an exposed hybrid input. -/
theorem nonempty_of_hybrid :
    Nonempty (D19FinalTraceRotationOneHybridBoundaryInputs.{u, uP} h) →
      Nonempty (D19FinalExposedHybridBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact ⟨ofD19FinalTraceRotationOneHybridBoundaryInputs data⟩

/-- The exposed presentation is equivalent at the `Nonempty` level to the
current hybrid final boundary. -/
theorem nonempty_iff_hybrid :
    Nonempty (D19FinalExposedHybridBoundaryInputs.{u, uP} h) ↔
      Nonempty (D19FinalTraceRotationOneHybridBoundaryInputs.{u, uP} h) := by
  constructor
  · exact nonempty_to_hybrid
  · exact nonempty_of_hybrid

end D19FinalExposedHybridBoundaryInputs

end Moore57
