import Moore57.D19FinalTraceRotationOneCanonicalCarrier
import Moore57.AdjacentMovedReflectionCanonicalAFiberInclusions

/-!
# Final D19 inputs with canonical carrier inclusion data

This file adds a thin final boundary that uses the canonical carrier witness
directly, but states the moving/A-fiber identification by mutual containment
instead of a direct finset equality.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Final inputs whose canonical-carrier moving residual is identified with an
A-fiber union by the two inclusions that imply equality. -/
structure D19FinalTraceRotationOneCanonicalInclusionCarrierInputs
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
  /-- A-fiber-only contribution data replacing the split contribution field. -/
  contribution :
    AFiberOnlyContribution38Data h orbitBase.toCarrierWitness.toInput
      reflectedAvoidance.k (coords.fiberUnion indices)

namespace D19FinalTraceRotationOneCanonicalInclusionCarrierInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- The two inclusion hypotheses recover the moving/A-fiber equality expected
by the existing canonical-carrier boundary. -/
theorem moving_eq_aFiber
    (data : D19FinalTraceRotationOneCanonicalInclusionCarrierInputs h) :
    rotationOneMovingResidualPart h data.orbitBase.toCarrierWitness.toInput
        data.reflectedAvoidance.k =
      data.coords.fiberUnion data.indices :=
  Finset.Subset.antisymm
    data.moving_subset_aFiber
    data.aFiber_subset_moving

/-- Forget the inclusion presentation to the existing canonical-carrier
boundary. -/
noncomputable def toD19FinalTraceRotationOneCanonicalCarrierInputs
    (data : D19FinalTraceRotationOneCanonicalInclusionCarrierInputs h) :
    D19FinalTraceRotationOneCanonicalCarrierInputs h
    where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen :=
    data.rotationOneFixedCount_le_nineteen
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_eq_aFiber := data.moving_eq_aFiber
  contribution := data.contribution

/-- Forget the inclusion-form canonical-carrier presentation down to the final
input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalTraceRotationOneCanonicalInclusionCarrierInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneCanonicalCarrierInputs.toD19FinalInputs

/-- The inclusion-form canonical carrier final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceRotationOneCanonicalInclusionCarrierInputs h) := by
  rintro ⟨data⟩
  exact
    D19FinalTraceRotationOneCanonicalCarrierInputs.not_nonempty
      h
      ⟨data.toD19FinalTraceRotationOneCanonicalCarrierInputs⟩

end D19FinalTraceRotationOneCanonicalInclusionCarrierInputs

end Moore57
