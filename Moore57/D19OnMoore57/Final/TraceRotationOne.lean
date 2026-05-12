import Moore57.D19OnMoore57.AdjacentMoved.ReflectionAFiber
import Moore57.D19OnMoore57.AFiber.ContributionDecomposition
import Moore57.D19OnMoore57.AFiber.ContributionOnlyCriteria
import Moore57.D19OnMoore57.AFiber.OnlyContributionConstant
import Moore57.D19OnMoore57.CanonicalCarrier.ReflectedAvoidance
import Moore57.D19OnMoore57.D19Core.RepresentationCharacterFromData
import Moore57.D19OnMoore57.Final.RepresentationUpperBound
import Moore57.D19OnMoore57.Orbit.BaseSelection
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

