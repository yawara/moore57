import Moore57.D19OnMoore57.AFiber.OrbitBaseSelection
import Moore57.D19OnMoore57.AFiber.OrbitMovingResidual
import Moore57.D19OnMoore57.Final.CharacterAFiberBoundary
import Moore57.D19OnMoore57.Final.TraceRotationOne
import Moore57.D19OnMoore57.Rotation.FixedRegularity

/-!
# Final D19 boundaries with automatic rotation fixed-count bounds

This file removes the now-proved rotation fixed-count upper bound from two thin
final-boundary interfaces.  The old records are left unchanged; these wrappers
fill their fixed-count fields from
`D19ActsOnMoore57.rotation_one_fixedVertexCount_eq_one`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- The proved exact fixed count supplies the coarse fixed-count upper-bound
input for all nontrivial rotations. -/
def RotationFixedUpperBoundInput.of_rotation_fixed_card_eq_one
    (h : D19ActsOnMoore57 V Γ) :
    RotationFixedUpperBoundInput h where
  fixed_le_nineteen := by
    intro d hd
    rw [h.rotation_fixed_card_eq_one hd]
    norm_num

end D19ActsOnMoore57

namespace D19FinalCharacterInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Build final character inputs from only the representation-character data;
the fixed-count upper bound is now a theorem of the ambient D19 action. -/
def ofRepresentationCharacterInput
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h) :
    D19FinalCharacterInputs h where
  representation := representation
  fixedUpperBound :=
    D19ActsOnMoore57.RotationFixedUpperBoundInput.of_rotation_fixed_card_eq_one h

/-- Build final character inputs from trace-core data, with the fixed-count
upper bound filled automatically. -/
def ofTraceCharacterCoreData
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1) :
    D19FinalCharacterInputs h :=
  ofRepresentationCharacterInput
    (D19ActsOnMoore57.D19RepresentationCharacterInput.ofTraceCharacterCoreData
      traceCore)

end D19FinalCharacterInputs

/-- Direct-character/A-fiber boundary inputs with no fixed-count upper-bound
field. -/
structure D19FinalCharacterAFiberNoFixedBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-theoretic character data. -/
  representation : D19ActsOnMoore57.D19RepresentationCharacterInput h
  /-- Downstream orbit-base selection input. -/
  orbitInput : OrbitBaseSelectionInput h
  /-- Reflected-copy parameter. -/
  k : ZMod 19
  /-- Reflected selected bases avoid the selected orbit-family union. -/
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
        orbitInput.orbitFamilyUnion
  /-- A coordinate system for the A-side fibers. -/
  coords : AFiberCoordinates.{u, uP} Γ
  /-- The A-side fiber indices used in the moving residual. -/
  indices : Finset (ZMod 19)
  /-- The moving residual complement is contained in the selected A-fiber
  union. -/
  moving_subset_aFiber :
    rotationOneMovingResidualPart h orbitInput k ⊆
      coords.fiberUnion indices
  /-- The selected A-fiber union is contained in the moving residual
  complement. -/
  aFiber_subset_moving :
    coords.fiberUnion indices ⊆
      rotationOneMovingResidualPart h orbitInput k
  /-- Packaged final-boundary A-fiber-side filtered cardinality statement. -/
  aFiberCardinality :
    AFiberCardinality38Boundary h coords indices

namespace D19FinalCharacterAFiberNoFixedBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Reinsert the proved fixed-count bound and recover the existing direct
character/A-fiber boundary. -/
noncomputable def toD19FinalCharacterAFiberBoundaryInputs
    (data : D19FinalCharacterAFiberNoFixedBoundaryInputs h) :
    D19FinalCharacterAFiberBoundaryInputs.{u, uP} h where
  character :=
    D19FinalCharacterInputs.ofRepresentationCharacterInput data.representation
  orbitInput := data.orbitInput
  k := data.k
  reflection_not_mem_orbitFamilyUnion :=
    data.reflection_not_mem_orbitFamilyUnion
  coords := data.coords
  indices := data.indices
  moving_subset_aFiber := data.moving_subset_aFiber
  aFiber_subset_moving := data.aFiber_subset_moving
  aFiberCardinality := data.aFiberCardinality

/-- Forget the no-fixed-bound boundary down to the final input record. -/
noncomputable def toD19FinalInputs
    (data : D19FinalCharacterAFiberNoFixedBoundaryInputs h) :
    D19FinalInputs h :=
  data.toD19FinalCharacterAFiberBoundaryInputs.toD19FinalInputs

/-- Direct-character/A-fiber no-fixed-bound final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact D19FinalCharacterAFiberBoundaryInputs.not_nonempty h
    ⟨data.toD19FinalCharacterAFiberBoundaryInputs⟩

end D19FinalCharacterAFiberNoFixedBoundaryInputs

/-- Trace-core hybrid boundary inputs with no fixed-count upper-bound field. -/
structure D19FinalTraceHybridNoFixedBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Split trace/multiplicity data for the representation-character side. -/
  traceCore : TraceCharacterCoreData Γ h.rotation h.a1
  /-- Canonical carrier witness for the selected moved rotation orbits. -/
  orbitBase : OrbitBaseSelectionCanonicalCarrierWitness h
  /-- Reflected-base avoidance stated directly against the canonical carrier. -/
  reflectedAvoidance :
    OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h orbitBase
  /-- A coordinate system for the A-side fibers. -/
  coords : AFiberCoordinates.{u, uP} Γ
  /-- The A-side fiber indices used in the moving residual. -/
  indices : Finset (ZMod 19)
  /-- The moving residual complement is contained in the selected A-fiber
  union. -/
  moving_subset_aFiber :
    rotationOneMovingResidualPart h orbitBase.toCarrierWitness.toInput
        reflectedAvoidance.k ⊆
      coords.fiberUnion indices
  /-- The selected A-fiber union is contained in the moving residual
  complement. -/
  aFiber_subset_moving :
    coords.fiberUnion indices ⊆
      rotationOneMovingResidualPart h orbitBase.toCarrierWitness.toInput
        reflectedAvoidance.k
  /-- The concrete A-fiber-side filtered cardinality is `38` for every nonzero
  rotation step. -/
  aFiber_card_eq_thirtyEight :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      fixedAFiberAFiberCard h (coords.fiberUnion indices) d = 38

namespace D19FinalTraceHybridNoFixedBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Reinsert the proved fixed-count bound and recover the existing hybrid
trace boundary. -/
noncomputable def toD19FinalTraceRotationOneHybridBoundaryInputs
    (data : D19FinalTraceHybridNoFixedBoundaryInputs h) :
    D19FinalTraceRotationOneHybridBoundaryInputs.{u, uP} h where
  traceCore := data.traceCore
  rotationOneFixedCount_le_nineteen := by
    rw [h.rotation_one_fixedVertexCount_eq_one]
    norm_num
  orbitBase := data.orbitBase
  reflectedAvoidance := data.reflectedAvoidance
  coords := data.coords
  indices := data.indices
  moving_subset_aFiber := data.moving_subset_aFiber
  aFiber_subset_moving := data.aFiber_subset_moving
  aFiber_card_eq_thirtyEight := data.aFiber_card_eq_thirtyEight

/-- Forget the no-fixed-bound hybrid boundary down to the final input record.
-/
noncomputable def toD19FinalInputs
    (data : D19FinalTraceHybridNoFixedBoundaryInputs h) :
    D19FinalInputs h :=
  data.toD19FinalTraceRotationOneHybridBoundaryInputs.toD19FinalInputs

/-- Trace-core hybrid no-fixed-bound final inputs cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
      (D19FinalTraceHybridNoFixedBoundaryInputs.{u, uP} h) := by
  rintro ⟨data⟩
  exact D19FinalTraceRotationOneHybridBoundaryInputs.not_nonempty h
    ⟨data.toD19FinalTraceRotationOneHybridBoundaryInputs⟩

end D19FinalTraceHybridNoFixedBoundaryInputs

end Moore57

/-!
# No-fixed-bound final boundaries from residual containment

This file removes one more redundant boundary field from the no-fixed-bound
interfaces: for rotation-equivariant A-fiber coordinates, containment in the
reflection-copy residual implies containment in the rotation-one moving
residual.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19FinalCharacterAFiberNoFixedBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor from residual containment for rotation-equivariant A-fiber
coordinates.  Equivariance supplies the reverse A-fiber/moving-residual
inclusion. -/
noncomputable def of_equivariantAFiberResidual
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (indices : Finset (ZMod 19))
    (rot : AFiberRotationEquivariance h coords)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h orbitInput k ⊆
        coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆
        reflectionCopyResidual h orbitInput.base k)
    (aFiberCardinality : AFiberCardinality38Boundary h coords indices) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, uP} h where
  representation := representation
  orbitInput := orbitInput
  k := k
  reflection_not_mem_orbitFamilyUnion :=
    reflection_not_mem_orbitFamilyUnion
  coords := coords
  indices := indices
  moving_subset_aFiber := moving_subset_aFiber
  aFiber_subset_moving :=
    rot.fiberUnion_subset_movingResidual_of_subset_residual
      orbitInput k indices aFiber_subset_residual
  aFiberCardinality := aFiberCardinality

/-- Constructor where the orbit-base input is the one generated directly from
the rotation-equivariant A-fiber coordinates. -/
noncomputable def of_equivariantAFiberResidualFromCoordinates
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (rot : AFiberRotationEquivariance h coords)
    (k : ZMod 19)
    (indices : Finset (ZMod 19))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k)
            ((coords.toOrbitBaseSelectionInputOfMoore rot).base r) ∉
          (coords.toOrbitBaseSelectionInputOfMoore rot).orbitFamilyUnion)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h
          (coords.toOrbitBaseSelectionInputOfMoore rot) k ⊆
        coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆
        reflectionCopyResidual h
          (coords.toOrbitBaseSelectionInputOfMoore rot).base k)
    (aFiberCardinality : AFiberCardinality38Boundary h coords indices) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, uP} h :=
  of_equivariantAFiberResidual
    representation
    (coords.toOrbitBaseSelectionInputOfMoore rot)
    k reflection_not_mem_orbitFamilyUnion coords indices rot
    moving_subset_aFiber aFiber_subset_residual aFiberCardinality

end D19FinalCharacterAFiberNoFixedBoundaryInputs

namespace D19FinalTraceHybridNoFixedBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Constructor from residual containment for the canonical-carrier trace
hybrid boundary.  Equivariance supplies the reverse A-fiber/moving-residual
inclusion, and the cardinality package supplies the raw `38` statement. -/
noncomputable def of_residualContainment
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionCanonicalCarrierWitness h)
    (reflectedAvoidance :
      OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h orbitBase)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (indices : Finset (ZMod 19))
    (rot : AFiberRotationEquivariance h coords)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h orbitBase.toCarrierWitness.toInput
          reflectedAvoidance.k ⊆
        coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆
        reflectionCopyResidual h
          orbitBase.toCarrierWitness.toInput.base reflectedAvoidance.k)
    (aFiberCardinality : AFiberCardinality38Boundary h coords indices) :
    D19FinalTraceHybridNoFixedBoundaryInputs.{u, uP} h where
  traceCore := traceCore
  orbitBase := orbitBase
  reflectedAvoidance := reflectedAvoidance
  coords := coords
  indices := indices
  moving_subset_aFiber := moving_subset_aFiber
  aFiber_subset_moving :=
    rot.fiberUnion_subset_movingResidual_of_subset_residual
      orbitBase.toCarrierWitness.toInput reflectedAvoidance.k indices
      aFiber_subset_residual
  aFiber_card_eq_thirtyEight :=
    aFiberCardinality.card_eq_thirtyEight

/-- Constructor where the canonical carrier witness is generated directly from
the rotation-equivariant A-fiber coordinates. -/
noncomputable def of_residualContainmentFromCoordinates
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (rot : AFiberRotationEquivariance h coords)
    (reflectedAvoidance :
      OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h
        (coords.toCanonicalCarrierWitnessOfMoore rot))
    (indices : Finset (ZMod 19))
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h
          (coords.toCanonicalCarrierWitnessOfMoore rot).toCarrierWitness.toInput
          reflectedAvoidance.k ⊆
        coords.fiberUnion indices)
    (aFiber_subset_residual :
      coords.fiberUnion indices ⊆
        reflectionCopyResidual h
          (coords.toCanonicalCarrierWitnessOfMoore rot).toCarrierWitness.toInput.base
          reflectedAvoidance.k)
    (aFiberCardinality : AFiberCardinality38Boundary h coords indices) :
    D19FinalTraceHybridNoFixedBoundaryInputs.{u, uP} h :=
  of_residualContainment
    traceCore (coords.toCanonicalCarrierWitnessOfMoore rot)
    reflectedAvoidance coords indices rot moving_subset_aFiber
    aFiber_subset_residual aFiberCardinality

end D19FinalTraceHybridNoFixedBoundaryInputs

end Moore57

/-!
# No-fixed final boundaries for all A-fibers

This file specializes the residual-containment constructors to the common
case where the A-side part is `coords.allFibers`, i.e. `fiberUnion univ`.
-/

namespace Moore57

open Finset

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19FinalCharacterAFiberNoFixedBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Character/A-fiber no-fixed boundary specialized to all A-side fibers. -/
noncomputable def of_allFibersResidual
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (orbitInput : OrbitBaseSelectionInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (orbitInput.base r) ∉
          orbitInput.orbitFamilyUnion)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (rot : AFiberRotationEquivariance h coords)
    (moving_subset_allFibers :
      rotationOneMovingResidualPart h orbitInput k ⊆ coords.allFibers)
    (allFibers_subset_residual :
      coords.allFibers ⊆ reflectionCopyResidual h orbitInput.base k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h coords (Finset.univ : Finset (ZMod 19))) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, uP} h :=
  of_equivariantAFiberResidual representation orbitInput k
    reflection_not_mem_orbitFamilyUnion coords (Finset.univ : Finset (ZMod 19))
    rot (by simpa [AFiberCoordinates.allFibers] using moving_subset_allFibers)
    (by simpa [AFiberCoordinates.allFibers] using allFibers_subset_residual)
    aFiberCardinality

/-- Character/A-fiber no-fixed boundary specialized to all A-side fibers, with
the orbit-base input generated from the A-fiber coordinates. -/
noncomputable def of_allFibersResidualFromCoordinates
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (rot : AFiberRotationEquivariance h coords)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k)
            ((coords.toOrbitBaseSelectionInputOfMoore rot).base r) ∉
          (coords.toOrbitBaseSelectionInputOfMoore rot).orbitFamilyUnion)
    (moving_subset_allFibers :
      rotationOneMovingResidualPart h
          (coords.toOrbitBaseSelectionInputOfMoore rot) k ⊆
        coords.allFibers)
    (allFibers_subset_residual :
      coords.allFibers ⊆
        reflectionCopyResidual h
          (coords.toOrbitBaseSelectionInputOfMoore rot).base k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h coords (Finset.univ : Finset (ZMod 19))) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, uP} h :=
  of_equivariantAFiberResidualFromCoordinates representation coords rot k
    (Finset.univ : Finset (ZMod 19)) reflection_not_mem_orbitFamilyUnion
    (by simpa [AFiberCoordinates.allFibers] using moving_subset_allFibers)
    (by simpa [AFiberCoordinates.allFibers] using allFibers_subset_residual)
    aFiberCardinality

end D19FinalCharacterAFiberNoFixedBoundaryInputs

namespace D19FinalTraceHybridNoFixedBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Trace-hybrid no-fixed boundary specialized to all A-side fibers. -/
noncomputable def of_allFibersResidual
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (orbitBase : OrbitBaseSelectionCanonicalCarrierWitness h)
    (reflectedAvoidance :
      OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h orbitBase)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (rot : AFiberRotationEquivariance h coords)
    (moving_subset_allFibers :
      rotationOneMovingResidualPart h orbitBase.toCarrierWitness.toInput
          reflectedAvoidance.k ⊆
        coords.allFibers)
    (allFibers_subset_residual :
      coords.allFibers ⊆
        reflectionCopyResidual h
          orbitBase.toCarrierWitness.toInput.base reflectedAvoidance.k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h coords (Finset.univ : Finset (ZMod 19))) :
    D19FinalTraceHybridNoFixedBoundaryInputs.{u, uP} h :=
  of_residualContainment traceCore orbitBase reflectedAvoidance coords
    (Finset.univ : Finset (ZMod 19)) rot
    (by simpa [AFiberCoordinates.allFibers] using moving_subset_allFibers)
    (by simpa [AFiberCoordinates.allFibers] using allFibers_subset_residual)
    aFiberCardinality

/-- Trace-hybrid no-fixed boundary specialized to all A-side fibers, with the
canonical carrier generated from the A-fiber coordinates. -/
noncomputable def of_allFibersResidualFromCoordinates
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (coords : AFiberCoordinates.{u, uP} Γ)
    (rot : AFiberRotationEquivariance h coords)
    (reflectedAvoidance :
      OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h
        (coords.toCanonicalCarrierWitnessOfMoore rot))
    (moving_subset_allFibers :
      rotationOneMovingResidualPart h
          (coords.toCanonicalCarrierWitnessOfMoore rot).toCarrierWitness.toInput
          reflectedAvoidance.k ⊆
        coords.allFibers)
    (allFibers_subset_residual :
      coords.allFibers ⊆
        reflectionCopyResidual h
          (coords.toCanonicalCarrierWitnessOfMoore rot).toCarrierWitness.toInput.base
          reflectedAvoidance.k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h coords (Finset.univ : Finset (ZMod 19))) :
    D19FinalTraceHybridNoFixedBoundaryInputs.{u, uP} h :=
  of_residualContainmentFromCoordinates traceCore coords rot
    reflectedAvoidance (Finset.univ : Finset (ZMod 19))
    (by simpa [AFiberCoordinates.allFibers] using moving_subset_allFibers)
    (by simpa [AFiberCoordinates.allFibers] using allFibers_subset_residual)
    aFiberCardinality

end D19FinalTraceHybridNoFixedBoundaryInputs

end Moore57

