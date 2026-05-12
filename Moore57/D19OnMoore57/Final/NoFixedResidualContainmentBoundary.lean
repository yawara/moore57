import Moore57.D19OnMoore57.Final.NoFixedBoundBoundary
import Moore57.D19OnMoore57.AFiber.OrbitBaseSelection
import Moore57.D19OnMoore57.AFiber.OrbitMovingResidual

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
