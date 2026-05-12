import Moore57.D19OnMoore57.BranchOrbit.ABCData
import Moore57.D19OnMoore57.AFiber.OrbitBaseSelection
import Moore57.D19OnMoore57.Final.NoFixedResidualContainmentBoundary

/-!
# Branch-orbit A/B/C data to no-fixed final boundaries

This file is a thin bridge from the high-level branch-orbit boundary data to
the no-fixed residual-containment final-boundary interfaces.  It only packages
existing constructors: the A-side coordinate system comes from
`BranchOrbitABCData.toAFiberCoordinates`, and the selected moved rotation
orbits are either the ones stored in the branch data or the canonical selection
generated from the coordinates.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCData

variable {h : D19ActsOnMoore57 V Γ}

/-- The A-fiber coordinates constructed from branch-orbit data are rotation
equivariant. -/
theorem toAFiberRotationEquivariance
    (data : BranchOrbitABCData h) :
    AFiberRotationEquivariance h data.toAFiberCoordinates :=
  AFiberCoordinates.ofRotationOrbitOfMoved_rotationEquivariance
    h data.u data.a0 data.u_fixed data.a0_adj
    data.a0_move_step_ne_zero data.a0_moved

/-- Promote the stored orbit-base selection to the canonical-carrier witness
used by the trace-hybrid boundary. -/
def toCanonicalCarrierWitnessFromOrbitBase
    (data : BranchOrbitABCData h) :
    OrbitBaseSelectionCanonicalCarrierWitness h :=
  data.toOrbitBaseSelectionInput.toCanonicalCarrierWitness

/-- The downstream input obtained from the stored orbit-base selection after
passing through the canonical-carrier API. -/
def toCanonicalCarrierInputFromOrbitBase
    (data : BranchOrbitABCData h) :
    OrbitBaseSelectionInput h :=
  data.toCanonicalCarrierWitnessFromOrbitBase.toCarrierWitness.toInput

/-- Build the direct-character no-fixed boundary using the orbit-base
selection already stored in the branch-orbit data. -/
def toCharacterAFiberNoFixedBoundaryInputsFromOrbitBase
    (data : BranchOrbitABCData h)
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (k : ZMod 19)
    (indices : Finset (ZMod 19))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (data.toOrbitBaseSelectionInput.base r) ∉
          data.toOrbitBaseSelectionInput.orbitFamilyUnion)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h data.toOrbitBaseSelectionInput k ⊆
        data.toAFiberCoordinates.fiberUnion indices)
    (aFiber_subset_residual :
      data.toAFiberCoordinates.fiberUnion indices ⊆
        reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h data.toAFiberCoordinates indices) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, u} h :=
  D19FinalCharacterAFiberNoFixedBoundaryInputs.of_equivariantAFiberResidual
    representation data.toOrbitBaseSelectionInput k
    reflection_not_mem_orbitFamilyUnion data.toAFiberCoordinates indices
    data.toAFiberRotationEquivariance moving_subset_aFiber
    aFiber_subset_residual aFiberCardinality

/-- Build the direct-character no-fixed boundary using the orbit-base
selection generated canonically from the branch-built A-fiber coordinates. -/
def toCharacterAFiberNoFixedBoundaryInputsFromCoordinates
    (data : BranchOrbitABCData h)
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (k : ZMod 19)
    (indices : Finset (ZMod 19))
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k)
            ((data.toAFiberCoordinates.toOrbitBaseSelectionInputOfMoore
              data.toAFiberRotationEquivariance).base r) ∉
          (data.toAFiberCoordinates.toOrbitBaseSelectionInputOfMoore
            data.toAFiberRotationEquivariance).orbitFamilyUnion)
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h
          (data.toAFiberCoordinates.toOrbitBaseSelectionInputOfMoore
            data.toAFiberRotationEquivariance) k ⊆
        data.toAFiberCoordinates.fiberUnion indices)
    (aFiber_subset_residual :
      data.toAFiberCoordinates.fiberUnion indices ⊆
        reflectionCopyResidual h
          (data.toAFiberCoordinates.toOrbitBaseSelectionInputOfMoore
            data.toAFiberRotationEquivariance).base k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h data.toAFiberCoordinates indices) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, u} h :=
  D19FinalCharacterAFiberNoFixedBoundaryInputs.of_equivariantAFiberResidualFromCoordinates
    representation data.toAFiberCoordinates data.toAFiberRotationEquivariance
    k indices reflection_not_mem_orbitFamilyUnion moving_subset_aFiber
    aFiber_subset_residual aFiberCardinality

/-- Build the trace-hybrid no-fixed boundary using the orbit-base selection
already stored in the branch-orbit data. -/
def toTraceHybridNoFixedBoundaryInputsFromOrbitBase
    (data : BranchOrbitABCData h)
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (reflectedAvoidance :
      OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h
        data.toCanonicalCarrierWitnessFromOrbitBase)
    (indices : Finset (ZMod 19))
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h data.toCanonicalCarrierInputFromOrbitBase
          reflectedAvoidance.k ⊆
        data.toAFiberCoordinates.fiberUnion indices)
    (aFiber_subset_residual :
      data.toAFiberCoordinates.fiberUnion indices ⊆
        reflectionCopyResidual h data.toCanonicalCarrierInputFromOrbitBase.base
          reflectedAvoidance.k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h data.toAFiberCoordinates indices) :
    D19FinalTraceHybridNoFixedBoundaryInputs.{u, u} h :=
  D19FinalTraceHybridNoFixedBoundaryInputs.of_residualContainment
    traceCore data.toCanonicalCarrierWitnessFromOrbitBase
    reflectedAvoidance data.toAFiberCoordinates indices
    data.toAFiberRotationEquivariance moving_subset_aFiber
    aFiber_subset_residual aFiberCardinality

/-- Build the trace-hybrid no-fixed boundary using the canonical carrier
generated from the branch-built A-fiber coordinates. -/
def toTraceHybridNoFixedBoundaryInputsFromCoordinates
    (data : BranchOrbitABCData h)
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (reflectedAvoidance :
      OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h
        (data.toAFiberCoordinates.toCanonicalCarrierWitnessOfMoore
          data.toAFiberRotationEquivariance))
    (indices : Finset (ZMod 19))
    (moving_subset_aFiber :
      rotationOneMovingResidualPart h
          (data.toAFiberCoordinates.toCanonicalCarrierWitnessOfMoore
            data.toAFiberRotationEquivariance).toCarrierWitness.toInput
          reflectedAvoidance.k ⊆
        data.toAFiberCoordinates.fiberUnion indices)
    (aFiber_subset_residual :
      data.toAFiberCoordinates.fiberUnion indices ⊆
        reflectionCopyResidual h
          (data.toAFiberCoordinates.toCanonicalCarrierWitnessOfMoore
            data.toAFiberRotationEquivariance).toCarrierWitness.toInput.base
          reflectedAvoidance.k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h data.toAFiberCoordinates indices) :
    D19FinalTraceHybridNoFixedBoundaryInputs.{u, u} h :=
  D19FinalTraceHybridNoFixedBoundaryInputs.of_residualContainmentFromCoordinates
    traceCore data.toAFiberCoordinates data.toAFiberRotationEquivariance
    reflectedAvoidance indices moving_subset_aFiber aFiber_subset_residual
    aFiberCardinality

end BranchOrbitABCData

end

end Moore57
