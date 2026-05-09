import Moore57.D19FinalNoFixedResidualContainmentBoundary

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
