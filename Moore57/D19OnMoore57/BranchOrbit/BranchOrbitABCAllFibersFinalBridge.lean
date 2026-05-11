import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCResidualBridge
import Moore57.D19OnMoore57.AFiber.AFiberAllFibersCardinalityBoundary

/-!
# Branch-orbit all-fiber final-boundary bridge

This file combines the branch-orbit residual bridge with the all-A-fiber
matching-equation cardinality constructors.  It removes the separate
`AFiberCardinality38Boundary` argument from the branch final-boundary API in
the common `indices = univ` case.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCData

variable {h : D19ActsOnMoore57 V Γ}

local instance instBranchOrbitABCAllFibersFinalBridgePFintype
    (data : BranchOrbitABCData h) : Fintype data.toAFiberCoordinates.P :=
  data.toAFiberCoordinates.P_fintype

local instance instBranchOrbitABCAllFibersFinalBridgeDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- The all-A-fiber cardinality boundary obtained from fixed-coordinate counts
of the branch-built matching-rotation permutations. -/
noncomputable def toAllFibersCardinalityFromMatchingSupportTwo
    (data : BranchOrbitABCData h)
    (matchingSupportCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        (data.toAFiberRotationEquivariance.matchingRotationPerm d i hd).supportᶜ.card =
          2) :
    AFiberCardinality38Boundary h data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  AFiberCardinality38Boundary.of_allFibers_matchingRotationPerm_support_compl_card_eq_two
    data.toAFiberRotationEquivariance matchingSupportCardTwo

/-- The all-A-fiber cardinality boundary obtained from explicit
matching-equation solution counts in the branch-built coordinates. -/
noncomputable def toAllFibersCardinalityFromMatchingEquationTwo
    (data : BranchOrbitABCData h)
    (matchingEquationCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        ((Finset.univ : Finset data.toAFiberCoordinates.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore data.toAFiberCoordinates
              i (i + d) (index_ne_add_of_ne_zero hd) p =
            data.toAFiberRotationEquivariance.coordPerm d i p).card = 2) :
    AFiberCardinality38Boundary h data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  AFiberCardinality38Boundary.of_allFibers_matchingEquationFilterCard_eq_two
    data.toAFiberRotationEquivariance matchingEquationCardTwo

/-- Direct-character final-boundary package from branch data, semantic
residual classification, all-fiber residual containment, and local
matching-equation two-solution counts. -/
def toCharacterAFiberNoFixedBoundaryInputsFromOrbitBaseResidualClassificationMatchingEquationTwo
    (data : BranchOrbitABCData h)
    (representation : D19ActsOnMoore57.D19RepresentationCharacterInput h)
    (k : ZMod 19)
    (reflection_not_mem_orbitFamilyUnion :
      ∀ r : Fin 56,
        h.smul (DihedralGroup.sr k) (data.toOrbitBaseSelectionInput.base r) ∉
          data.toOrbitBaseSelectionInput.orbitFamilyUnion)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers)
    (allFibers_subset_residual :
      data.toAFiberCoordinates.allFibers ⊆
        reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k)
    (matchingEquationCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        ((Finset.univ : Finset data.toAFiberCoordinates.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore data.toAFiberCoordinates
              i (i + d) (index_ne_add_of_ne_zero hd) p =
            data.toAFiberRotationEquivariance.coordPerm d i p).card = 2) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, u} h :=
  data.toCharacterAFiberNoFixedBoundaryInputsFromOrbitBaseResidualClassification
    representation k reflection_not_mem_orbitFamilyUnion hnonfixed
    (by
      simpa [AFiberCoordinates.allFibers] using allFibers_subset_residual)
    (data.toAllFibersCardinalityFromMatchingEquationTwo
      matchingEquationCardTwo)

/-- Trace-hybrid final-boundary package from branch data, semantic residual
classification for the canonical carrier input, all-fiber residual
containment, and local matching-equation two-solution counts. -/
def toTraceHybridNoFixedBoundaryInputsFromOrbitBaseResidualClassificationMatchingEquationTwo
    (data : BranchOrbitABCData h)
    (traceCore : TraceCharacterCoreData Γ h.rotation h.a1)
    (reflectedAvoidance :
      OrbitBaseSelectionCanonicalCarrierReflectedAvoidance h
        data.toCanonicalCarrierWitnessFromOrbitBase)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toCanonicalCarrierInputFromOrbitBase.base
            reflectedAvoidance.k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers)
    (allFibers_subset_residual :
      data.toAFiberCoordinates.allFibers ⊆
        reflectionCopyResidual h data.toCanonicalCarrierInputFromOrbitBase.base
          reflectedAvoidance.k)
    (matchingEquationCardTwo :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        ((Finset.univ : Finset data.toAFiberCoordinates.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore data.toAFiberCoordinates
              i (i + d) (index_ne_add_of_ne_zero hd) p =
            data.toAFiberRotationEquivariance.coordPerm d i p).card = 2) :
    D19FinalTraceHybridNoFixedBoundaryInputs.{u, u} h :=
  data.toTraceHybridNoFixedBoundaryInputsFromOrbitBase
    traceCore reflectedAvoidance (Finset.univ : Finset (ZMod 19))
    (by
      intro y hy
      have hymem := mem_rotationOneMovingResidualPart_iff.mp hy
      exact hnonfixed y hymem.1 hymem.2)
    (by
      simpa [AFiberCoordinates.allFibers] using allFibers_subset_residual)
    (data.toAllFibersCardinalityFromMatchingEquationTwo
      matchingEquationCardTwo)

end BranchOrbitABCData

end

end Moore57
