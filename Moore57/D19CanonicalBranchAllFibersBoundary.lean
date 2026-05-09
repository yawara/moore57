import Moore57.BranchOrbitABCAllFibersFinalBridge
import Moore57.BranchOrbitABCDataFromCenter
import Moore57.D19RepresentationCharacterDataBridge

/-!
# Canonical branch all-fiber final boundary

This file packages the current canonical branch/all-fiber frontier.  The
branch data is constructed from the fixed-center neighbor orbits, with the
selected `Fin 56` orbit bases chosen from `L_{b0}` as in the natural-language
proof.  The remaining fields expose the representation-character boundary,
the B/C reflection-copy geometry, the residual split, and the A-fiber matching
cardinality.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- The canonical branch-orbit boundary data obtained from the fixed rotation
center and its three rotation-orbit neighbor classes. -/
noncomputable def canonicalBranchABCData
    (h : D19ActsOnMoore57 V Γ) :
    BranchOrbitABCData h :=
  BranchOrbitABCData.ofRotationFixedCenterNeighborOrbits h

end D19ActsOnMoore57

local instance instD19CanonicalBranchAllFibersBoundaryPFintype
    (h : D19ActsOnMoore57 V Γ) :
    Fintype h.canonicalBranchABCData.toAFiberCoordinates.P :=
  h.canonicalBranchABCData.toAFiberCoordinates.P_fintype

local instance instD19CanonicalBranchAllFibersBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Current top-level boundary package for the canonical branch/all-A-fiber
route with selected bases coming from `L_{b0}`. -/
structure D19CanonicalBranchAllFibersBoundaryInputs
    (h : D19ActsOnMoore57 V Γ) where
  /-- Representation-character data, exposed as arithmetic components and the
  nontrivial-rotation character identity. -/
  representationComponents :
    D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h
  /-- Reflected-copy parameter. -/
  k : ZMod 19
  /-- Reflected selected bases avoid the selected orbit-family union. -/
  reflection_not_mem_orbitFamilyUnion :
    ∀ r : Fin 56,
      h.smul (DihedralGroup.sr k)
          (h.canonicalBranchABCData.toOrbitBaseSelectionInput.base r) ∉
        h.canonicalBranchABCData.toOrbitBaseSelectionInput.orbitFamilyUnion
  /-- Every non-fixed residual vertex lies in the all-A-fiber side. -/
  nonfixed_residual_subset_allFibers :
    ∀ y : V,
      y ∈ reflectionCopyResidual h
          h.canonicalBranchABCData.toOrbitBaseSelectionInput.base k →
        y ∉ fixedVertexSet (h.rotation 1) →
          y ∈ h.canonicalBranchABCData.toAFiberCoordinates.allFibers
  /-- The all-A-fiber side is residual. -/
  allFibers_subset_residual :
    h.canonicalBranchABCData.toAFiberCoordinates.allFibers ⊆
      reflectionCopyResidual h
        h.canonicalBranchABCData.toOrbitBaseSelectionInput.base k
  /-- Each explicit matching equation on the all-A-fiber coordinate system has
  exactly two solutions. -/
  matchingEquationCardTwo :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
      ((Finset.univ :
          Finset h.canonicalBranchABCData.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            h.canonicalBranchABCData.toAFiberCoordinates
            i (i + d) (index_ne_add_of_ne_zero hd) p =
          h.canonicalBranchABCData.toAFiberRotationEquivariance.coordPerm d i p).card =
        2

namespace D19CanonicalBranchAllFibersBoundaryInputs

variable {h : D19ActsOnMoore57 V Γ}

/-- Convert the current canonical branch/all-fiber boundary package to the
already refuted no-fixed final-boundary interface. -/
noncomputable def toCharacterAFiberNoFixedBoundaryInputs
    (data : D19CanonicalBranchAllFibersBoundaryInputs h) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, u} h := by
  let representation :
      D19ActsOnMoore57.D19RepresentationCharacterInput h :=
    Classical.choice
      ((D19ActsOnMoore57.D19RepresentationCharacterInput.nonempty_iff_componentsBoundary
        h).mpr
          data.representationComponents)
  exact
    h.canonicalBranchABCData
      |>.toCharacterAFiberNoFixedBoundaryInputsFromOrbitBaseResidualClassificationMatchingEquationTwo
        representation data.k data.reflection_not_mem_orbitFamilyUnion
        data.nonfixed_residual_subset_allFibers
        data.allFibers_subset_residual
        data.matchingEquationCardTwo

/-- The current canonical branch/all-fiber boundary package cannot exist. -/
theorem not_nonempty (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19CanonicalBranchAllFibersBoundaryInputs h) := by
  rintro ⟨data⟩
  exact D19FinalCharacterAFiberNoFixedBoundaryInputs.not_nonempty h
    ⟨data.toCharacterAFiberNoFixedBoundaryInputs⟩

end D19CanonicalBranchAllFibersBoundaryInputs

/-- Public alias for the canonical branch/all-fiber top-level boundary. -/
theorem no_D19_canonical_branch_allFibers_boundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (D19CanonicalBranchAllFibersBoundaryInputs h) :=
  D19CanonicalBranchAllFibersBoundaryInputs.not_nonempty h

end

end Moore57
