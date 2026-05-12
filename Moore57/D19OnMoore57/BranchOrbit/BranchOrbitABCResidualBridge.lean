import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCData
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCFinalBridge
import Moore57.D19OnMoore57.Rotation.RotationOneMovingResidualProperties
import Moore57.D19OnMoore57.AFiber.AFiberResidualSplitBridge

/-!
# Branch-orbit residual classification bridge

This file gives a thin semantic bridge for the branch-orbit A/B/C boundary:
instead of asking directly for the raw containment of the rotation-one moving
residual in the A-fiber side, it accepts the classification statement that
every non-fixed reflection-copy residual vertex lies in the A-fibers.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCData

variable {h : D19ActsOnMoore57 V Γ}

/-- Semantic residual classification implies the raw moving-residual
containment used by the no-fixed-boundary constructors. -/
theorem rotationOneMovingResidualPart_subset_allFibers_of_nonfixed_residual_subset
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers) :
    rotationOneMovingResidualPart h data.toOrbitBaseSelectionInput k ⊆
      data.toAFiberCoordinates.allFibers := by
  intro y hy
  have hymem := mem_rotationOneMovingResidualPart_iff.mp hy
  exact hnonfixed y hymem.1 hymem.2

/-- The same bridge, expressed with `indices = Finset.univ`, for APIs that are
written in terms of `fiberUnion`. -/
theorem rotationOneMovingResidualPart_subset_fiberUnion_univ_of_nonfixed_residual_subset
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers) :
    rotationOneMovingResidualPart h data.toOrbitBaseSelectionInput k ⊆
      data.toAFiberCoordinates.fiberUnion Finset.univ := by
  simpa [AFiberCoordinates.allFibers] using
    data.rotationOneMovingResidualPart_subset_allFibers_of_nonfixed_residual_subset
      k hnonfixed

/-- Build the direct-character no-fixed boundary from the semantic residual
classification, selecting all A-fibers. -/
def toCharacterAFiberNoFixedBoundaryInputsFromOrbitBaseResidualClassification
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
    (aFiber_subset_residual :
      data.toAFiberCoordinates.fiberUnion Finset.univ ⊆
        reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k)
    (aFiberCardinality :
      AFiberCardinality38Boundary h data.toAFiberCoordinates Finset.univ) :
    D19FinalCharacterAFiberNoFixedBoundaryInputs.{u, u} h :=
  data.toCharacterAFiberNoFixedBoundaryInputsFromOrbitBase
    representation k Finset.univ reflection_not_mem_orbitFamilyUnion
    (data.rotationOneMovingResidualPart_subset_fiberUnion_univ_of_nonfixed_residual_subset
      k hnonfixed)
    aFiber_subset_residual aFiberCardinality

/-- A split-equality helper for callers that also know all A-fibers are
residual. -/
theorem reflectionCopyResidual_eq_fixed_union_allFibers_of_nonfixed_residual_subset
    (data : BranchOrbitABCData h) (k : ZMod 19)
    (hnonfixed :
      ∀ y : V,
        y ∈ reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k →
          y ∉ fixedVertexSet (h.rotation 1) →
            y ∈ data.toAFiberCoordinates.allFibers)
    (hallFibers_subset_residual :
      data.toAFiberCoordinates.allFibers ⊆
        reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k) :
    reflectionCopyResidual h data.toOrbitBaseSelectionInput.base k =
      rotationOneFixedResidualPart h data.toOrbitBaseSelectionInput k ∪
        data.toAFiberCoordinates.allFibers := by
  simpa [AFiberCoordinates.allFibers] using
    (reflectionCopyResidual_eq_fixed_union_fiberUnion_of_nonfixed_residual_subset
      (h := h) (input := data.toOrbitBaseSelectionInput) (k := k)
      (coords := data.toAFiberCoordinates) (indices := Finset.univ)
      hnonfixed
      (by
        simpa [AFiberCoordinates.allFibers] using
          hallFibers_subset_residual))

end BranchOrbitABCData

end

end Moore57
