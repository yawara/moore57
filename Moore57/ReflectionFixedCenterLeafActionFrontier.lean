import Moore57.ReflectionFixedStarFromActionBoundary
import Moore57.BranchOrbitABCActionLevelFinalBoundary
import Moore57.BranchOrbitABCActionLevelLocalObstructionBoundary
import Moore57.BranchOrbitABCDoublingEquationSupportBoundary
import Moore57.InvolutionFixedStarA1

/-!
# Fixed-center-leaf action frontier

This file only adds thin connectors to the fixed-center-leaf boundary.  The
central observation is already in `ReflectionFixedStarBoundary`: a reflection
fixed-star package implies the fixed-center leaf package.  The definitions
below expose that projection directly from action-level packages whose
`starCounts` field already builds the fixed-star boundary.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace ReflectionFixedInducedStarDegrees

variable {h : D19ActsOnMoore57 V Γ}

/-- Degree-distribution fixed-star input directly yields the
fixed-center-leaf boundary. -/
def toReflectionFixedCenterLeafBoundary
    (input : ReflectionFixedInducedStarDegrees h) :
    ReflectionFixedCenterLeafBoundary h :=
  input.toReflectionFixedStarBoundary.toReflectionFixedCenterLeafBoundary

end ReflectionFixedInducedStarDegrees

namespace ReflectionFixedNeighborStarCounts

variable {h : D19ActsOnMoore57 V Γ}

/-- Action-level fixed-neighbor star counts directly yield the
fixed-center-leaf boundary. -/
def toReflectionFixedCenterLeafBoundary
    (input : ReflectionFixedNeighborStarCounts h) :
    ReflectionFixedCenterLeafBoundary h :=
  input.toReflectionFixedStarBoundary.toReflectionFixedCenterLeafBoundary

end ReflectionFixedNeighborStarCounts

/-- Convenience constructor from induced fixed-graph degree data to the
fixed-center-leaf boundary. -/
def reflectionFixedCenterLeafBoundary_of_fixedInduced_degrees
    {h : D19ActsOnMoore57 V Γ}
    (input : ReflectionFixedInducedStarDegrees h) :
    ReflectionFixedCenterLeafBoundary h :=
  input.toReflectionFixedCenterLeafBoundary

/-- Convenience constructor from action-level reflection fixed-neighbor counts
to the fixed-center-leaf boundary. -/
def reflectionFixedCenterLeafBoundary_of_reflectionFixedNeighbor_counts
    {h : D19ActsOnMoore57 V Γ}
    (input : ReflectionFixedNeighborStarCounts h) :
    ReflectionFixedCenterLeafBoundary h :=
  input.toReflectionFixedCenterLeafBoundary

namespace BranchOrbitABCActionLevelFinalBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget an action-level final package down to its fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelFinalBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelFinalBoundary

namespace BranchOrbitABCActionLevelCaseBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a case-level action package down to its fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelCaseBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelCaseBoundary

namespace BranchOrbitABCActionLevelLocalObstructionBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget an action-level local-obstruction package down to its
fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelLocalObstructionBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelLocalObstructionBoundary

namespace BranchOrbitABCActionLevelWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a witness-level action package down to its fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelWitnessBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelWitnessBoundary

namespace BranchOrbitABCActionLevelSetInvariantWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a set-invariant witness action package down to its
fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelSetInvariantWitnessBoundary

namespace BranchOrbitABCActionLevelCoordinateWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a coordinate witness action package down to its fixed-center-leaf
input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelCoordinateWitnessBoundary

namespace BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a reduced coordinate witness action package down to its
fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary

namespace BranchOrbitABCActionLevelCommonNeighborReducedBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a common-neighbor reduced action package down to its
fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelCommonNeighborReducedBoundary

namespace BranchOrbitABCActionLevelMinimalRemainingBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a minimal remaining action package down to its fixed-center-leaf
input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelMinimalRemainingBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelMinimalRemainingBoundary

namespace BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a refined minimal remaining action package down to its
fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary

namespace BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget a matching-equation refined action package down to its
fixed-center-leaf input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary

namespace BranchOrbitABCActionLevelDoublingEquationSupportBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget an equation/support action package down to its fixed-center-leaf
input. -/
def toReflectionFixedCenterLeafBoundary
    (boundary : BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    ReflectionFixedCenterLeafBoundary h :=
  boundary.starCounts.toReflectionFixedCenterLeafBoundary

end BranchOrbitABCActionLevelDoublingEquationSupportBoundary

namespace InvolutionK155

variable {σ : Equiv.Perm V}

/-- In an explicit `K_{1,55}` fixed-star package, any fixed vertex other than
the star center has at most one fixed neighbor. -/
theorem fixed_neighbor_count_le_one_of_fixed_ne_center
    (hK : InvolutionK155 Γ σ)
    {v : V}
    (hv_fixed : σ v = v)
    (hv_ne_center : v ≠ hK.center) :
    ((Γ.neighborFinset v).filter fun w => σ w = w).card ≤ 1 := by
  classical
  have hv_leaf : v ∈ hK.leaves := by
    rcases (hK.fixed_iff v).mp hv_fixed with hv_center | hv_leaf
    · exact (hv_ne_center hv_center).elim
    · exact hv_leaf
  have hsubset :
      ((Γ.neighborFinset v).filter fun w => σ w = w) ⊆ {hK.center} := by
    intro w hw
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw
    rcases (hK.fixed_iff w).mp hw.2 with hw_center | hw_leaf
    · simp [hw_center]
    · exact (hK.leaves_pairwise_not_adj hv_leaf hw_leaf hw.1).elim
  exact le_trans (Finset.card_le_card hsubset) (by simp)

end InvolutionK155

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- For one reflection, an explicit `K_{1,55}` fixed-star package whose center
is not `rotationFixedCenter` gives the fixed-center-neighbor count bound used
by the reflection-labeled branch argument. -/
theorem reflectionFixedNeighborFinset_card_le_one_of_involutionK155
    (k : ZMod 19)
    (hK : InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k)))
    (hcenter_ne : h.rotationFixedCenter ≠ hK.center) :
    (reflectionFixedNeighborFinset h k h.rotationFixedCenter).card ≤ 1 := by
  simpa [reflectionFixedNeighborFinset] using
    hK.fixed_neighbor_count_le_one_of_fixed_ne_center
      (by simpa using h.reflection_smul_rotationFixedCenter k)
      hcenter_ne

/-- Per-reflection explicit `K_{1,55}` fixed-star packages, with
`rotationFixedCenter` not the star center, yield the fixed-center-leaf
boundary. -/
def reflectionFixedCenterLeafBoundary_of_involutionK155
    (hK : ∀ k : ZMod 19,
      InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k)))
    (hcenter_ne : ∀ k : ZMod 19, h.rotationFixedCenter ≠ (hK k).center) :
    ReflectionFixedCenterLeafBoundary h where
  degree_le_one := by
    intro k
    change
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) ≤ 1
    have hdegree :=
      h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card
        (DihedralGroup.sr k) (reflectionRotationFixedCenterVertex h k)
    rw [hdegree]
    simpa [reflectionFixedNeighborFinset, reflectionRotationFixedCenterVertex] using
      h.reflectionFixedNeighborFinset_card_le_one_of_involutionK155
        k (hK k) (hcenter_ne k)

end D19ActsOnMoore57

end

end Moore57
