import Moore57.D19OnMoore57.BranchOrbit.ABCFinalGapReportBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCCardTwoAllOffsetsCommonNeighborBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportSubsetAllOffsetsEndpointBoundary

/-!
# Final-gap contradiction from all-offset common neighbors

This file records the report-level contradiction using the corrected card-two
input: all-offset endpoint adjacency on the two-point A-fixing support yields
two distinct common neighbors of a non-adjacent endpoint pair.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFinalGapAllOffsetsContradictionPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFinalGapAllOffsetsContradictionDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCCurrentFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The report-level support-subset exception, together with the midpoint
criterion, gives endpoint adjacency for every nonzero endpoint offset on the
A-fixing support. -/
def allOffsetsEndpointAdj
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : boundary.labeling.data.toAFiberCoordinates.P,
        p ∈ boundary.labeling.aFiberReflectionSupport →
          Γ.Adj
            (((boundary.labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ boundary.labeling.data.toAFiberCoordinates.u
                  (boundary.labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((boundary.labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (boundary.labeling.midpointReflectionCoordPerm
                  (midpointOf d) p) :
              {x : V // x ∈
                branchFiber Γ boundary.labeling.data.toAFiberCoordinates.u
                  (boundary.labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V)) :=
  boundary.labeling.all_offsets_endpoint_adj_of_support_subset_midpointExceptionSet
    boundary.doublingReflectedEquation.midpointCriterion
    boundary.supportSubsetException.support_subset_exception

/-- The A-fixing card-two support boundary gives the corrected all-offset
common-neighbor obstruction. -/
def allOffsetsCommonNeighborObstruction
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
      boundary.labeling :=
  boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary
    |>.toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    |>.toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary

/-- A current final-gap report is inconsistent by the all-offset
common-neighbor obstruction, without using the older pointwise endpoint
obstruction. -/
theorem false_of_supportSubset_allOffsetsCommonNeighbor
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) : False :=
  boundary.allOffsetsCommonNeighborObstruction
    |>.not_all_offsets_support_endpoint_adj
      boundary.allOffsetsEndpointAdj

end BranchOrbitABCCurrentFinalGapBoundary

/-- No current final-gap report exists by the all-offset common-neighbor
obstruction. -/
theorem not_currentFinalGapBoundary_allOffsetsCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) := by
  rintro ⟨boundary⟩
  exact boundary.false_of_supportSubset_allOffsetsCommonNeighbor

end

end Moore57
