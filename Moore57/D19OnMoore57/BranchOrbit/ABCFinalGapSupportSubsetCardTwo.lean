import Moore57.D19OnMoore57.BranchOrbit.ABCFinalGapReportBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportSubsetCardTwoBoundary

/-!
# Final-gap support subset as the card-two branch

This file connects the current final-gap report's `supportSubsetException`
field with the finite-set card-two branch used by the midpoint-exception case
analysis.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instFinalGapSupportSubsetCardTwoPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instFinalGapSupportSubsetCardTwoDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCSupportSubsetExceptionIssueBoundary

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Forget the report-level all-support field to the natural card-two branch
shape indexed by endpoint offsets. -/
def toMidpointExceptionAFixingSupportAllSubsetBoundary
    (boundary :
      BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportAllSubsetBoundary
      labeling where
  all_support_subset_exception := by
    intro d hd
    exact boundary.support_subset_exception
      (midpointOf d) (midpointOf_ne_zero hd)

/-- The report-level all-support field forces the corresponding midpoint
exception/support intersection to have cardinality two. -/
theorem midpointExceptionAFixingSupportIntersection_card_two
    (boundary :
      BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling)
    (supportCard :
      BranchOrbitABCReflectionLabeling.AFixingReflectionFixedNeighborCardBoundary
        labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card = 2 :=
  boundary.toMidpointExceptionAFixingSupportAllSubsetBoundary
    |>.intersection_card_two supportCard d hd

end BranchOrbitABCSupportSubsetExceptionIssueBoundary

namespace BranchOrbitABCCurrentFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- In the current final-gap report, `supportSubsetException` is the positive
card-two midpoint-exception/support case. -/
theorem supportSubset_intersection_card_two
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h)
    (d : ZMod 19) (hd : d ≠ 0) :
    (boundary.labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card = 2 :=
  boundary.supportSubsetException
    |>.midpointExceptionAFixingSupportIntersection_card_two
      boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary d hd

end BranchOrbitABCCurrentFinalGapBoundary

end

end Moore57
