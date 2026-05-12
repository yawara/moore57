import Moore57.D19OnMoore57.BranchOrbit.ABCCardTwoAllOffsetsCommonNeighborBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCCardTwoAllOffsetsNoCardBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportSubsetAllOffsetsEndpointBoundary

/-!
# Final-gap connector for the card-two all-offset obstruction

This file wires the all-offset card-two common-neighbor obstruction into the
final-gap support-subset boundary shape.  The support-card hypothesis gives the
all-offset two-common-neighbor contradiction; the midpoint-reflection criterion
then converts support containment in midpoint exception sets into endpoint
adjacency, ruling out the all-offset support-subset branch.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Repackage the common-neighbor all-offset endpoint obstruction in the
global no-endpoint-adjacency shape used by the final-gap support-subset API. -/
def toNoAllOffsetsEndpointAdj
    (boundary :
      MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
        labeling) :
    NoAllOffsetsEndpointAdj labeling where
  not_all_offsets_endpoint_adj :=
    boundary.not_all_offsets_support_endpoint_adj

/-- The all-offset endpoint obstruction gives the final-gap no-support-subset
boundary once the midpoint-reflection criterion is available. -/
def toNoAllOffsetsSupportSubsetBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
        labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    NoAllOffsetsSupportSubsetBoundary labeling :=
  boundary.toNoAllOffsetsEndpointAdj
    |>.toNoAllOffsetsSupportSubsetBoundary criterion

/-- Direct report-level form: the all-offset endpoint obstruction rules out
the support-subset exception issue under the midpoint-reflection criterion. -/
theorem not_supportSubsetExceptionIssueBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
        labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling := by
  intro supportSubset
  exact
    boundary.not_all_offsets_support_endpoint_adj
      (all_offsets_endpoint_adj_of_support_subset_midpointExceptionSet
        labeling criterion supportSubset.support_subset_exception)

end MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary

namespace MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The all-offset two-common-neighbor obstruction gives the final-gap
no-endpoint-adjacency shape. -/
def toNoAllOffsetsEndpointAdj
    (boundary :
      MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
        labeling) :
    NoAllOffsetsEndpointAdj labeling :=
  boundary.toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
    |>.toNoAllOffsetsEndpointAdj

/-- The all-offset two-common-neighbor obstruction gives the final-gap
no-support-subset boundary under the midpoint-reflection criterion. -/
def toNoAllOffsetsSupportSubsetBoundary
    (boundary :
      MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
        labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    NoAllOffsetsSupportSubsetBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
    |>.toNoAllOffsetsSupportSubsetBoundary criterion

/-- Direct report-level form from the all-offset two-common-neighbor
obstruction. -/
theorem not_supportSubsetExceptionIssueBoundary
    (boundary :
      MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
        labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
    |>.not_supportSubsetExceptionIssueBoundary criterion

end MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- A two-point A-fixing support supplies the all-offset endpoint obstruction
needed by the final-gap support-subset API. -/
def toNoAllOffsetsEndpointAdj
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    NoAllOffsetsEndpointAdj labeling :=
  supportCard.toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    |>.toNoAllOffsetsEndpointAdj

/-- Main connector: from the support-card boundary and midpoint-reflection
criterion, produce the global final-gap no-support-subset boundary. -/
def toNoAllOffsetsSupportSubsetBoundary
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    NoAllOffsetsSupportSubsetBoundary labeling :=
  supportCard.toNoAllOffsetsEndpointAdj
    |>.toNoAllOffsetsSupportSubsetBoundary criterion

/-- Direct final-gap report-level contradiction from the support-card boundary
and midpoint-reflection criterion. -/
theorem not_supportSubsetExceptionIssueBoundary
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling :=
  supportCard.toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    |>.not_supportSubsetExceptionIssueBoundary criterion

end AFixingReflectionFixedNeighborCardBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
