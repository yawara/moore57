import Moore57.D19OnMoore57.BranchOrbit.ABCAllOffsetsClosedFrontier

/-!
# More all-offset closed frontier aliases

This file records the shared non-representation closure core for the visible
final-gap wrappers that carry an A-fixing support-card input, a midpoint
criterion, and a report-level support-subset exception.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAllOffsetsMoreClosedFrontierPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instAllOffsetsMoreClosedFrontierDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- The common all-offset contradiction core carried by the current
final-gap wrappers, with no representation component. -/
structure BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary
    (h : D19ActsOnMoore57 V Γ) where
  starCounts : ReflectionFixedNeighborStarCounts h
  labeling : BranchOrbitABCReflectionLabeling h
  aFixing :
    BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
      starCounts.toReflectionFixedStarBoundary labeling
  midpointCriterion :
    BranchOrbitABCReflectionLabeling.MidpointReflectionCriterionBoundary
      labeling
  supportSubsetException :
    BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling

namespace BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The common core is inconsistent by the all-offset common-neighbor
obstruction. -/
theorem false_of_allOffsetsCommonNeighbor
    (boundary : BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary h) : False :=
  _root_.Moore57.BranchOrbitABCReflectionLabeling.false_of_aFixing_supportSubset_allOffsetsCommonNeighbor
      boundary.aFixing
      boundary.midpointCriterion
      boundary.supportSubsetException

end BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary

/-- No standalone support-subset core exists after the all-offset
common-neighbor obstruction. -/
theorem not_allOffsetsSupportSubsetCoreBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary h) := by
  rintro ⟨boundary⟩
  exact boundary.false_of_allOffsetsCommonNeighbor

namespace BranchOrbitABCActionLevelDoublingEquationSupportBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- The older action-level equation/support package contains the same
support-subset core, with the midpoint criterion stored in `referenceMatching`. -/
def toAllOffsetsSupportSubsetCoreBoundary
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :
    BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  aFixing := boundary.aFixing
  midpointCriterion := boundary.referenceMatching.criterion
  supportSubsetException := boundary.toSupportSubsetExceptionIssueBoundary

/-- Core-only proof of the all-offset closure for the action-level
equation/support package. -/
theorem false_of_allOffsetsSupportSubsetCore
    (boundary :
      BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) : False :=
  boundary.toAllOffsetsSupportSubsetCoreBoundary
    |>.false_of_allOffsetsCommonNeighbor

end BranchOrbitABCActionLevelDoublingEquationSupportBoundary

namespace BranchOrbitABCCurrentFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the current final-gap report to its shared all-offset
support-subset core. -/
def toAllOffsetsSupportSubsetCoreBoundary
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) :
    BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  aFixing := boundary.aFixing
  midpointCriterion := boundary.doublingReflectedEquation.midpointCriterion
  supportSubsetException := boundary.supportSubsetException

/-- Core-only spelling of the current final-gap all-offset contradiction. -/
theorem false_of_allOffsetsSupportSubsetCore
    (boundary : BranchOrbitABCCurrentFinalGapBoundary h) : False :=
  boundary.toAllOffsetsSupportSubsetCoreBoundary
    |>.false_of_allOffsetsCommonNeighbor

end BranchOrbitABCCurrentFinalGapBoundary

namespace BranchOrbitABCEndpointPairedFinalGapBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the endpoint-paired final-gap report to its shared all-offset
support-subset core; the paired endpoint field is not used. -/
def toAllOffsetsSupportSubsetCoreBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h) :
    BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  aFixing := boundary.aFixing
  midpointCriterion := boundary.doublingReflectedEquation.midpointCriterion
  supportSubsetException := boundary.supportSubsetException

/-- The support-subset field forces all-offset endpoint adjacency on the
A-fixing support. -/
def allOffsetsEndpointAdj
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h) :=
  boundary.labeling.all_offsets_endpoint_adj_of_support_subset_midpointExceptionSet
    boundary.doublingReflectedEquation.midpointCriterion
    boundary.supportSubsetException.support_subset_exception

/-- The A-fixing two-point support gives the all-offset common-neighbor
obstruction for the paired final-gap report. -/
def allOffsetsCommonNeighborObstruction
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
      boundary.labeling :=
  boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary
    |>.toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    |>.toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary

/-- Direct endpoint-adjacency spelling of the paired final-gap all-offset
contradiction. -/
theorem false_of_allOffsetsEndpointAdj
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h) : False :=
  boundary.allOffsetsCommonNeighborObstruction
    |>.not_all_offsets_support_endpoint_adj
      boundary.allOffsetsEndpointAdj

/-- Core-only spelling of the paired final-gap all-offset contradiction. -/
theorem false_of_allOffsetsSupportSubsetCore
    (boundary : BranchOrbitABCEndpointPairedFinalGapBoundary h) : False :=
  boundary.toAllOffsetsSupportSubsetCoreBoundary
    |>.false_of_allOffsetsCommonNeighbor

end BranchOrbitABCEndpointPairedFinalGapBoundary

namespace BranchOrbitABCEndpointPairedFinalBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the endpoint-paired final package to the shared all-offset core
carried by its nested final-gap report. -/
def toAllOffsetsSupportSubsetCoreBoundary
    (boundary : BranchOrbitABCEndpointPairedFinalBoundary h) :
    BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary h :=
  boundary.pairedFinalGap.toAllOffsetsSupportSubsetCoreBoundary

/-- Core-only spelling of the endpoint-paired final package contradiction. -/
theorem false_of_allOffsetsSupportSubsetCore
    (boundary : BranchOrbitABCEndpointPairedFinalBoundary h) : False :=
  boundary.toAllOffsetsSupportSubsetCoreBoundary
    |>.false_of_allOffsetsCommonNeighbor

end BranchOrbitABCEndpointPairedFinalBoundary

namespace BranchOrbitABCEndpointObstructionFinalBoundary

variable {h : D19ActsOnMoore57 V Γ}

/-- Forget the endpoint-obstruction final report to its shared all-offset
support-subset core; the endpoint obstruction fields are not used. -/
def toAllOffsetsSupportSubsetCoreBoundary
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) :
    BranchOrbitABCAllOffsetsSupportSubsetCoreBoundary h where
  starCounts := boundary.starCounts
  labeling := boundary.labeling
  aFixing := boundary.aFixing
  midpointCriterion := boundary.doublingReflectedEquation.midpointCriterion
  supportSubsetException := boundary.supportSubsetException

/-- The support-subset field forces all-offset endpoint adjacency on the
A-fixing support. -/
def allOffsetsEndpointAdj
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  boundary.labeling.all_offsets_endpoint_adj_of_support_subset_midpointExceptionSet
    boundary.doublingReflectedEquation.midpointCriterion
    boundary.supportSubsetException.support_subset_exception

/-- The A-fixing two-point support gives the all-offset common-neighbor
obstruction for the endpoint-obstruction final report. -/
def allOffsetsCommonNeighborObstruction
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) :
    BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
      boundary.labeling :=
  boundary.aFixing.toAFixingReflectionFixedNeighborCardBoundary
    |>.toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    |>.toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary

/-- Direct endpoint-adjacency spelling of the endpoint-obstruction final
all-offset contradiction. -/
theorem false_of_allOffsetsEndpointAdj
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) : False :=
  boundary.allOffsetsCommonNeighborObstruction
    |>.not_all_offsets_support_endpoint_adj
      boundary.allOffsetsEndpointAdj

/-- Core-only spelling of the endpoint-obstruction final all-offset
contradiction. -/
theorem false_of_allOffsetsSupportSubsetCore
    (boundary : BranchOrbitABCEndpointObstructionFinalBoundary h) : False :=
  boundary.toAllOffsetsSupportSubsetCoreBoundary
    |>.false_of_allOffsetsCommonNeighbor

end BranchOrbitABCEndpointObstructionFinalBoundary

/-- Diagnostic inventory: all currently visible non-representation
action/report/final packages carrying the shared all-offset support-subset
core are closed. -/
theorem allOffsetsSupportSubsetCore_closed_visibleFrontier
    (h : D19ActsOnMoore57 V Γ) :
    (¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h)) ∧
    (¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h)) ∧
    (¬ Nonempty (BranchOrbitABCEndpointPairedFinalGapBoundary h)) ∧
    (¬ Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h)) ∧
    (¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h)) := by
  exact
    ⟨fun hboundary =>
        not_allOffsetsSupportSubsetCoreBoundary h
          (hboundary.map
            BranchOrbitABCActionLevelDoublingEquationSupportBoundary.toAllOffsetsSupportSubsetCoreBoundary),
      fun hboundary =>
        not_allOffsetsSupportSubsetCoreBoundary h
          (hboundary.map
            BranchOrbitABCCurrentFinalGapBoundary.toAllOffsetsSupportSubsetCoreBoundary),
      fun hboundary =>
        not_allOffsetsSupportSubsetCoreBoundary h
          (hboundary.map
            BranchOrbitABCEndpointPairedFinalGapBoundary.toAllOffsetsSupportSubsetCoreBoundary),
      fun hboundary =>
        not_allOffsetsSupportSubsetCoreBoundary h
          (hboundary.map
            BranchOrbitABCEndpointPairedFinalBoundary.toAllOffsetsSupportSubsetCoreBoundary),
      fun hboundary =>
        not_allOffsetsSupportSubsetCoreBoundary h
          (hboundary.map
            BranchOrbitABCEndpointObstructionFinalBoundary.toAllOffsetsSupportSubsetCoreBoundary)⟩

end

end Moore57
