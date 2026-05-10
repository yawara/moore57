import Moore57.BranchOrbitABCCardTwoAllOffsetsFinalGapBoundary
import Moore57.BranchOrbitABCCardTwoOffsetGapDiagnostic

/-!
# Card-two single-offset compatibility

The weak single-offset boundary
`MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary` is kept as
an old compatibility shape.  The card-two common-neighbor construction uses
endpoint equations at several offsets, so the intended replacement is the
all-offset boundary
`MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary`.

This file exposes only safe compatibility conversions from the all-offset
boundary to global no-all/no-card forms.  It intentionally does not construct
the older per-offset
`MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary` or
`MidpointExceptionAFixingSupportNoCardTwoBoundary`: the all-offset obstruction
proves that not all nonzero offsets can hold simultaneously, not that each
individual offset is impossible.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Deprecated compatibility spelling for the weak card-two single-offset
common-neighbor boundary.  Use `CardTwoAllOffsetsEndpointBoundary` instead. -/
@[deprecated CardTwoAllOffsetsEndpointBoundary (since := "2026-05-10")]
abbrev CardTwoSingleOffsetEndpointBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop :=
  MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary labeling

/-- Public compatibility spelling for the intended card-two endpoint boundary. -/
abbrev CardTwoIntendedAllOffsetsEndpointBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop :=
  CardTwoAllOffsetsEndpointBoundary labeling

namespace CardTwoSingleOffsetCompatibility

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The support-card API produces the intended all-offset card-two boundary. -/
def intendedAllOffsetsEndpointBoundary_of_supportCard
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    CardTwoIntendedAllOffsetsEndpointBoundary labeling :=
  supportCard.toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary

/-- Safe all-offset conversion to the support-indexed no-all-offset endpoint
adjacency boundary. -/
def toSupportNoAllOffsetsEndpointAdjBoundary
    (boundary : CardTwoIntendedAllOffsetsEndpointBoundary labeling) :
    MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary

/-- Safe all-offset conversion to the global no-all-offset endpoint-adjacency
boundary used by the final-gap API. -/
def toNoAllOffsetsEndpointAdj
    (boundary : CardTwoIntendedAllOffsetsEndpointBoundary labeling) :
    NoAllOffsetsEndpointAdj labeling :=
  boundary.toNoAllOffsetsEndpointAdj

/-- Safe all-offset conversion to the global no-card/support-subset boundary,
once the midpoint-reflection criterion is available. -/
def toNoAllOffsetsSupportSubsetBoundary
    (boundary : CardTwoIntendedAllOffsetsEndpointBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    NoAllOffsetsSupportSubsetBoundary labeling :=
  boundary.toNoAllOffsetsSupportSubsetBoundary criterion

/-- Report-level no-card compatibility form from the intended all-offset
card-two boundary. -/
theorem not_supportSubsetExceptionIssueBoundary
    (boundary : CardTwoIntendedAllOffsetsEndpointBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling :=
  boundary.not_supportSubsetExceptionIssueBoundary criterion

/-- Safe conversion from the support-indexed no-all-offset endpoint boundary to
the global no-all-offset endpoint-adjacency boundary. -/
def supportNoAllOffsetsEndpointAdjBoundary_toNoAllOffsetsEndpointAdj
    (boundary :
      MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
        labeling) :
    NoAllOffsetsEndpointAdj labeling :=
  boundary.toNoAllOffsetsEndpointAdj

/-- Safe conversion from the support-indexed no-all-offset endpoint boundary to
the global no-card/support-subset boundary. -/
def supportNoAllOffsetsEndpointAdjBoundary_toNoAllOffsetsSupportSubsetBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
        labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    NoAllOffsetsSupportSubsetBoundary labeling :=
  boundary.toNoAllOffsetsSupportSubsetBoundary criterion

/-- Report-level no-card compatibility form from the support-indexed
no-all-offset endpoint boundary. -/
theorem supportNoAllOffsetsEndpointAdjBoundary_not_supportSubsetExceptionIssueBoundary
    (boundary :
      MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
        labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling :=
  boundary.not_supportSubsetExceptionIssueBoundary criterion

end CardTwoSingleOffsetCompatibility

end BranchOrbitABCReflectionLabeling

end

end Moore57
