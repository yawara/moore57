import Moore57.D19OnMoore57.Final.D19FinalCriterionPublic
import Moore57.D19OnMoore57.D19Core.D19CanonicalBranchCompactSplitBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCLeanAwareFinalBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCActionLevelAllOffsetsSupportBoundary
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCFinalGapAllOffsetsContradiction
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCCardTwoSingleOffsetCompatibility

/-!
# Remaining gap after all-offset card-two

Diagnostic inventory for the public no-go surface after the all-offset
card-two obstruction.  The important change is that the all-offset card-two
work now rules out the equation/support and current-final-gap packages without
using representation data.  What remains for a genuine `D19ActsOnMoore57 →
False` theorem is therefore not another card-two contradiction, but connectors
constructing one of these boundary packages from a raw action.

This file intentionally adds no root import and no new mathematical
assumption.  It only gives stable aliases and theorem names for the remaining
frontier.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ## Boundary package aliases -/

/-- Representation-character component boundary still used by most public
`no_D19...` package theorems. -/
abbrev RemainingRepresentationComponents
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h

/-- Top compact-split canonical branch package. -/
abbrev RemainingCanonicalCompactSplitPackage
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (D19CanonicalBranchCompactSplitBoundaryInputs h)

/-- Older all-fiber canonical branch package, still publicly exposed. -/
abbrev RemainingCanonicalAllFibersPackage
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (D19CanonicalBranchAllFibersBoundaryInputs h)

/-- Reflection-labeled compact-split package. -/
abbrev RemainingReflectionLabeledCompactSplitPackage
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (D19ReflectionLabeledBranchCompactSplitBoundaryInputs h)

/-- Fixed-star/reference-matching cardinality frontier. -/
abbrev RemainingFixedStarReferenceMatchingPackage
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  ∃ _representationComponents : RemainingRepresentationComponents h,
    ∃ star : ReflectionFixedStarBoundary h,
    ∃ labeling : BranchOrbitABCReflectionLabeling h,
      BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
        star labeling

/-- Lean-aware fixed-star frontier. -/
abbrev RemainingLeanAwareFixedStarPackage
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  ∃ _representationComponents : RemainingRepresentationComponents h,
    ∃ star : ReflectionFixedStarBoundary h,
    ∃ labeling : BranchOrbitABCReflectionLabeling h,
      BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
        star labeling

/-- Action-level equation/support package closed by the all-offset card-two
connector. -/
abbrev RemainingActionLevelAllOffsetsSupportPackage
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h)

/-- Current final-gap report package closed by the all-offset card-two
connector. -/
abbrev RemainingCurrentFinalGapReportPackage
    (h : D19ActsOnMoore57 V Γ) : Prop :=
  Nonempty (BranchOrbitABCCurrentFinalGapBoundary h)

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Intended card-two endpoint boundary after the single-offset mismatch was
isolated. -/
abbrev RemainingCardTwoEndpointPackage
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop :=
  CardTwoIntendedAllOffsetsEndpointBoundary labeling

/-- Global no-support-subset package produced from the all-offset endpoint
obstruction plus the midpoint criterion. -/
abbrev RemainingNoAllOffsetsSupportSubsetPackage
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop :=
  NoAllOffsetsSupportSubsetBoundary labeling

end BranchOrbitABCReflectionLabeling

/-! ## Existing public no-go aliases -/

theorem no_remaining_canonicalAllFibersPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingCanonicalAllFibersPackage h :=
  no_D19_canonical_branch_allFibers_boundary h

theorem no_remaining_canonicalCompactSplitPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingCanonicalCompactSplitPackage h :=
  no_D19_canonical_branch_compact_split_boundary h

theorem no_remaining_reflectionLabeledCompactSplitPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingReflectionLabeledCompactSplitPackage h :=
  no_D19_reflection_labeled_branch_compact_split_boundary h

theorem no_remaining_fixedStarReferenceMatchingPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingFixedStarReferenceMatchingPackage h :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary h

theorem no_remaining_leanAwareFixedStarPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingLeanAwareFixedStarPackage h :=
  no_D19_leanAwareFixedStarFinalBoundary h

/-! ## All-offset card-two closures now available -/

/-- The action-level equation/support package is already inconsistent after
the all-offset card-two work; no representation component is needed. -/
theorem no_remaining_actionLevelAllOffsetsSupportPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingActionLevelAllOffsetsSupportPackage h :=
  not_actionLevelDoublingEquationSupportBoundary_allOffsets h

/-- Public `no_D19...` spelling for the same all-offset action-level closure. -/
theorem no_D19_remaining_actionLevelAllOffsetsSupportPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        RemainingActionLevelAllOffsetsSupportPackage h := by
  rintro ⟨_, hboundary⟩
  exact no_remaining_actionLevelAllOffsetsSupportPackage h hboundary

/-- The current final-gap report is already inconsistent after the all-offset
card-two work; no representation component is needed. -/
theorem no_remaining_currentFinalGapReportPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingCurrentFinalGapReportPackage h :=
  not_currentFinalGapBoundary_allOffsetsCommonNeighbor h

/-- Public `no_D19...` spelling for the all-offset current-final-gap closure. -/
theorem no_D19_remaining_currentFinalGapReportPackage
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
        RemainingCurrentFinalGapReportPackage h := by
  rintro ⟨_, hboundary⟩
  exact no_remaining_currentFinalGapReportPackage h hboundary

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Support-card plus midpoint criterion is enough to rule out the report-level
support-subset exception by the all-offset common-neighbor obstruction. -/
theorem no_supportSubsetException_from_supportCard_allOffsets
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling :=
  supportCard.not_supportSubsetExceptionIssueBoundary criterion

/-- The intended all-offset card-two endpoint package gives the same
report-level support-subset contradiction under the midpoint criterion. -/
theorem no_supportSubsetException_from_intendedCardTwoEndpoint
    (boundary : RemainingCardTwoEndpointPackage labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary labeling :=
  CardTwoSingleOffsetCompatibility.not_supportSubsetExceptionIssueBoundary
    boundary criterion

end BranchOrbitABCReflectionLabeling

end

end Moore57
