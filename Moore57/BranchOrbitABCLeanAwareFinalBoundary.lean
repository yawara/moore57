import Moore57.BranchOrbitABCFixedStarFinalBridge
import Moore57.BranchOrbitABCExceptionCaseBoundary
import Moore57.BranchOrbitABCExceptionDoublingBoundary
import Moore57.BranchOrbitABCExceptionCardTwoBoundary
import Moore57.BranchOrbitABCReferenceSolutionGeometryBoundary
import Moore57.BranchOrbitABCExceptionCardOneBoundary
import Moore57.BranchOrbitABCExceptionAllSupportBoundary
import Moore57.BranchOrbitABCReferenceSolutionFromExceptions
import Moore57.BranchOrbitABCSupportComplementSumBoundary

/-!
# Lean-aware fixed-star final boundary

This file states the current branch of the natural-language proof in the
smallest boundary shape produced by the midpoint-reflection work:

* the midpoint middle A-vertex is the fixed-star center;
* reference matching solutions are fixed by the A-fixing reflection;
* the `S_h ∩ E` cardinality cases `1` and `2` are excluded.

The file contains only wiring.  It does not prove those three remaining
geometric inputs.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instLeanAwareFinalBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instLeanAwareFinalBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Current Lean-aware package of the remaining geometric inputs after the
midpoint-reflection bridge. -/
structure LeanAwareFixedStarFinalBoundary
    (star : ReflectionFixedStarBoundary h)
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  middle : ReflectionFixedStarMiddleBoundary star labeling
  referenceSolutionVertexFixed :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling
  midpointExceptionAFixingSupportCase :
    MidpointExceptionAFixingSupportCaseBoundary labeling

namespace LeanAwareFixedStarFinalBoundary

variable {star : ReflectionFixedStarBoundary h}
variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the lean-aware remaining-input package to the cardinality pipeline
that feeds the final reflection-labeled compact-split contradiction. -/
noncomputable def toFixedStarReferenceMatchingCardinalityPipelineBoundary
    (boundary : LeanAwareFixedStarFinalBoundary star labeling) :
    FixedStarReferenceMatchingCardinalityPipelineBoundary star labeling :=
  FixedStarReferenceMatchingCardinalityPipelineBoundary.of_vertexFixed
    boundary.middle boundary.referenceSolutionVertexFixed
    (boundary.midpointExceptionAFixingSupportCase
      |>.toMidpointExceptionDisjointAFixingSupportBoundary
      |>.toAllFibersSupportComplementAtLeastTwoBoundary
        (labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
          star.toReflectionFixedCenterLeafBoundary)
        (boundary.middle.toMidpointMiddleFixedNeighborCardBoundary
          |>.toMidpointMiddleSupportCardTwoBoundary)
      |>.supportCompl_sum_ge)

/-- Expose the all-fibers lower-bound boundary derived from the midpoint
exception/A-fixing support case boundary. -/
noncomputable def toAllFibersSupportComplementAtLeastTwoBoundary
    (boundary : LeanAwareFixedStarFinalBoundary star labeling) :
    AllFibersSupportComplementAtLeastTwoBoundary labeling :=
  boundary.midpointExceptionAFixingSupportCase
    |>.toMidpointExceptionDisjointAFixingSupportBoundary
    |>.toAllFibersSupportComplementAtLeastTwoBoundary
      (labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
        star.toReflectionFixedCenterLeafBoundary)
      (boundary.middle.toMidpointMiddleFixedNeighborCardBoundary
        |>.toMidpointMiddleSupportCardTwoBoundary)

/-- Build the lean-aware final package from the A-fixing fixed-star-center
identification and the two remaining positive-cardinality exclusions. -/
noncomputable def of_aFixingCenter
    (middle : ReflectionFixedStarMiddleBoundary star labeling)
    (aFixing : ReflectionFixedStarAFixingBoundary star labeling)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (no_card_two :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2) :
    LeanAwareFixedStarFinalBoundary star labeling where
  middle := middle
  referenceSolutionVertexFixed := referenceSolutionVertexFixed
  midpointExceptionAFixingSupportCase :=
    { support_card_boundary :=
        aFixing.toAFixingReflectionFixedNeighborCardBoundary
      no_card_one := no_card_one
      no_card_two := no_card_two }

/-- Variant of `of_aFixingCenter` using the more finite-set oriented boundary
that reference matching solutions lie outside the A-fixing moving support. -/
noncomputable def of_aFixingCenter_referenceSupportCompl
    (middle : ReflectionFixedStarMiddleBoundary star labeling)
    (aFixing : ReflectionFixedStarAFixingBoundary star labeling)
    (referenceSolutionSupportCompl :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling)
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (no_card_two :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  of_aFixingCenter middle aFixing
    referenceSolutionSupportCompl.toReferenceRotationMatchingSolutionVertexFixedBoundary
    no_card_one no_card_two

/-- Variant using doubling propagation to supply the `no_card_one` field and
non-containment of `E` in `S_(d/2)` to exclude the card-two case. -/
noncomputable def of_aFixingCenter_doubling_notAllSupport
    (middle : ReflectionFixedStarMiddleBoundary star labeling)
    (aFixing : ReflectionFixedStarAFixingBoundary star labeling)
    (referenceSolutionSupportCompl :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling)
    (doubling : MidpointExceptionDoublingBoundary labeling)
    {baseOne : ZMod 19} (hbaseOne : baseOne ≠ 0)
    (hne_one :
      (labeling.midpointExceptionAFixingSupportIntersection
        baseOne hbaseOne).card ≠ 1)
    (not_all_support_subset_exception :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ¬ labeling.aFiberReflectionSupport ⊆
          labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  of_aFixingCenter_referenceSupportCompl middle aFixing
    referenceSolutionSupportCompl
    (doubling.no_card_one_of_card_ne_one hbaseOne hne_one)
    ((MidpointExceptionAFixingSupportNoCardTwoBoundary.mk
      not_all_support_subset_exception).no_card_two
        aFixing.toAFixingReflectionFixedNeighborCardBoundary)

/-- Variant using the card-one singleton-fixed boundary and an endpoint-adjacency
negation for the card-two case. -/
noncomputable def of_aFixingCenter_doubling_singletonFixed_noAllEndpointAdj
    (middle : ReflectionFixedStarMiddleBoundary star labeling)
    (aFixing : ReflectionFixedStarAFixingBoundary star labeling)
    (referenceSolutionSupportCompl :
      ReferenceRotationMatchingSolutionAFixingSupportComplBoundary labeling)
    (singletonFixed :
      MidpointExceptionAFixingSupportSingletonFixedBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  of_aFixingCenter_referenceSupportCompl middle aFixing
    referenceSolutionSupportCompl
    singletonFixed.no_card_one
    ((noAllEndpointAdj.toMidpointExceptionAFixingSupportNoCardTwoBoundary
      (labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
        star.toReflectionFixedCenterLeafBoundary)).no_card_two
        aFixing.toAFixingReflectionFixedNeighborCardBoundary)

/-- Variant where the reference-solution fixedness is derived from the same
finite exception-case boundary used for the support-complement lower bound. -/
noncomputable def of_referenceMatching_aFixingCenter_cases
    (middle : ReflectionFixedStarMiddleBoundary star labeling)
    (aFixing : ReflectionFixedStarAFixingBoundary star labeling)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (caseBoundary : MidpointExceptionAFixingSupportCaseBoundary labeling) :
    LeanAwareFixedStarFinalBoundary star labeling :=
  of_aFixingCenter_referenceSupportCompl middle aFixing
    (caseBoundary.toReferenceRotationMatchingSolutionAFixingSupportComplBoundary
      referenceMatching)
    caseBoundary.no_card_one caseBoundary.no_card_two

end LeanAwareFixedStarFinalBoundary

end BranchOrbitABCReflectionLabeling

/-- No final lean-aware fixed-star package can coexist with the representation
component boundary. -/
theorem no_D19_leanAwareFixedStarFinalBoundary
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ _representationComponents :
          D19ActsOnMoore57.RepresentationCharacterComponentsBoundary h,
        ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling := by
  rintro ⟨representationComponents, star, labeling, boundary⟩
  exact no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary h
    ⟨representationComponents, star, labeling,
      boundary.toFixedStarReferenceMatchingCardinalityPipelineBoundary⟩

/-- Character-class version of `no_D19_leanAwareFixedStarFinalBoundary`. -/
theorem no_D19_characterClassBoundary_leanAwareFixedStarFinalBoundary
    (h : D19ActsOnMoore57 V Γ)
    {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ (DihedralGroup 19) W)
    (alpha beta gamma : ℕ)
    (finrank_eq : Module.finrank ℚ W = 1729)
    (trace_eq_character :
      ∀ g : DihedralGroup 19,
        Matrix.trace (E7Matrix Γ * permMatrix (h.smulEquiv g)) =
          ρ.character g)
    (characterClass : D19CharacterClassBoundary ρ alpha beta gamma)
    (reflection : (alpha : ℤ) - (beta : ℤ) = 33)
    (minus8_trivial_nonneg : alpha ≤ 113)
    (minus8_sign_nonneg : beta ≤ 58) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling := by
  intro hlean
  rcases hlean with ⟨star, labeling, boundary⟩
  exact no_D19_characterClassBoundary_fixedStarReferenceMatchingCardinalityPipeline_boundary
    h ρ alpha beta gamma finrank_eq trace_eq_character characterClass
    reflection minus8_trivial_nonneg minus8_sign_nonneg
    ⟨star, labeling,
      boundary.toFixedStarReferenceMatchingCardinalityPipelineBoundary⟩

end

end Moore57
