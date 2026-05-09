import Moore57.BranchOrbitABCFixedStarFinalBridge
import Moore57.BranchOrbitABCExceptionDisjointBoundary
import Moore57.BranchOrbitABCSupportComplementSumBoundary

/-!
# Lean-aware fixed-star final boundary

This file states the current branch of the natural-language proof in the
smallest boundary shape produced by the midpoint-reflection work:

* the midpoint middle A-vertex is the fixed-star center;
* reference matching solutions are fixed by the A-fixing reflection;
* each A-fiber contributes at least two matching fixed coordinates.

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
  midpointExceptionDisjointAFixingSupport :
    MidpointExceptionDisjointAFixingSupportBoundary labeling

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
    (boundary.midpointExceptionDisjointAFixingSupport
      |>.toAllFibersSupportComplementAtLeastTwoBoundary
        (labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
          star.toReflectionFixedCenterLeafBoundary)
        (boundary.middle.toMidpointMiddleFixedNeighborCardBoundary
          |>.toMidpointMiddleSupportCardTwoBoundary)
      |>.supportCompl_sum_ge)

/-- Expose the all-fibers lower-bound boundary derived from the midpoint
exception/A-fixing support disjointness field. -/
noncomputable def toAllFibersSupportComplementAtLeastTwoBoundary
    (boundary : LeanAwareFixedStarFinalBoundary star labeling) :
    AllFibersSupportComplementAtLeastTwoBoundary labeling :=
  boundary.midpointExceptionDisjointAFixingSupport
    |>.toAllFibersSupportComplementAtLeastTwoBoundary
      (labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
        star.toReflectionFixedCenterLeafBoundary)
      (boundary.middle.toMidpointMiddleFixedNeighborCardBoundary
        |>.toMidpointMiddleSupportCardTwoBoundary)

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
