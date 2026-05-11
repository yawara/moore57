import Moore57.ReferenceMatchingSupportComplFromDisjointness
import Moore57.MidpointExceptionECardTwoContradiction
import Moore57.ReflectionRawActionFixedStar
import Moore57.AFiberAllFibersCardinalityBoundary
import Moore57.BranchOrbitABCExceptionDisjointBoundary

/-!
# `AFiberCardinality38Boundary` from the now-closed Lemma 6.3/6.4 + raw action

This file completes Option A of the post-Lemma-6.3 wiring:

* combine `MidpointExceptionDisjointAFixingSupportBoundary` (proved here in
  `MidpointExceptionECardTwoContradiction`) with raw-action consequences
  (criterion, middle support card two) and the proved reference-side support
  complement to construct `ReferenceMatchingPipelineBoundary`,
* invoke the existing `matching_supportCompl_card_eq_two` to get
  `|support^c| = 2` for every nonzero `d` and fiber index `i`,
* feed into `AFiberCardinality38Boundary.of_allFibers_matchingRotationPerm_support_compl_card_eq_two`
  to obtain the all-fiber `38` boundary.

Combined with raw action, this gives the natural-language **Theorem 6.5 / 7.6**
(A-fiber contribution is `38` for every nonzero rotation step) directly from
`h : D19ActsOnMoore57 V Γ`, with no additional inputs.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberCardinality38PFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instAFiberCardinality38DecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reference-matching pipeline boundary from raw-action consequences plus
the now-proved reference-side support-complement closure. -/
noncomputable def referenceMatchingPipelineBoundary_of_closures
    (labeling : BranchOrbitABCReflectionLabeling h) :
    ReferenceMatchingPipelineBoundary labeling :=
  let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
  let supportCard :=
    labeling.reflectionFixedStarAFixingBoundary_of_raw_action
      |>.toAFixingReflectionFixedNeighborCardBoundary
  let supportCompl :=
    labeling.referenceRotationMatchingSolutionAFixingSupportComplBoundary_of_criterion_supportCard
      criterion supportCard
  let referenceToMidpoint :=
    supportCompl.toReferenceRotationToMidpointReflectionBoundary
  labeling.referenceMatchingPipelineBoundary_of_raw_action
    labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
    referenceToMidpoint

/-- Every nonzero-step matching-rotation permutation has exactly two fixed
coordinates in every A-fiber, from the now-closed Lemma 6.3 + the proved
reference-side support complement. -/
theorem matching_supportCompl_card_eq_two_of_closures
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0) (i : ZMod 19) :
    (labeling.data.toAFiberRotationEquivariance.matchingRotationPerm
      d i hd).supportᶜ.card = 2 := by
  classical
  let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
  let supportCard :=
    labeling.reflectionFixedStarAFixingBoundary_of_raw_action
      |>.toAFixingReflectionFixedNeighborCardBoundary
  let disjointness :=
    labeling.midpointExceptionDisjointAFixingSupportBoundary_of_criterion_supportCard
      criterion supportCard
  let pipeline := labeling.referenceMatchingPipelineBoundary_of_closures
  exact disjointness.matching_supportCompl_card_eq_two pipeline d hd i

/-- The all-A-fiber cardinality `38` boundary for any `BranchOrbitABCReflectionLabeling`,
constructed entirely from raw-action consequences and the now-proved Lemma 6.3 +
Lemma 6.4 inclusion (no additional axiomatic inputs).

This is the natural-language Theorem 6.5 / 7.6: the A-fiber contribution to
each nonzero rotation step is exactly `38`. -/
noncomputable def aFiberCardinality38Boundary_of_closures
    (labeling : BranchOrbitABCReflectionLabeling h) :
    AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  AFiberCardinality38Boundary.of_allFibers_matchingRotationPerm_support_compl_card_eq_two
    labeling.data.toAFiberRotationEquivariance
    (fun d hd i =>
      labeling.matching_supportCompl_card_eq_two_of_closures d hd i)

end BranchOrbitABCReflectionLabeling

namespace D19ActsOnMoore57

/-- Raw-action wrapper: the all-A-fiber cardinality `38` boundary for the
default-base labeling at parameter `k`, with no additional axiomatic inputs. -/
noncomputable def aFiberCardinality38Boundary_of_raw_action
    (h : D19ActsOnMoore57 V Γ) (k : ZMod 19) :
    AFiberCardinality38Boundary h
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action
    k).aFiberCardinality38Boundary_of_closures

end D19ActsOnMoore57

end

end Moore57
