import Moore57.BranchOrbitABCExceptionDisjointBoundary
import Moore57.D19LabeledReflectionMatchingEquationFrontier

/-!
# Reference-fiber matching-equation frontier

This file keeps a non-representation connector from the existing
reference-matching pipeline to the public reference-fiber matching-equation
alias.  The extra non-formal input beyond `ReferenceMatchingPipelineBoundary`
is the existing disjointness boundary between midpoint exceptions and the
A-fixing reflection support; that boundary supplies the lower bound matching
the pipeline's two-point upper bound.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReferenceFiberMatchingEquationFrontierPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReferenceFiberMatchingEquationFrontierBranchDataPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P :=
  labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instReferenceFiberMatchingEquationFrontierDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Non-representation connector from the reference matching pipeline plus the
midpoint-exception disjointness lower bound to the exact reference-fiber
matching equation in the promoted `BranchOrbitABCData` coordinates. -/
theorem referenceFiberMatchingEquationCardTwo_of_referenceMatchingPipeline_disjoint
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceMatching : ReferenceMatchingPipelineBoundary labeling)
    (disjoint : MidpointExceptionDisjointAFixingSupportBoundary labeling) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ :
          Finset
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates
            0 (0 + d) (index_ne_add_of_ne_zero hd) p =
          (labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
            d 0 p).card =
        2 := by
  intro d hd
  have hcard :
      ((Finset.univ :
          Finset labeling.data.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates
            0 (0 + d) (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p).card =
        2 := by
    rw [← AFiberRotationEquivariance.matchingRotationPerm_support_compl_card_eq_filter_card
      labeling.data.toAFiberRotationEquivariance d 0 hd]
    exact disjoint.reference_matching_supportCompl_card_eq_two
      referenceMatching d hd
  simpa using hcard

/-- Bundled diagnostic connector: the exact additional non-representation data
needed after `ReferenceMatchingPipelineBoundary` is the midpoint-exception
disjointness boundary. -/
structure ReferenceFiberMatchingEquationFrontierBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  referenceMatching : ReferenceMatchingPipelineBoundary labeling
  midpointExceptionDisjoint :
    MidpointExceptionDisjointAFixingSupportBoundary labeling

namespace ReferenceFiberMatchingEquationFrontierBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Collapse the bundled frontier inputs to the exact reference-fiber
matching-equation statement in promoted branch coordinates. -/
theorem toReferenceFiberMatchingEquationCardTwo
    (boundary : ReferenceFiberMatchingEquationFrontierBoundary labeling) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ :
          Finset
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toBranchOrbitABCData.toAFiberCoordinates
            0 (0 + d) (index_ne_add_of_ne_zero hd) p =
          (labeling.data.toBranchOrbitABCData.toAFiberRotationEquivariance).coordPerm
            d 0 p).card =
        2 :=
  referenceFiberMatchingEquationCardTwo_of_referenceMatchingPipeline_disjoint
    labeling boundary.referenceMatching boundary.midpointExceptionDisjoint

end ReferenceFiberMatchingEquationFrontierBoundary

/-- Specialization to the canonical labeling attached to a minimal labeled
reflection pair, giving the public `ReferenceFiberMatchingEquationCardTwoOfPair`
alias. -/
theorem referenceFiberMatchingEquationCardTwoOfPair_of_referenceMatchingPipeline_disjoint
    (hp : HasLabeledReflectionPair h)
    (referenceMatching :
      ReferenceMatchingPipelineBoundary
        (ofHasLabeledReflectionPair (h := h) hp))
    (disjoint :
      MidpointExceptionDisjointAFixingSupportBoundary
        (ofHasLabeledReflectionPair (h := h) hp)) :
    ReferenceFiberMatchingEquationCardTwoOfPair (h := h) hp :=
  referenceFiberMatchingEquationCardTwo_of_referenceMatchingPipeline_disjoint
    (ofHasLabeledReflectionPair (h := h) hp) referenceMatching disjoint

/-- Bundled specialization of the frontier inputs to
`ReferenceFiberMatchingEquationCardTwoOfPair`. -/
theorem ReferenceFiberMatchingEquationFrontierBoundary.toReferenceFiberMatchingEquationCardTwoOfPair
    (hp : HasLabeledReflectionPair h)
    (boundary :
      ReferenceFiberMatchingEquationFrontierBoundary
        (ofHasLabeledReflectionPair (h := h) hp)) :
    ReferenceFiberMatchingEquationCardTwoOfPair (h := h) hp :=
  referenceFiberMatchingEquationCardTwoOfPair_of_referenceMatchingPipeline_disjoint
    hp boundary.referenceMatching boundary.midpointExceptionDisjoint

end BranchOrbitABCReflectionLabeling

end

end Moore57
