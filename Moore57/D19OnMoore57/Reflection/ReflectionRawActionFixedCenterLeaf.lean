import Moore57.D19OnMoore57.Reflection.ReflectionAdjacentMovedPositive
import Moore57.D19OnMoore57.Reflection.ReflectionRawGeometrySplit
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDefaultBaseReferenceFrontier
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCReferenceMatchingPipeline

/-!
# Raw-action fixed-center leaf bridge

The Cameron/Higman reflection fixed-count slice is now available directly from
the raw `D19ActsOnMoore57` action.  This file records the immediate geometric
consequence used by the default-base branch-orbit frontier: every reflection
has the fixed-center leaf bound, hence the default center-neighbor base already
supplies a labeled reflection pair.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReflectionRawActionFixedCenterLeafPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReflectionRawActionFixedCenterLeafBranchDataPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P :=
  labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instReflectionRawActionFixedCenterLeafDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw action gives the local fixed-center leaf geometry for every
reflection. -/
theorem reflectionFixedCenterLeafAt_of_raw_action
    (k : ZMod 19) :
    ReflectionFixedCenterLeafAt h k :=
  h.reflectionFixedCenterLeafAt_of_fixedVertexCount_eq_56 k
    (h.fixedVertexCount_reflection_eq_56_of_raw_action k)

/-- Raw action gives the global fixed-center leaf boundary used by the
default-base branch-orbit frontier. -/
theorem reflectionFixedCenterLeafBoundary_of_raw_action :
    ReflectionFixedCenterLeafBoundary h where
  degree_le_one := by
    intro k
    exact (h.reflectionFixedCenterLeafAt_of_raw_action k).degree_le_one

/-- Raw action gives the fixed-neighbor bound around `rotationFixedCenter`
for every reflection. -/
theorem fixed_center_neighbors_card_le_one_of_raw_action
    (k : ZMod 19) :
    ((Γ.neighborFinset h.rotationFixedCenter).filter fun y =>
      h.smul (DihedralGroup.sr k) y = y).card ≤ 1 :=
  h.reflectionFixedCenterLeafBoundary_of_raw_action
    |>.fixed_center_neighbors_card_le_one k

/-- The default center-neighbor base already yields a labeled reflection pair
from the raw action. -/
noncomputable def fixedCenterLeafDefaultBasePair_of_raw_action
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.HasLabeledReflectionPair h :=
  BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBasePair
    (h := h) h.reflectionFixedCenterLeafBoundary_of_raw_action k

/-- Canonical default-base labeling obtained from the raw action. -/
noncomputable abbrev fixedCenterLeafDefaultBaseLabeling_of_raw_action
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling h :=
  BranchOrbitABCReflectionLabeling.fixedCenterLeafDefaultBaseLabeling
    (h := h) h.reflectionFixedCenterLeafBoundary_of_raw_action k

/-- Once the reference-fiber matching equation is proved for the raw-action
default-base pair, the public labeled-reflection connector is available. -/
theorem remainingLabeledReflectionMatchingEquationConnector_of_raw_action
    (k : ZMod 19)
    (referenceMatchingEquationCardTwo :
      BranchOrbitABCReflectionLabeling.ReferenceFiberMatchingEquationCardTwoOfPair
        (h := h) (h.fixedCenterLeafDefaultBasePair_of_raw_action k)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  ⟨h.fixedCenterLeafDefaultBasePair_of_raw_action k,
    referenceMatchingEquationCardTwo⟩

/-- Raw-action spelling of the default-base reference connector: the only
remaining fields are the reference matching pipeline and the midpoint
disjointness boundary for the induced default-base labeling. -/
noncomputable def remainingDefaultBaseFixedCenterLeafReferenceConnector_of_raw_action
    (k : ZMod 19)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (midpointExceptionDisjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h where
  fixedCenterLeaf := h.reflectionFixedCenterLeafBoundary_of_raw_action
  k := k
  referenceMatching := referenceMatching
  midpointExceptionDisjoint := midpointExceptionDisjoint

end D19ActsOnMoore57

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw action supplies the midpoint-reflection criterion for any
reflection-compatible branch labeling. -/
noncomputable def midpointReflectionCriterionBoundary_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h) :
    MidpointReflectionCriterionBoundary labeling :=
  labeling.midpointReflectionCriterionBoundary_of_fixedCenterLeaf
    h.reflectionFixedCenterLeafBoundary_of_raw_action

/-- Raw action supplies the first field of the reference matching pipeline.
The remaining inputs are the middle support-card-two statement and the
reference-to-midpoint comparison. -/
noncomputable def referenceMatchingPipelineBoundary_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h)
    (midpointSupportCardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (referenceToMidpoint : ReferenceRotationToMidpointReflectionBoundary labeling) :
    ReferenceMatchingPipelineBoundary labeling where
  criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
  midpointSupportCardTwo := midpointSupportCardTwo
  referenceToMidpoint := referenceToMidpoint

/-- Raw action gives the cardinality comparison between midpoint equation
sets and midpoint supports for any compatible labeling. -/
theorem midpointEquationSet_card_eq_midpointMiddleSupport_card_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0) :
    (labeling.midpointEquationSet m hm).card =
      (labeling.midpointMiddleSupport m).card :=
  labeling.midpointReflectionCriterionBoundary_of_raw_action
    |>.midpointEquationSet_card_eq_midpointMiddleSupport_card m hm

/-- Raw action unfolds the reference-fiber matching-equation frontier down to
the two genuinely remaining fields: middle support-card-two and
midpoint-exception disjointness, plus the reference-to-midpoint comparison. -/
noncomputable def referenceFiberMatchingEquationFrontierBoundary_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h)
    (midpointSupportCardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (referenceToMidpoint : ReferenceRotationToMidpointReflectionBoundary labeling)
    (midpointExceptionDisjoint :
      MidpointExceptionDisjointAFixingSupportBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling where
  referenceMatching :=
    labeling.referenceMatchingPipelineBoundary_of_raw_action
      midpointSupportCardTwo referenceToMidpoint
  midpointExceptionDisjoint := midpointExceptionDisjoint

/-- Raw-action constructor for the exact reference-fiber matching equation on
any compatible labeling. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h)
    (midpointSupportCardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (referenceToMidpoint : ReferenceRotationToMidpointReflectionBoundary labeling)
    (midpointExceptionDisjoint :
      MidpointExceptionDisjointAFixingSupportBoundary labeling) :
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
  classical
  letI := labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype
  exact
    (labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action
      midpointSupportCardTwo referenceToMidpoint midpointExceptionDisjoint)
      |>.toReferenceFiberMatchingEquationCardTwo

end BranchOrbitABCReflectionLabeling

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw-action default-base reference connector with the automatic midpoint
criterion expanded away. -/
noncomputable def remainingDefaultBaseFixedCenterLeafReferenceConnector_of_raw_action_fields
    (k : ZMod 19)
    (midpointSupportCardTwo :
      BranchOrbitABCReflectionLabeling.MidpointMiddleSupportCardTwoBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (midpointExceptionDisjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedCenterLeafReferenceConnector_of_raw_action k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.referenceMatchingPipelineBoundary_of_raw_action
        midpointSupportCardTwo referenceToMidpoint)
    midpointExceptionDisjoint

/-- Raw-action default-base constructor for the public labeled-reflection
matching-equation connector, with the automatic midpoint criterion expanded
away. -/
theorem remainingLabeledReflectionMatchingEquationConnector_of_raw_action_fields
    (k : ZMod 19)
    (midpointSupportCardTwo :
      BranchOrbitABCReflectionLabeling.MidpointMiddleSupportCardTwoBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (midpointExceptionDisjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.referenceFiberMatchingEquationFrontierBoundary_of_raw_action
        midpointSupportCardTwo referenceToMidpoint midpointExceptionDisjoint
      |>.toReferenceFiberMatchingEquationCardTwoOfPair
        (h.fixedCenterLeafDefaultBasePair_of_raw_action k))

end D19ActsOnMoore57

end

end Moore57
