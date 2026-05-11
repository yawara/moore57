import Moore57.ReflectionRawActionFixedStar
import Moore57.BranchOrbitABCSupportCardFrontier
import Moore57.BranchOrbitABCCardTwoAllOffsetsFinalGapBoundary

/-!
# Raw-action default-base frontier bridge

The raw action now supplies both reflection fixed-star and fixed-center-leaf
boundaries.  This file uses those positive facts to remove the corresponding
fields from the default-base non-representation frontier constructors.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw action supplies the corrected all-offset endpoint obstruction on every
default-base labeling.  This is the useful replacement for trying to prove the
older single-offset `noAllEndpointAdj` shape from the card-two common-neighbor
construction. -/
def noAllOffsetsEndpointAdj_of_raw_action_defaultBase
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.NoAllOffsetsEndpointAdj
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
    |>.reflectionFixedStarAFixingBoundary_of_raw_action
    |>.toAFixingReflectionFixedNeighborCardBoundary
    |>.toNoAllOffsetsEndpointAdj

/-- Raw action supplies the all-offset no-support-subset boundary on every
default-base labeling. -/
def noAllOffsetsSupportSubsetBoundary_of_raw_action_defaultBase
    (k : ZMod 19) :
    BranchOrbitABCReflectionLabeling.NoAllOffsetsSupportSubsetBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  h.noAllOffsetsEndpointAdj_of_raw_action_defaultBase k
    |>.toNoAllOffsetsSupportSubsetBoundary
      ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        |>.midpointReflectionCriterionBoundary_of_raw_action)

/-- Raw action rules out the global all-offset support-subset exception on
every default-base labeling. -/
theorem not_supportSubsetExceptionIssueBoundary_of_raw_action_defaultBase
    (k : ZMod 19) :
    ¬ BranchOrbitABCSupportSubsetExceptionIssueBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  h.noAllOffsetsSupportSubsetBoundary_of_raw_action_defaultBase k
    |>.not_supportSubsetExceptionIssueBoundary

/-- No raw-action default-base labeling can satisfy the global support-subset
exception package. -/
theorem not_exists_supportSubsetExceptionIssueBoundary_of_raw_action_defaultBase :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCSupportSubsetExceptionIssueBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, supportSubset⟩
  exact h.not_supportSubsetExceptionIssueBoundary_of_raw_action_defaultBase k
    supportSubset

/-- Raw-action constructor for the default-base A-fixing frontier.  The
fixed-star and fixed-center-leaf fields are supplied automatically from the raw
action; the remaining inputs are the genuinely local default-base fields. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_fields
    (k : ZMod 19)
    (aFixing :
      BranchOrbitABCReflectionLabeling.ReflectionFixedStarAFixingBoundary
        h.reflectionFixedStarBoundary_of_raw_action
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h where
  star := h.reflectionFixedStarBoundary_of_raw_action
  fixedCenterLeaf := h.reflectionFixedCenterLeafBoundary_of_raw_action
  k := k
  aFixing := aFixing
  referenceMatching := referenceMatching
  no_card_one := no_card_one
  noAllEndpointAdj := noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier with the
A-fixing center identification filled automatically.  The remaining inputs are
now the reference-matching pipeline, card-one exclusion, and endpoint-adjacency
obstruction. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    (k : ZMod 19)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_fields
    k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.reflectionFixedStarAFixingBoundary_of_raw_action)
    referenceMatching no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier after reducing
the reference-matching pipeline to vertex-fixed reference solutions. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.referenceMatchingPipelineBoundary_of_raw_action_vertexFixed
        referenceSolutionVertexFixed)
    no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier with the
one-point exception case supplied by singleton-fixedness. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed_singletonFixed
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed
    k referenceSolutionVertexFixed singletonFixed.no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier from an
independent reference-to-midpoint comparison and endpoint target-sign
compatibility. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointTargetSign
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointTargetSign :
      BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  let singletonFixed :=
    endpointTargetSign.toMidpointEquationSetAFixingInvariantBoundary
      |>.toMidpointExceptionAFixingSupportSingletonFixedBoundary
        labeling.midpointReflectionCriterionBoundary_of_raw_action
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k
    (labeling.referenceMatchingPipelineBoundary_of_raw_action
      labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
      referenceToMidpoint)
    singletonFixed.no_card_one noAllEndpointAdj

/-- Raw-action constructor for the default-base A-fixing frontier from an
independent reference-to-midpoint comparison and the corrected negative-endpoint
label exchange. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNegativePair
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNegativePair :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h :=
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
  let noPaired :=
    endpointNegativePair
      |>.toMidpointExceptionAFixingSupportNoPairedSingletonBoundary criterion
  let transport :=
    labeling.midpointExceptionAFixingSupportIntersectionNegInvariantBoundary
      criterion
  let noCardOne :=
    noPaired.toMidpointExceptionAFixingSupportNoCardOneBoundary transport
  h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k
    (labeling.referenceMatchingPipelineBoundary_of_raw_action
      labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
      referenceToMidpoint)
    noCardOne.no_card_one noAllEndpointAdj

/-- Raw-action constructor for the explicit default-base non-representation
frontier after removing the `star`, `fixedCenterLeaf`, and `support_card_boundary`
fields. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_fields
    (k : ZMod 19)
    (referenceMatching :
      BranchOrbitABCReflectionLabeling.ReferenceMatchingPipelineBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action
    k referenceMatching no_card_one noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier after reducing
the reference-matching pipeline to vertex-fixed reference solutions. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_vertexFixed_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
            |>.midpointExceptionAFixingSupportIntersection
              (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed
    k referenceSolutionVertexFixed no_card_one noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier with the
one-point exception case supplied by singleton-fixedness. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_vertexFixed_singletonFixed_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (singletonFixed :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportSingletonFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_vertexFixed_singletonFixed
    k referenceSolutionVertexFixed singletonFixed noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from an
independent reference-to-midpoint comparison and endpoint target-sign
compatibility. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointTargetSign_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointTargetSign :
      BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointTargetSign
    k referenceToMidpoint endpointTargetSign noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the explicit default-base frontier from an
independent reference-to-midpoint comparison and the corrected negative-endpoint
label exchange. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointNegativePair :
      BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBase h :=
  (h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNegativePair
    k referenceToMidpoint endpointNegativePair noAllEndpointAdj)
    |>.toRemainingNonRepresentationFrontierAfterDefaultBase

/-- Raw-action constructor for the fixed-star-local default-base frontier.  This
removes the now-proved raw fixed-star and fixed-center-leaf fields from the
connector surface. -/
noncomputable def
    remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_raw_action_fields
    (k : ZMod 19)
    (fixedStarLocal :
      BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
        h.reflectionFixedStarBoundary_of_raw_action
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector h where
  star := h.reflectionFixedStarBoundary_of_raw_action
  fixedCenterLeaf := h.reflectionFixedCenterLeafBoundary_of_raw_action
  k := k
  fixedStarLocal := fixedStarLocal

end D19ActsOnMoore57

end

end Moore57
