import Moore57.D19OnMoore57.E7Projection.Minus8RotationSplitAdjacentSwapNoGo
import Moore57.D19OnMoore57.LinearCharacter.Nonempty
import Moore57.D19OnMoore57.NoGo.EndpointFinalBoundaryNoGoConnectors
import Moore57.D19OnMoore57.NoGo.RemainingRawActionFrontier
import Moore57.D19OnMoore57.NoGo.LabeledReflectionMatchingEquationFrontier
import Moore57.D19OnMoore57.NoGo.LabeledReflectionMatchingEquationFromDisjoint
import Moore57.D19OnMoore57.NoGo.FixedCenterLeafReplacement
import Moore57.D19OnMoore57.NoGo.EndpointFrontier
import Moore57.D19OnMoore57.NoGo.DefaultBaseCombinedFrontier
import Moore57.D19OnMoore57.NoGo.DefaultBaseFrontierNoGoConnectors
import Moore57.D19OnMoore57.NoGo.FixedStarBoundaryNoGoConnectors
import Moore57.D19OnMoore57.Reflection.RemainingLeafConnectorBoundary
import Moore57.D19OnMoore57.Reflection.RawActionDefaultBaseFrontier

/-!
# Raw-action no-go connectors from the rotation split

The rotation-invariant / moving-summand split, together with the raw reflection
fixed-count theorem, now constructs `Nonempty (D19LinearCharacterInput h)` from
the raw `D19ActsOnMoore57` action.  This file re-exposes the existing
action-level and current-gap no-go surfaces without representation-component
or fixed-count hypotheses.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace D19ActsOnMoore57

/-- Raw action plus the concrete rotation split supplies the representation
component package consumed by the public branch-orbit no-go frontiers. -/
theorem representationCharacterComponentsBoundary_of_rotation_split_and_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    RepresentationCharacterComponentsBoundary h :=
  D19ActsOnMoore57.representationCharacterComponentsBoundary_of_nonempty_linearCharacterInput
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

end D19ActsOnMoore57

private theorem no_nonempty_frontier_of_rotation_split_raw_action_components
    (h : D19ActsOnMoore57 V Γ)
    {Frontier : Type*}
    (hno :
      ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
          Nonempty Frontier) :
    ¬ Nonempty Frontier := by
  intro hfrontier
  exact hno
    ⟨h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action,
      hfrontier⟩

private theorem no_prop_frontier_of_rotation_split_raw_action_components
    (h : D19ActsOnMoore57 V Γ)
    {Frontier : Prop}
    (hno :
      ¬ ∃ _representationComponents : RemainingRepresentationComponents h,
          Frontier) :
    ¬ Frontier := by
  intro hfrontier
  exact hno
    ⟨h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action,
      hfrontier⟩

/-! ## Action-level frontiers -/

theorem no_D19_actionLevelCaseBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelCaseBoundary h) :=
  no_D19_actionLevelCaseBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelWitnessBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelWitnessBoundary h) :=
  no_D19_actionLevelWitnessBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelCoordinateWitnessBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelCoordinateWitnessBoundary h) :=
  no_D19_actionLevelCoordinateWitnessBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelFinalBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelFinalBoundary h) :=
  no_D19_actionLevelFinalBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelLocalObstructionBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelLocalObstructionBoundary h) :=
  no_D19_actionLevelLocalObstructionBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelDoublingEquationSupportBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelDoublingEquationSupportBoundary h) :=
  no_D19_actionLevelDoublingEquationSupportBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelSetInvariantWitnessBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelSetInvariantWitnessBoundary h) :=
  no_D19_actionLevelSetInvariantWitnessBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelReducedCoordinateWitnessBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelReducedCoordinateWitnessBoundary h) :=
  no_D19_actionLevelReducedCoordinateWitnessBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

/-! ## Current-gap frontiers -/

theorem no_D19_actionLevelCommonNeighborReducedBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelCommonNeighborReducedBoundary h) :=
  no_D19_actionLevelCommonNeighborReducedBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelMinimalRemainingBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingBoundary h) :=
  no_D19_actionLevelMinimalRemainingBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelMinimalRemainingRefinedBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelMinimalRemainingRefinedBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (BranchOrbitABCActionLevelMinimalRemainingRefinedMatchingBoundary h) :=
  no_D19_actionLevelMinimalRemainingRefinedMatchingBoundary_of_nonempty_linearCharacterInput h
    (h.nonempty_d19LinearCharacterInput_of_rotation_split_and_raw_action 0)

theorem no_D19_currentFinalGapBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCCurrentFinalGapBoundary h) :=
  h.no_currentFinalGapBoundary_of_rotation_split_and_raw_action

/-! ## Endpoint-final frontiers -/

theorem no_D19_actionLevelEndpointObstructionBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCActionLevelEndpointObstructionBoundary h) :=
  no_D19_actionLevelEndpointObstructionBoundary_of_components h
    h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action

theorem no_D19_endpointObstructionFinalBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCEndpointObstructionFinalBoundary h) :=
  no_D19_endpointObstructionFinalBoundary_of_components h
    h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action

theorem no_D19_endpointPairedFinalBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (BranchOrbitABCEndpointPairedFinalBoundary h) :=
  no_D19_endpointPairedFinalBoundary_of_components h
    h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action

/-! ## Fixed-star frontiers -/

theorem no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
            star labeling :=
  no_D19_fixedStarReferenceMatchingCardinalityPipeline_boundary_of_components h
    h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
            star labeling := by
  rintro ⟨star, labeling, boundary⟩
  exact no_D19_leanAwareFixedStarFinalBoundary h
    ⟨h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action,
      star, labeling, boundary⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceVertexFixed_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceSolutionVertexFixed, endpointPointwiseNonadj⟩
  exact no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action h
    ⟨h.reflectionFixedStarBoundary_of_raw_action,
      h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k,
      h.leanAwareFixedStarFinalBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj_fields
        k referenceSolutionVertexFixed endpointPointwiseNonadj⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPointwiseNonadj⟩
  exact no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action h
    ⟨h.reflectionFixedStarBoundary_of_raw_action,
      h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k,
      h.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
        k referenceToMidpoint endpointPointwiseNonadj⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointCommonNeighborBasic⟩
  exact no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action h
    ⟨h.reflectionFixedStarBoundary_of_raw_action,
      h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k,
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        |>.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
          referenceToMidpoint endpointCommonNeighborBasic⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointExchange⟩
  exact no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action h
    ⟨h.reflectionFixedStarBoundary_of_raw_action,
      h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k,
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        |>.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
          referenceToMidpoint endpointExchange⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoReflectedReferenceNegMatching⟩
  exact no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action h
    ⟨h.reflectionFixedStarBoundary_of_raw_action,
      h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k,
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
        |>.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
          referenceToMidpoint endpointNoReflectedReferenceNegMatching⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointNoPositiveTarget
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoPositiveTarget⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
      h
      ⟨k, referenceToMidpoint,
        endpointNoPositiveTarget.toEndpointSignNoReflectedReferenceNegMatchingBoundary⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceSupportCompl, endpointPointwiseNonadj⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceSupportCompl.toReferenceRotationToMidpointReflectionBoundary,
        endpointPointwiseNonadj⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointCommonNeighborBasic
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceSupportCompl, endpointCommonNeighborBasic⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
      h
      ⟨k, referenceSupportCompl.toReferenceRotationToMidpointReflectionBoundary,
        endpointCommonNeighborBasic⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointExchangeCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceSupportCompl, endpointExchange⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
      h
      ⟨k, referenceSupportCompl.toReferenceRotationToMidpointReflectionBoundary,
        endpointExchange⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointNoReflectedReferenceNegMatching
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceSupportCompl, endpointNoReflectedReferenceNegMatching⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
      h
      ⟨k, referenceSupportCompl.toReferenceRotationToMidpointReflectionBoundary,
        endpointNoReflectedReferenceNegMatching⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointNoPositiveTarget
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionAFixingSupportComplBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceSupportCompl, endpointNoPositiveTarget⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceToMidpoint_endpointNoPositiveTarget
      h
      ⟨k, referenceSupportCompl.toReferenceRotationToMidpointReflectionBoundary,
        endpointNoPositiveTarget⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_globalReferenceSupportCompl_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ (D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h ∧
        ∃ k : ZMod 19,
          BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
            (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) := by
  rintro ⟨referenceSupportCompl, k, endpointPointwiseNonadj⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointPointwiseNonadj
      h
      ⟨k,
        referenceSupportCompl.referenceRotationMatchingSolutionAFixingSupportComplBoundary
          k,
        endpointPointwiseNonadj⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_globalReferenceSupportCompl_endpointCommonNeighborBasic
    (h : D19ActsOnMoore57 V Γ) :
    ¬ (D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h ∧
        ∃ k : ZMod 19,
          BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
            (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) := by
  rintro ⟨referenceSupportCompl, k, endpointCommonNeighborBasic⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointCommonNeighborBasic
      h
      ⟨k,
        referenceSupportCompl.referenceRotationMatchingSolutionAFixingSupportComplBoundary
          k,
        endpointCommonNeighborBasic⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_globalReferenceSupportCompl_endpointExchangeCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ (D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h ∧
        ∃ k : ZMod 19,
          BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
            (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) := by
  rintro ⟨referenceSupportCompl, k, endpointExchange⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointExchangeCommonNeighbor
      h
      ⟨k,
        referenceSupportCompl.referenceRotationMatchingSolutionAFixingSupportComplBoundary
          k,
        endpointExchange⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_globalReferenceSupportCompl_endpointNoReflectedReferenceNegMatching
    (h : D19ActsOnMoore57 V Γ) :
    ¬ (D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h ∧
        ∃ k : ZMod 19,
          BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
            (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) := by
  rintro ⟨referenceSupportCompl, k, endpointNoReflectedReferenceNegMatching⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointNoReflectedReferenceNegMatching
      h
      ⟨k,
        referenceSupportCompl.referenceRotationMatchingSolutionAFixingSupportComplBoundary
          k,
        endpointNoReflectedReferenceNegMatching⟩

theorem no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_globalReferenceSupportCompl_endpointNoPositiveTarget
    (h : D19ActsOnMoore57 V Γ) :
    ¬ (D19ActsOnMoore57.RawActionDefaultBaseReferenceSolutionSupportComplBoundary h ∧
        ∃ k : ZMod 19,
          BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
            (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) := by
  rintro ⟨referenceSupportCompl, k, endpointNoPositiveTarget⟩
  exact
    no_D19_leanAwareFixedStarFinalBoundary_of_rotation_split_raw_action_referenceSupportCompl_endpointNoPositiveTarget
      h
      ⟨k,
        referenceSupportCompl.referenceRotationMatchingSolutionAFixingSupportComplBoundary
          k,
        endpointNoPositiveTarget⟩

theorem no_D19_fixedStarLocalObstructionBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarLocalObstructionBoundary
            star labeling :=
  no_D19_fixedStarLocalObstructionBoundary_of_components h
    h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action

theorem no_D19_fixedStarWitnessBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarWitnessBoundary star labeling :=
  no_D19_fixedStarWitnessBoundary_of_components h
    h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action

theorem no_D19_fixedStarCoordinateWitnessBoundary_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ star : ReflectionFixedStarBoundary h,
        ∃ labeling : BranchOrbitABCReflectionLabeling h,
          BranchOrbitABCReflectionLabeling.FixedStarCoordinateWitnessBoundary
            star labeling :=
  no_D19_fixedStarCoordinateWitnessBoundary_of_components h
    h.representationCharacterComponentsBoundary_of_rotation_split_and_raw_action

/-! ## Remaining raw-action and default-base frontiers -/

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingLabeledReflectionMatchingEquationConnector h :=
  no_prop_frontier_of_rotation_split_raw_action_components h
    (no_remainingLabeledReflectionMatchingEquationConnector_of_components h)

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointTargetSign
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointTargetSign, noAllEndpointAdj⟩
  exact no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action
    h
    (h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointTargetSign_fields
      k referenceToMidpoint endpointTargetSign noAllEndpointAdj)

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNegativePair, noAllEndpointAdj⟩
  exact no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action
    h
    (h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
      k referenceToMidpoint endpointNegativePair noAllEndpointAdj)

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPairedAdj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPairedAdj, noAllEndpointAdj⟩
  exact
    no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
      h
      ⟨k, referenceToMidpoint,
        endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary,
        noAllEndpointAdj⟩

/-- Rotation-split no-go with the endpoint side compressed to pointwise
endpoint non-adjacency, which supplies both paired endpoint adjacency and the
endpoint non-containment input. -/
theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPointwiseNonadj⟩
  exact no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action
    h
    (h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
      k referenceToMidpoint endpointPointwiseNonadj)

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointCommonNeighborBasic⟩
  exact
    no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointCommonNeighborBasic.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointExchange⟩
  exact
    no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointExchange.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoReflectedReferenceNegMatching⟩
  exact
    no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointNoReflectedReferenceNegMatching
          |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoPositiveTarget
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoPositiveTarget⟩
  exact
    no_remainingLabeledReflectionMatchingEquationConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
      h
      ⟨k, referenceToMidpoint,
        endpointNoPositiveTarget.toEndpointSignNoReflectedReferenceNegMatchingBoundary⟩

theorem no_remainingLabeledReflectionMatchingEquationFromDisjointConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingLabeledReflectionMatchingEquationFromDisjointConnector h :=
  no_prop_frontier_of_rotation_split_raw_action_components h
    (no_remainingLabeledReflectionMatchingEquationFromDisjointConnector_of_components h)

theorem no_remainingReflectionIndexMatchingEquationConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingReflectionIndexMatchingEquationConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingReflectionIndexMatchingEquationConnector_of_components h)

theorem no_remainingFixedNeighborBoundMatchingEquationConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingFixedNeighborBoundMatchingEquationConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingFixedNeighborBoundMatchingEquationConnector_of_components h)

theorem no_remainingFixedCenterLeafMatchingEquationConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingFixedCenterLeafMatchingEquationConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingFixedCenterLeafMatchingEquationConnector_of_components h)

theorem no_remainingNon56FixedCenterLeafIndexMatchingEquationConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingNon56FixedCenterLeafIndexMatchingEquationConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNon56FixedCenterLeafIndexMatchingEquationConnector_of_components h)

theorem no_remainingNon56FixedCenterLeafReferenceConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingNon56FixedCenterLeafReferenceConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNon56FixedCenterLeafReferenceConnector_of_components h)

theorem no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingNon56FixedCenterLeafMidpointDisjointnessConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNon56FixedCenterLeafMidpointDisjointnessConnector_of_components h)

theorem no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingNon56FixedCenterLeafLocalObstructionConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNon56FixedCenterLeafLocalObstructionConnector_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBase h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBase_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointTargetSign
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointTargetSign, noAllEndpointAdj⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action
    h
    ⟨h.remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointTargetSign_fields
      k referenceToMidpoint endpointTargetSign noAllEndpointAdj⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNegativePair, noAllEndpointAdj⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action
    h
    ⟨h.remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
      k referenceToMidpoint endpointNegativePair noAllEndpointAdj⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointPairedAdj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPairedAdj, noAllEndpointAdj⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
      h
      ⟨k, referenceToMidpoint,
        endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary,
        noAllEndpointAdj⟩

/-- Rotation-split no-go for the explicit default-base frontier with the
endpoint side compressed to pointwise endpoint non-adjacency. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPointwiseNonadj⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action
    h
    ⟨h.remainingNonRepresentationFrontierAfterDefaultBase_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
      k referenceToMidpoint endpointPointwiseNonadj⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointCommonNeighborBasic⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointCommonNeighborBasic.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointExchange⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointExchange.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoReflectedReferenceNegMatching⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointNoReflectedReferenceNegMatching
          |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointNoPositiveTarget
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoPositiveTarget⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBase_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
      h
      ⟨k, referenceToMidpoint,
        endpointNoPositiveTarget.toEndpointSignNoReflectedReferenceNegMatchingBoundary⟩

theorem no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ RemainingNonRepresentationRawActionFrontierAfterDefaultBase h :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationRawActionFrontierAfterDefaultBase_of_components h)

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingDefaultBaseFixedCenterLeafReferenceConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_components h)

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointTargetSign
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointTargetSign, noAllEndpointAdj⟩
  exact no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action
    h
    ⟨h.remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointTargetSign_fields
      k referenceToMidpoint endpointTargetSign noAllEndpointAdj⟩

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNegativePair, noAllEndpointAdj⟩
  exact no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action
    h
    ⟨h.remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
      k referenceToMidpoint endpointNegativePair noAllEndpointAdj⟩

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPairedAdj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPairedAdj, noAllEndpointAdj⟩
  exact
    no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
      h
      ⟨k, referenceToMidpoint,
        endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary,
        noAllEndpointAdj⟩

/-- Rotation-split no-go for the fixed-center-leaf reference connector with
the endpoint side compressed to pointwise endpoint non-adjacency. -/
theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPointwiseNonadj⟩
  exact no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action
    h
    ⟨h.remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
      k referenceToMidpoint endpointPointwiseNonadj⟩

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointCommonNeighborBasic⟩
  exact
    no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointCommonNeighborBasic.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointExchange⟩
  exact
    no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointExchange.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoReflectedReferenceNegMatching⟩
  exact
    no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointNoReflectedReferenceNegMatching
          |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoPositiveTarget
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoPositiveTarget⟩
  exact
    no_remainingDefaultBaseFixedCenterLeafReferenceConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
      h
      ⟨k, referenceToMidpoint,
        endpointNoPositiveTarget.toEndpointSignNoReflectedReferenceNegMatchingBoundary⟩

theorem no_remainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingDefaultBaseFixedCenterLeafMidpointDisjointnessConnector_of_components h)

theorem no_remainingDefaultBaseFixedCenterLeafLocalObstructionConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingDefaultBaseFixedCenterLeafLocalObstructionConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingDefaultBaseFixedCenterLeafLocalObstructionConnector_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointTargetSign
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingTargetSignBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointTargetSign, noAllEndpointAdj⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action
    h
    ⟨h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointTargetSign
      k referenceToMidpoint endpointTargetSign noAllEndpointAdj⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNegativeMatchingPairBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNegativePair, noAllEndpointAdj⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action
    h
    ⟨h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointNegativePair
      k referenceToMidpoint endpointNegativePair noAllEndpointAdj⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPairedAdj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPairedAdj, noAllEndpointAdj⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNegativePair
      h
      ⟨k, referenceToMidpoint,
        endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary,
        noAllEndpointAdj⟩

/-- Rotation-split no-go for the A-fixing default-base frontier with the
endpoint side compressed to pointwise endpoint non-adjacency. -/
theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointPointwiseNonadj⟩
  exact no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action
    h
    ⟨h.remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      k referenceToMidpoint endpointPointwiseNonadj⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.MidpointExceptionEndpointAdjCommonNeighborBasicBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointCommonNeighborBasic⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointCommonNeighborBasic.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointReferenceExchangeCommonNeighborBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointExchange⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointExchange.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointSignNoReflectedReferenceNegMatchingBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoReflectedReferenceNegMatching⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      h
      ⟨k, referenceToMidpoint,
        endpointNoReflectedReferenceNegMatching
          |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoPositiveTarget
    (h : D19ActsOnMoore57 V Γ) :
    ¬ ∃ k : ZMod 19,
        BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) ∧
        BranchOrbitABCReflectionLabeling.EndpointMatchingAFixingNoPositiveTargetBoundary
          (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) := by
  rintro ⟨k, referenceToMidpoint, endpointNoPositiveTarget⟩
  exact
    no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingConnector_of_rotation_split_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
      h
      ⟨k, referenceToMidpoint,
        endpointNoPositiveTarget.toEndpointSignNoReflectedReferenceNegMatchingBoundary⟩

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalConnector_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelLocalConnector_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseFixedInducedStarDegrees_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseFixedNeighborStarCounts_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155 h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseInvolutionK155_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointNonadjWitness_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointPointwiseNonadj_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingFixed_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseEndpointAdjForcesAFixingVertexFixed_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointNonadj_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBasePairEndpointTwoCommonNeighbors_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseLeanAwareEndpointObstruction_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingSingletonEndpointObstruction_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseAFixingDoublingEndpointObstruction_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseFixedStarLocalSingletonEndpointObstruction_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelSingletonEndpointObstruction_of_components h)

theorem no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_rotation_split_raw_action
    (h : D19ActsOnMoore57 V Γ) :
    ¬ Nonempty
        (RemainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction h) :=
  no_nonempty_frontier_of_rotation_split_raw_action_components h
    (no_remainingNonRepresentationFrontierAfterDefaultBaseActionLevelDoublingEndpointObstruction_of_components h)

end

end Moore57
