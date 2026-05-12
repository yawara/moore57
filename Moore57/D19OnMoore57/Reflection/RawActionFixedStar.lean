import Moore57.D19OnMoore57.Reflection.RawActionFixedCenterLeaf
import Moore57.D19OnMoore57.Reflection.FixedCountBoundsBridge
import Moore57.D19OnMoore57.Reflection.PaperFixedStarBoundary
import Moore57.D19OnMoore57.BranchOrbit.Matching
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCaseEndpointPointwiseBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointPairedSymmetryBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointExchangeCommonNeighborBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCLeanAwareFinalBoundary

/-!
# Raw-action paper fixed-star consequences

The raw reflection fixed-count theorem now supplies the paper-shaped fixed-star
package for every reflection.  This file exposes the reusable positive
consequences directly, without routing through a linear-character input.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instReflectionRawActionFixedStarPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instReflectionRawActionFixedStarBranchDataPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P :=
  labeling.data.toBranchOrbitABCData.toAFiberCoordinates.P_fintype

local instance instReflectionRawActionFixedStarDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw action gives the fixed-count bounds package used by older reflection
trace consumers. -/
def reflectionFixedCountBounds_of_raw_action :
    ReflectionFixedCountBounds h :=
  ReflectionFixedCountBounds.of_exact
    (h := h)
    h.fixedVertexCount_reflection_eq_56_of_raw_action

/-- Raw action gives the paper-shaped `56`-vertex fixed-star statement for
every reflection. -/
theorem involutionFixedSetStar56_of_raw_action
    (k : ZMod 19) :
    InvolutionFixedSetStar56 Γ (h.smulEquiv (DihedralGroup.sr k)) :=
  h.involutionFixedSetStar56_of_reflection_fixedVertexCount_eq_56 k
    (h.fixedVertexCount_reflection_eq_56_of_raw_action k)

/-- Raw action gives a Prop-level explicit `K_{1,55}` witness for every
reflection. -/
theorem nonempty_involutionK155_of_raw_action
    (k : ZMod 19) :
    Nonempty (InvolutionK155 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (h.involutionFixedSetStar56_of_raw_action k).nonempty_involutionK155

/-- Raw action gives the fixed-star count abstraction for every reflection. -/
theorem nonempty_involutionFixedStar55_of_raw_action
    (k : ZMod 19) :
    Nonempty (InvolutionFixedStar55 Γ (h.smulEquiv (DihedralGroup.sr k))) :=
  (h.involutionFixedSetStar56_of_raw_action k).nonempty_involutionFixedStar55
    h.isMoore

/-- In the raw-action fixed-star situation, the center of the paper-shaped
fixed star cannot be the rotation-fixed center.  This is the local separation
needed to make the rotation-fixed center a leaf of the fixed star. -/
theorem fixedSetStarWithCenter_ne_rotationFixedCenter_of_raw_action
    (k : ZMod 19) {c : V}
    (hc : FixedSetStarWithCenter Γ (h.smulEquiv (DihedralGroup.sr k)) c) :
    c ≠ h.rotationFixedCenter := by
  intro hc_eq
  have hcenter_degree :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) = 55 := by
    have hdegree :=
      h.fixedInducedGraph_center_degree_eq_55_of_fixedSetStarWithCenter
        k (h.involutionFixedSetStar56_of_raw_action k) hc
    have hvertex :
        (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h k) =
          reflectionRotationFixedCenterVertex h k :=
      Subtype.ext hc_eq
    rw [hvertex] at hdegree
    exact hdegree
  have hleaf_degree :
      (h.fixedInducedGraph (DihedralGroup.sr k)).degree
          (reflectionRotationFixedCenterVertex h k) ≤ 1 :=
    h.reflectionFixedCenterLeafBoundary_of_raw_action.degree_le_one k
  omega

/-- Raw action gives the induced fixed-star degree package from the
paper-shaped fixed-star theorem and the center-separation fact above. -/
def reflectionFixedInducedStarDegrees_of_raw_action :
    ReflectionFixedInducedStarDegrees h :=
  h.reflectionFixedInducedStarDegrees_of_reflectionFixedSetStar56
    (fun k => h.involutionFixedSetStar56_of_raw_action k)
    (fun k _c hc => h.fixedSetStarWithCenter_ne_rotationFixedCenter_of_raw_action k hc)

/-- Raw action gives the branch-geometry fixed-star boundary for all
reflections.  The only extra check beyond the paper-shaped fixed star is that
the rotation-fixed center is a leaf, supplied by the raw fixed-center-leaf
boundary. -/
theorem reflectionFixedStarBoundary_of_raw_action :
    ReflectionFixedStarBoundary h :=
  h.reflectionFixedInducedStarDegrees_of_raw_action
    |>.toReflectionFixedStarBoundary

/-- Raw action gives the standard adjacent-moved count `112` for every
reflection. -/
theorem adjacentMovedCount_reflection_eq_112_of_raw_action
    (k : ZMod 19) :
    adjacentMovedCount Γ (h.smulEquiv (DihedralGroup.sr k)) = 112 :=
  (h.involutionFixedSetStar56_of_raw_action k).adjacentMovedCount_eq_112
    h.isMoore

end D19ActsOnMoore57

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Raw action identifies the A-fixing branch vertex with the fixed-star center
for the A-fixing reflection. -/
noncomputable def reflectionFixedStarAFixingBoundary_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h) :
    ReflectionFixedStarAFixingBoundary
      h.reflectionFixedStarBoundary_of_raw_action labeling where
  aFixing_is_center := by
    classical
    let idx := labeling.aFixingReflectionIndex
    let hStar := h.involutionFixedSetStar56_of_raw_action idx
    rcases hStar.exists_center with ⟨c, hc⟩
    have hc_is_center :
        IsReflectionFixedStarCenter h idx
          (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h idx) := by
      refine ⟨?_, ?_⟩
      · exact
          h.fixedInducedGraph_center_degree_eq_55_of_fixedSetStarWithCenter
            idx hStar hc
      · intro x hx
        exact
          h.fixedInducedGraph_noncenter_degree_le_one_of_fixedSetStarWithCenter
            idx hc x hx
    have hc_ne_u : c ≠ h.rotationFixedCenter := by
      intro hc_eq
      have hsub :
          (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h idx) =
            reflectionRotationFixedCenterVertex h idx :=
        Subtype.ext hc_eq
      exact h.reflectionFixedStarBoundary_of_raw_action.rotationFixedCenter_not_center
        idx (by simpa [hsub] using hc_is_center)
    have hc_adj_u : Γ.Adj labeling.data.toAFiberCoordinates.u c := by
      have hcu :
          Γ.Adj c h.rotationFixedCenter :=
        hc.center_adj_fixed h.rotationFixedCenter
          (by
            change h.smul (DihedralGroup.sr idx) h.rotationFixedCenter =
              h.rotationFixedCenter
            exact h.reflection_smul_rotationFixedCenter idx)
          hc_ne_u.symm
      simpa [BranchOrbitABCFromCenter.toAFiberCoordinates_u,
        labeling.data.u_eq_rotationFixedCenter] using hcu.symm
    have hc_fixed :
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex 0)) c = c := by
      simpa [idx, BranchOrbitABCReflectionLabeling.midpointReflectionIndex] using
        hc.center_fixed
    have hc_eq_a0 :
        c = labeling.data.toAFiberCoordinates.a (0 + 0) :=
      labeling.midpoint_fixed_center_neighbor_eq_middle_of_fixedCenterLeaf
        h.reflectionFixedCenterLeafBoundary_of_raw_action 0 hc_adj_u hc_fixed
    have hsub :
        (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h idx) =
          labeling.aFixingFixedVertex :=
      Subtype.ext (by
        simpa [BranchOrbitABCReflectionLabeling.aFixingFixedVertex,
          BranchOrbitABCFromCenter.toAFiberCoordinates_a] using hc_eq_a0)
    simpa [idx, hsub] using hc_is_center

/-- Raw action identifies each midpoint middle A-branch vertex with the
fixed-star center for the corresponding midpoint reflection. -/
noncomputable def reflectionFixedStarMiddleBoundary_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h) :
    ReflectionFixedStarMiddleBoundary
      h.reflectionFixedStarBoundary_of_raw_action labeling where
  midpointMiddle_is_center := by
    classical
    intro m _hm
    let idx := labeling.midpointReflectionIndex m
    let hStar := h.involutionFixedSetStar56_of_raw_action idx
    rcases hStar.exists_center with ⟨c, hc⟩
    have hc_is_center :
        IsReflectionFixedStarCenter h idx
          (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h idx) := by
      refine ⟨?_, ?_⟩
      · exact
          h.fixedInducedGraph_center_degree_eq_55_of_fixedSetStarWithCenter
            idx hStar hc
      · intro x hx
        exact
          h.fixedInducedGraph_noncenter_degree_le_one_of_fixedSetStarWithCenter
            idx hc x hx
    have hc_ne_u : c ≠ h.rotationFixedCenter := by
      intro hc_eq
      have hsub :
          (⟨c, hc.center_fixed⟩ : reflectionFixedVertex h idx) =
            reflectionRotationFixedCenterVertex h idx :=
        Subtype.ext hc_eq
      exact h.reflectionFixedStarBoundary_of_raw_action.rotationFixedCenter_not_center
        idx (by simpa [hsub] using hc_is_center)
    have hc_adj_u : Γ.Adj labeling.data.toAFiberCoordinates.u c := by
      have hcu :
          Γ.Adj c h.rotationFixedCenter :=
        hc.center_adj_fixed h.rotationFixedCenter
          (by
            change h.smul (DihedralGroup.sr idx) h.rotationFixedCenter =
              h.rotationFixedCenter
            exact h.reflection_smul_rotationFixedCenter idx)
          hc_ne_u.symm
      simpa [BranchOrbitABCFromCenter.toAFiberCoordinates_u,
        labeling.data.u_eq_rotationFixedCenter] using hcu.symm
    have hc_fixed :
        h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m)) c = c := by
      simpa [idx] using hc.center_fixed
    have hc_eq_middle :
        c = labeling.data.toAFiberCoordinates.a (0 + m) :=
      labeling.midpoint_fixed_center_neighbor_eq_middle_of_fixedCenterLeaf
        h.reflectionFixedCenterLeafBoundary_of_raw_action m hc_adj_u hc_fixed
    have hsub :
        (⟨c, hc.center_fixed⟩ :
          reflectionFixedVertex h (labeling.midpointReflectionIndex m)) =
          labeling.midpointMiddleFixedVertex m :=
      Subtype.ext (by
        simpa [BranchOrbitABCReflectionLabeling.midpointMiddleFixedVertex]
          using hc_eq_middle)
    simpa [idx, hsub] using hc_is_center

/-- With the raw fixed-star boundary available, the middle-star identification
is enough to produce the two-point midpoint moving support boundary. -/
noncomputable def midpointMiddleSupportCardTwoBoundary_of_raw_action_middle
    (labeling : BranchOrbitABCReflectionLabeling h)
    (middle :
      ReflectionFixedStarMiddleBoundary
        h.reflectionFixedStarBoundary_of_raw_action labeling) :
    MidpointMiddleSupportCardTwoBoundary labeling :=
  middle.toMidpointMiddleFixedNeighborCardBoundary
    |>.toMidpointMiddleSupportCardTwoBoundary

/-- Raw action supplies the two-point midpoint moving support boundary for any
reflection-compatible branch labeling. -/
noncomputable def midpointMiddleSupportCardTwoBoundary_of_raw_action
    (labeling : BranchOrbitABCReflectionLabeling h) :
    MidpointMiddleSupportCardTwoBoundary labeling :=
  labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action_middle
    (labeling.reflectionFixedStarMiddleBoundary_of_raw_action)

/-- Raw-action fixed-star spelling of the reference matching pipeline: the
midpoint support-card-two and reference-to-midpoint fields are obtained from
the fixed-star middle identification and vertex-fixed reference solutions. -/
noncomputable def referenceMatchingPipelineBoundary_of_raw_action_fixedStar
    (labeling : BranchOrbitABCReflectionLabeling h)
    (middle :
      ReflectionFixedStarMiddleBoundary
        h.reflectionFixedStarBoundary_of_raw_action labeling)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling) :
    ReferenceMatchingPipelineBoundary labeling :=
  (FixedStarReferenceMatchingPipelineBoundary.of_vertexFixed
    (star := h.reflectionFixedStarBoundary_of_raw_action)
    middle referenceSolutionVertexFixed).toReferenceMatchingPipelineBoundary

/-- Raw-action reference matching pipeline from the remaining vertex-fixed
reference-solution geometry. -/
noncomputable def referenceMatchingPipelineBoundary_of_raw_action_vertexFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling) :
    ReferenceMatchingPipelineBoundary labeling :=
  labeling.referenceMatchingPipelineBoundary_of_raw_action_fixedStar
    labeling.reflectionFixedStarMiddleBoundary_of_raw_action
    referenceSolutionVertexFixed

/-- Raw-action fixed-star constructor for the reference-fiber matching equation.
The remaining geometric inputs are now the middle-star identification,
vertex-fixed reference solutions, and midpoint-exception disjointness. -/
noncomputable def referenceFiberMatchingEquationFrontierBoundary_of_raw_action_fixedStar
    (labeling : BranchOrbitABCReflectionLabeling h)
    (middle :
      ReflectionFixedStarMiddleBoundary
        h.reflectionFixedStarBoundary_of_raw_action labeling)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (midpointExceptionDisjoint :
      MidpointExceptionDisjointAFixingSupportBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action
    (labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action_middle middle)
    ((ReferenceRotationToMidpointReflectionBoundary.of_aFixingFixed
      (referenceSolutionVertexFixed.toReferenceRotationEquationAFixingFixedBoundary)))
    midpointExceptionDisjoint

/-- Raw-action reference-fiber matching-equation frontier from vertex-fixed
reference solutions and midpoint-exception disjointness. -/
noncomputable def referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (midpointExceptionDisjoint :
      MidpointExceptionDisjointAFixingSupportBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_fixedStar
    labeling.reflectionFixedStarMiddleBoundary_of_raw_action
    referenceSolutionVertexFixed midpointExceptionDisjoint

/-- Raw-action fixed-star constructor for the reference-fiber matching equation.
The remaining geometric inputs are now the middle-star identification,
vertex-fixed reference solutions, and midpoint-exception disjointness. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_fixedStar
    (labeling : BranchOrbitABCReflectionLabeling h)
    (middle :
      ReflectionFixedStarMiddleBoundary
        h.reflectionFixedStarBoundary_of_raw_action labeling)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
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
        2 :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_fixedStar
    middle referenceSolutionVertexFixed midpointExceptionDisjoint
    |>.toReferenceFiberMatchingEquationCardTwo

/-- Raw-action reference-fiber matching equation from vertex-fixed reference
solutions and midpoint-exception disjointness. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_vertexFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
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
        2 :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed
    referenceSolutionVertexFixed midpointExceptionDisjoint
    |>.toReferenceFiberMatchingEquationCardTwo

/-- Raw-action disjointness constructor for midpoint exceptions: the raw
fixed-star/A-fixing support-size boundary reduces disjointness to the one-point
exclusion and the all-endpoint-adjacency obstruction. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_noCardOne_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  let supportCard :=
    labeling.reflectionFixedStarAFixingBoundary_of_raw_action
      |>.toAFixingReflectionFixedNeighborCardBoundary
  let noCardTwo :=
    noAllEndpointAdj.toMidpointExceptionAFixingSupportNoCardTwoBoundary
      labeling.midpointReflectionCriterionBoundary_of_raw_action
  (noCardTwo.toMidpointExceptionAFixingSupportCaseBoundary
    supportCard no_card_one).toMidpointExceptionDisjointAFixingSupportBoundary

/-- Raw-action disjointness constructor using the singleton-fixed obstruction for
the one-point case. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_singletonFixed_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (singletonFixed :
      MidpointExceptionAFixingSupportSingletonFixedBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_noCardOne_noAllEndpointAdj
    singletonFixed.no_card_one noAllEndpointAdj

/-- Raw-action disjointness constructor using midpoint-equation invariance for
the one-point case. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_equationInvariant_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (equationInvariant :
      MidpointEquationSetAFixingInvariantBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_singletonFixed_noAllEndpointAdj
    (equationInvariant.toMidpointExceptionAFixingSupportSingletonFixedBoundary
      labeling.midpointReflectionCriterionBoundary_of_raw_action)
    noAllEndpointAdj

/-- Raw-action disjointness constructor using endpoint matching compatibility for
the one-point case. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointCoordinate_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (endpointCoordinate :
      EndpointMatchingAFixingCoordinateBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_equationInvariant_noAllEndpointAdj
    endpointCoordinate.toMidpointEquationSetAFixingInvariantBoundary
    noAllEndpointAdj

/-- Raw-action disjointness constructor using the reduced endpoint target-sign
compatibility for the one-point case. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointTargetSign_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (endpointTargetSign :
      EndpointMatchingAFixingTargetSignBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_equationInvariant_noAllEndpointAdj
    endpointTargetSign.toMidpointEquationSetAFixingInvariantBoundary
    noAllEndpointAdj

/-- Raw-action disjointness constructor using the corrected negative-endpoint
label exchange for the one-point case.  This avoids the false same-offset
target-sign route: the negative-pair exchange rules out paired singletons, and
the already-proved `d ↦ -d` transport reduces `no_card_one` to that
obstruction. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointNegativePair_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (endpointNegativePair :
      EndpointSignNegativeMatchingPairBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
  let noPaired :=
    endpointNegativePair
      |>.toMidpointExceptionAFixingSupportNoPairedSingletonBoundary criterion
  let transport :=
    labeling.midpointExceptionAFixingSupportIntersectionNegInvariantBoundary
      criterion
  let noCardOne :=
    noPaired.toMidpointExceptionAFixingSupportNoCardOneBoundary transport
  labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_noCardOne_noAllEndpointAdj
    noCardOne.no_card_one noAllEndpointAdj

/-- Raw-action disjointness constructor using the paired-adjacency form of the
corrected negative-endpoint label exchange. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointPairedAdj_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (endpointPairedAdj :
      EndpointSignPairedAdjacencyBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointNegativePair_noAllEndpointAdj
    endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary
    noAllEndpointAdj

/-- Raw-action disjointness constructor using pointwise endpoint non-adjacency
to supply both the paired-adjacency label exchange and the endpoint
non-containment input. -/
noncomputable def midpointExceptionAFixingSupportCaseBoundary_of_raw_action_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  let criterion := labeling.midpointReflectionCriterionBoundary_of_raw_action
  let supportCard :=
    labeling.reflectionFixedStarAFixingBoundary_of_raw_action
      |>.toAFixingReflectionFixedNeighborCardBoundary
  let noPaired :=
    endpointPointwiseNonadj.toEndpointSignPairedAdjacencyBoundary
      |>.toMidpointExceptionAFixingSupportNoPairedSingletonBoundary criterion
  let transport :=
    labeling.midpointExceptionAFixingSupportIntersectionNegInvariantBoundary
      criterion
  noPaired.toMidpointExceptionAFixingSupportCaseBoundary_endpointPointwiseNonadj
    transport supportCard criterion endpointPointwiseNonadj

/-- Raw-action disjointness constructor using pointwise endpoint non-adjacency
to supply the whole midpoint-exception support case boundary. -/
noncomputable def midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling :=
  (labeling.midpointExceptionAFixingSupportCaseBoundary_of_raw_action_endpointPointwiseNonadj
      endpointPointwiseNonadj)
    |>.toMidpointExceptionDisjointAFixingSupportBoundary

/-- Raw-action constructor for the lean-aware fixed-star final package after
the middle and A-fixing fixed-star fields are discharged. -/
noncomputable def leanAwareFixedStarFinalBoundary_of_raw_action_fields
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (caseBoundary : MidpointExceptionAFixingSupportCaseBoundary labeling) :
    LeanAwareFixedStarFinalBoundary h.reflectionFixedStarBoundary_of_raw_action
      labeling where
  middle := labeling.reflectionFixedStarMiddleBoundary_of_raw_action
  referenceSolutionVertexFixed := referenceSolutionVertexFixed
  midpointExceptionAFixingSupportCase := caseBoundary

/-- Raw-action lean-aware fixed-star package from the two genuine remaining
geometric inputs: reference-solution fixedness and pointwise endpoint
non-adjacency. -/
noncomputable def leanAwareFixedStarFinalBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    LeanAwareFixedStarFinalBoundary h.reflectionFixedStarBoundary_of_raw_action
      labeling :=
  labeling.leanAwareFixedStarFinalBoundary_of_raw_action_fields
    referenceSolutionVertexFixed
    (labeling.midpointExceptionAFixingSupportCaseBoundary_of_raw_action_endpointPointwiseNonadj
      endpointPointwiseNonadj)

/-- The same raw-action package, immediately converted to the fixed-star
cardinality pipeline feeding the `38` A-fiber count. -/
noncomputable def fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    FixedStarReferenceMatchingCardinalityPipelineBoundary
      h.reflectionFixedStarBoundary_of_raw_action labeling :=
  (labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj
      referenceSolutionVertexFixed endpointPointwiseNonadj)
    |>.toFixedStarReferenceMatchingCardinalityPipelineBoundary

/-- Canonical raw-action route to the exact A-fiber cardinality `38`: the upper
bound comes from the reference matching exception set, while the lower bound is
the all-fibers support-complement sum supplied by the midpoint-exception case. -/
noncomputable def aFiberCardinality38Boundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (labeling.fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj
      referenceSolutionVertexFixed endpointPointwiseNonadj)
    |>.toAFiberCardinality38Boundary

/-- Raw-action lean-aware fixed-star package from the independent
reference-to-midpoint comparison and pointwise endpoint non-adjacency.

The endpoint pointwise obstruction gives the finite midpoint-exception case
boundary.  Together with the raw-action reference matching pipeline, that case
boundary also supplies the reference-solution fixedness field internally. -/
noncomputable def leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    LeanAwareFixedStarFinalBoundary h.reflectionFixedStarBoundary_of_raw_action
      labeling :=
  let caseBoundary :=
    labeling.midpointExceptionAFixingSupportCaseBoundary_of_raw_action_endpointPointwiseNonadj
      endpointPointwiseNonadj
  LeanAwareFixedStarFinalBoundary.of_referenceMatching_aFixingCenter_cases
    labeling.reflectionFixedStarMiddleBoundary_of_raw_action
    labeling.reflectionFixedStarAFixingBoundary_of_raw_action
    (labeling.referenceMatchingPipelineBoundary_of_raw_action
      labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
      referenceToMidpoint)
    caseBoundary

/-- Fixed-star cardinality pipeline from the reference-to-midpoint comparison
and endpoint pointwise obstruction. -/
noncomputable def fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    FixedStarReferenceMatchingCardinalityPipelineBoundary
      h.reflectionFixedStarBoundary_of_raw_action labeling :=
  (labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      referenceToMidpoint endpointPointwiseNonadj)
    |>.toFixedStarReferenceMatchingCardinalityPipelineBoundary

/-- Raw-action route to the exact A-fiber cardinality `38` from the independent
reference-to-midpoint comparison and endpoint pointwise obstruction. -/
noncomputable def aFiberCardinality38Boundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (labeling.fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      referenceToMidpoint endpointPointwiseNonadj)
    |>.toAFiberCardinality38Boundary

/-- Raw-action route from the independent reference-to-midpoint comparison and
pointwise endpoint obstruction to reference-solution fixedness. -/
noncomputable def referenceRotationMatchingSolutionVertexFixedBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    ReferenceRotationMatchingSolutionVertexFixedBoundary labeling :=
  let caseBoundary :=
    labeling.midpointExceptionAFixingSupportCaseBoundary_of_raw_action_endpointPointwiseNonadj
      endpointPointwiseNonadj
  caseBoundary.toReferenceRotationMatchingSolutionVertexFixedBoundary
    (labeling.referenceMatchingPipelineBoundary_of_raw_action
      labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
      referenceToMidpoint)

/-- Raw-action lean-aware fixed-star package from reference-to-midpoint and the
single-endpoint common-neighbor boundary. -/
noncomputable def leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointCommonNeighborBasic :
      MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling) :
    LeanAwareFixedStarFinalBoundary h.reflectionFixedStarBoundary_of_raw_action
      labeling :=
  labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    referenceToMidpoint
    endpointCommonNeighborBasic.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- Raw-action `38` route from reference-to-midpoint and the single-endpoint
common-neighbor boundary. -/
noncomputable def aFiberCardinality38Boundary_of_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointCommonNeighborBasic :
      MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling) :
    AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointCommonNeighborBasic
      referenceToMidpoint endpointCommonNeighborBasic)
    |>.toFixedStarReferenceMatchingCardinalityPipelineBoundary
    |>.toAFiberCardinality38Boundary

/-- Raw-action lean-aware fixed-star package from reference-to-midpoint and
the endpoint-reference exchange common-neighbor boundary. -/
noncomputable def leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointExchange :
      EndpointReferenceExchangeCommonNeighborBoundary labeling) :
    LeanAwareFixedStarFinalBoundary h.reflectionFixedStarBoundary_of_raw_action
      labeling :=
  labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    referenceToMidpoint
    endpointExchange.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

/-- Raw-action `38` route from reference-to-midpoint and the endpoint-reference
exchange common-neighbor boundary. -/
noncomputable def aFiberCardinality38Boundary_of_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointExchange :
      EndpointReferenceExchangeCommonNeighborBoundary labeling) :
    AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointExchangeCommonNeighbor
      referenceToMidpoint endpointExchange)
    |>.toFixedStarReferenceMatchingCardinalityPipelineBoundary
    |>.toAFiberCardinality38Boundary

/-- Raw-action lean-aware fixed-star package from reference-to-midpoint and the
no-reflected-reference negative matching diagnostic. -/
noncomputable def leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointNoReflectedReferenceNegMatching :
      EndpointSignNoReflectedReferenceNegMatchingBoundary labeling) :
    LeanAwareFixedStarFinalBoundary h.reflectionFixedStarBoundary_of_raw_action
      labeling :=
  labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    referenceToMidpoint
    (endpointNoReflectedReferenceNegMatching
      |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary)

/-- Raw-action `38` route from reference-to-midpoint and the no-reflected
negative matching diagnostic. -/
noncomputable def aFiberCardinality38Boundary_of_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointNoReflectedReferenceNegMatching :
      EndpointSignNoReflectedReferenceNegMatchingBoundary labeling) :
    AFiberCardinality38Boundary h labeling.data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (labeling.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointNoReflectedReferenceNegMatching
      referenceToMidpoint endpointNoReflectedReferenceNegMatching)
    |>.toFixedStarReferenceMatchingCardinalityPipelineBoundary
    |>.toAFiberCardinality38Boundary

/-- Raw-action reference-fiber matching-equation frontier after reducing
midpoint-exception disjointness to the one-point and endpoint-adjacency
exclusions. -/
noncomputable def referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed
    referenceSolutionVertexFixed
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_noCardOne_noAllEndpointAdj
      no_card_one noAllEndpointAdj)

/-- Raw-action reference-fiber matching equation after reducing disjointness to
the one-point and endpoint-adjacency exclusions. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_vertexFixed_noAllEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
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
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed_noAllEndpointAdj
    referenceSolutionVertexFixed no_card_one noAllEndpointAdj
    |>.toReferenceFiberMatchingEquationCardTwo

/-- Raw-action reference-fiber matching-equation frontier with the one-point
case supplied by singleton-fixedness. -/
noncomputable def
    referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed_singletonFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (singletonFixed :
      MidpointExceptionAFixingSupportSingletonFixedBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed
    referenceSolutionVertexFixed
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_singletonFixed_noAllEndpointAdj
      singletonFixed noAllEndpointAdj)

/-- Raw-action reference-fiber matching equation with the one-point case supplied
by singleton-fixedness. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_vertexFixed_singletonFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceSolutionVertexFixed :
      ReferenceRotationMatchingSolutionVertexFixedBoundary labeling)
    (singletonFixed :
      MidpointExceptionAFixingSupportSingletonFixedBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
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
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_vertexFixed_singletonFixed
    referenceSolutionVertexFixed singletonFixed noAllEndpointAdj
    |>.toReferenceFiberMatchingEquationCardTwo

/-- Raw-action reference-fiber matching-equation frontier from an independent
reference-to-midpoint comparison and endpoint target-sign compatibility. -/
noncomputable def
    referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointTargetSign
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointTargetSign :
      EndpointMatchingAFixingTargetSignBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action
    labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
    referenceToMidpoint
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointTargetSign_noAllEndpointAdj
      endpointTargetSign noAllEndpointAdj)

/-- Raw-action reference-fiber matching equation from an independent
reference-to-midpoint comparison and endpoint target-sign compatibility. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_referenceToMidpoint_endpointTargetSign
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointTargetSign :
      EndpointMatchingAFixingTargetSignBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
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
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointTargetSign
    referenceToMidpoint endpointTargetSign noAllEndpointAdj
    |>.toReferenceFiberMatchingEquationCardTwo

/-- Raw-action reference-fiber matching-equation frontier from an independent
reference-to-midpoint comparison and the corrected negative-endpoint label
exchange. -/
noncomputable def
    referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointNegativePair
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointNegativePair :
      EndpointSignNegativeMatchingPairBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action
    labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
    referenceToMidpoint
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointNegativePair_noAllEndpointAdj
      endpointNegativePair noAllEndpointAdj)

/-- Raw-action reference-fiber matching equation from an independent
reference-to-midpoint comparison and the corrected negative-endpoint label
exchange. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_referenceToMidpoint_endpointNegativePair
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointNegativePair :
      EndpointSignNegativeMatchingPairBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
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
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointNegativePair
    referenceToMidpoint endpointNegativePair noAllEndpointAdj
    |>.toReferenceFiberMatchingEquationCardTwo

/-- Raw-action reference-fiber matching-equation frontier from an independent
reference-to-midpoint comparison and the paired-adjacency form of the corrected
negative-endpoint label exchange. -/
noncomputable def
    referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointPairedAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPairedAdj :
      EndpointSignPairedAdjacencyBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointNegativePair
    referenceToMidpoint
    endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary
    noAllEndpointAdj

/-- Raw-action reference-fiber matching equation from an independent
reference-to-midpoint comparison and paired endpoint adjacency. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_referenceToMidpoint_endpointPairedAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPairedAdj :
      EndpointSignPairedAdjacencyBoundary labeling)
    (noAllEndpointAdj :
      MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling) :
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
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointPairedAdj
    referenceToMidpoint endpointPairedAdj noAllEndpointAdj
    |>.toReferenceFiberMatchingEquationCardTwo

/-- Raw-action reference-fiber matching-equation frontier from an independent
reference-to-midpoint comparison and pointwise endpoint non-adjacency.  The
pointwise endpoint obstruction supplies both paired endpoint adjacency and the
single-offset endpoint obstruction. -/
noncomputable def
    referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    ReferenceFiberMatchingEquationFrontierBoundary labeling :=
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action
    labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
    referenceToMidpoint
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointPointwiseNonadj
      endpointPointwiseNonadj)

/-- Raw-action reference-fiber matching equation from an independent
reference-to-midpoint comparison and pointwise endpoint non-adjacency. -/
theorem referenceFiberMatchingEquationCardTwo_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (referenceToMidpoint :
      ReferenceRotationToMidpointReflectionBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
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
  labeling.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
    referenceToMidpoint endpointPointwiseNonadj
    |>.toReferenceFiberMatchingEquationCardTwo

end BranchOrbitABCReflectionLabeling

namespace D19ActsOnMoore57

variable {h : D19ActsOnMoore57 V Γ}

/-- Default-base raw-action constructor for the lean-aware fixed-star final
package.  Raw action supplies the fixed star and middle fields; the remaining
inputs are exactly reference-solution fixedness and the pointwise endpoint
obstruction. -/
noncomputable def
    leanAwareFixedStarFinalBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      h.reflectionFixedStarBoundary_of_raw_action
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
    |>.leanAwareFixedStarFinalBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj
      referenceSolutionVertexFixed endpointPointwiseNonadj

/-- Default-base raw-action route to the fixed-star cardinality pipeline from
the two remaining geometric inputs. -/
noncomputable def
    fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
      h.reflectionFixedStarBoundary_of_raw_action
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (h.leanAwareFixedStarFinalBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj_fields
      k referenceSolutionVertexFixed endpointPointwiseNonadj)
    |>.toFixedStarReferenceMatchingCardinalityPipelineBoundary

/-- Default-base raw-action route to the exact A-fiber cardinality `38` from
reference-solution fixedness and the pointwise endpoint obstruction. -/
noncomputable def
    aFiberCardinality38Boundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    AFiberCardinality38Boundary h
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (h.fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceVertexFixed_endpointPointwiseNonadj_fields
      k referenceSolutionVertexFixed endpointPointwiseNonadj)
    |>.toAFiberCardinality38Boundary

/-- Default-base raw-action constructor for the lean-aware fixed-star final
package from reference-to-midpoint comparison and pointwise endpoint
non-adjacency. -/
noncomputable def
    leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    BranchOrbitABCReflectionLabeling.LeanAwareFixedStarFinalBoundary
      h.reflectionFixedStarBoundary_of_raw_action
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
    |>.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      referenceToMidpoint endpointPointwiseNonadj

/-- Default-base raw-action route to the fixed-star cardinality pipeline from
reference-to-midpoint comparison and pointwise endpoint non-adjacency. -/
noncomputable def
    fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    BranchOrbitABCReflectionLabeling.FixedStarReferenceMatchingCardinalityPipelineBoundary
      h.reflectionFixedStarBoundary_of_raw_action
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (h.leanAwareFixedStarFinalBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
      k referenceToMidpoint endpointPointwiseNonadj)
    |>.toFixedStarReferenceMatchingCardinalityPipelineBoundary

/-- Default-base raw-action route to the exact A-fiber cardinality `38` from
reference-to-midpoint comparison and pointwise endpoint non-adjacency. -/
noncomputable def
    aFiberCardinality38Boundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    AFiberCardinality38Boundary h
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k).data.toAFiberCoordinates
      (Finset.univ : Finset (ZMod 19)) :=
  (h.fixedStarReferenceMatchingCardinalityPipelineBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
      k referenceToMidpoint endpointPointwiseNonadj)
    |>.toAFiberCardinality38Boundary

/-- Default-base raw-action route from reference-to-midpoint comparison and
pointwise endpoint non-adjacency to reference-solution fixedness. -/
noncomputable def
    referenceRotationMatchingSolutionVertexFixedBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
      (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k) :=
  (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
    |>.referenceRotationMatchingSolutionVertexFixedBoundary_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj
      referenceToMidpoint endpointPointwiseNonadj

/-- Default-base raw-action constructor using fixed-star middle and
vertex-fixed reference-solution geometry instead of the more algebraic
midpoint/reference pipeline fields. -/
noncomputable def remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_fields
    (k : ZMod 19)
    (middle :
      BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
        h.reflectionFixedStarBoundary_of_raw_action
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (midpointExceptionDisjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedCenterLeafReferenceConnector_of_raw_action k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.referenceMatchingPipelineBoundary_of_raw_action_fixedStar
        middle referenceSolutionVertexFixed)
    midpointExceptionDisjoint

/-- Default-base raw-action constructor after discharging the fixed-star middle
field.  The remaining inputs are the vertex-fixed reference solution and the
midpoint-exception disjointness. -/
noncomputable def remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_vertexFixed_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (midpointExceptionDisjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_fields k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.reflectionFixedStarMiddleBoundary_of_raw_action)
    referenceSolutionVertexFixed midpointExceptionDisjoint

/-- Public labeled-reflection matching connector from the same fixed-star
geometric fields. -/
theorem remainingLabeledReflectionMatchingEquationConnector_of_raw_action_fixedStar_fields
    (k : ZMod 19)
    (middle :
      BranchOrbitABCReflectionLabeling.ReflectionFixedStarMiddleBoundary
        h.reflectionFixedStarBoundary_of_raw_action
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (midpointExceptionDisjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.referenceFiberMatchingEquationFrontierBoundary_of_raw_action_fixedStar
        middle referenceSolutionVertexFixed midpointExceptionDisjoint
      |>.toReferenceFiberMatchingEquationCardTwoOfPair
        (h.fixedCenterLeafDefaultBasePair_of_raw_action k))

/-- Public labeled-reflection matching connector after discharging the fixed-star
middle field from raw action. -/
theorem remainingLabeledReflectionMatchingEquationConnector_of_raw_action_vertexFixed_fields
    (k : ZMod 19)
    (referenceSolutionVertexFixed :
      BranchOrbitABCReflectionLabeling.ReferenceRotationMatchingSolutionVertexFixedBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (midpointExceptionDisjoint :
      BranchOrbitABCReflectionLabeling.MidpointExceptionDisjointAFixingSupportBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_fixedStar_fields k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.reflectionFixedStarMiddleBoundary_of_raw_action)
    referenceSolutionVertexFixed midpointExceptionDisjoint

/-- Default-base raw-action constructor after also reducing midpoint-exception
disjointness to the one-point and endpoint-adjacency exclusions. -/
noncomputable def
    remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_vertexFixed_noAllEndpointAdj_fields
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
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_vertexFixed_fields k
    referenceSolutionVertexFixed
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_noCardOne_noAllEndpointAdj
        no_card_one noAllEndpointAdj)

/-- Public labeled-reflection matching connector after reducing both
fixed-star-middle and midpoint-exception disjointness from raw action. -/
theorem
    remainingLabeledReflectionMatchingEquationConnector_of_raw_action_vertexFixed_noAllEndpointAdj_fields
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
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_vertexFixed_fields k
    referenceSolutionVertexFixed
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_noCardOne_noAllEndpointAdj
        no_card_one noAllEndpointAdj)

/-- Default-base raw-action constructor with the one-point exception case
supplied by singleton-fixedness. -/
noncomputable def
    remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_vertexFixed_singletonFixed_fields
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
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_vertexFixed_fields k
    referenceSolutionVertexFixed
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_singletonFixed_noAllEndpointAdj
        singletonFixed noAllEndpointAdj)

/-- Public labeled-reflection matching connector with the one-point exception
case supplied by singleton-fixedness. -/
theorem
    remainingLabeledReflectionMatchingEquationConnector_of_raw_action_vertexFixed_singletonFixed_fields
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
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_vertexFixed_fields k
    referenceSolutionVertexFixed
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_singletonFixed_noAllEndpointAdj
        singletonFixed noAllEndpointAdj)

/-- Default-base raw-action constructor from an independent
reference-to-midpoint comparison and endpoint target-sign compatibility. -/
noncomputable def
    remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointTargetSign_fields
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
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedCenterLeafReferenceConnector_of_raw_action_fields k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointMiddleSupportCardTwoBoundary_of_raw_action)
    referenceToMidpoint
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointTargetSign_noAllEndpointAdj
        endpointTargetSign noAllEndpointAdj)

/-- Public labeled-reflection matching connector from an independent
reference-to-midpoint comparison and endpoint target-sign compatibility. -/
theorem
    remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointTargetSign_fields
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
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_fields k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointMiddleSupportCardTwoBoundary_of_raw_action)
    referenceToMidpoint
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointTargetSign_noAllEndpointAdj
        endpointTargetSign noAllEndpointAdj)

/-- Default-base raw-action constructor from an independent
reference-to-midpoint comparison and the corrected negative-endpoint label
exchange. -/
noncomputable def
    remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
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
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedCenterLeafReferenceConnector_of_raw_action_fields k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointMiddleSupportCardTwoBoundary_of_raw_action)
    referenceToMidpoint
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointNegativePair_noAllEndpointAdj
        endpointNegativePair noAllEndpointAdj)

/-- Public labeled-reflection matching connector from an independent
reference-to-midpoint comparison and the corrected negative-endpoint label
exchange. -/
theorem
    remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
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
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_fields k
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointMiddleSupportCardTwoBoundary_of_raw_action)
    referenceToMidpoint
    ((h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)
      |>.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointNegativePair_noAllEndpointAdj
        endpointNegativePair noAllEndpointAdj)

/-- Default-base raw-action constructor from an independent
reference-to-midpoint comparison and paired endpoint adjacency. -/
noncomputable def
    remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointPairedAdj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPairedAdj :
      BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  h.remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
    k referenceToMidpoint
    endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary
    noAllEndpointAdj

/-- Public labeled-reflection matching connector from an independent
reference-to-midpoint comparison and paired endpoint adjacency. -/
theorem
    remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointPairedAdj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPairedAdj :
      BranchOrbitABCReflectionLabeling.EndpointSignPairedAdjacencyBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (noAllEndpointAdj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointNegativePair_fields
    k referenceToMidpoint
    endpointPairedAdj.toEndpointSignNegativeMatchingPairBoundary
    noAllEndpointAdj

/-- Default-base raw-action constructor from an independent
reference-to-midpoint comparison and pointwise endpoint non-adjacency.  The
endpoint pointwise obstruction supplies both endpoint inputs required by the
paired-adjacency route. -/
noncomputable def
    remainingDefaultBaseFixedStarReferenceConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingDefaultBaseFixedCenterLeafReferenceConnector h :=
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  h.remainingDefaultBaseFixedCenterLeafReferenceConnector_of_raw_action_fields k
    labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
    referenceToMidpoint
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointPointwiseNonadj
      endpointPointwiseNonadj)

/-- Public labeled-reflection matching connector from an independent
reference-to-midpoint comparison and pointwise endpoint non-adjacency. -/
theorem
    remainingLabeledReflectionMatchingEquationConnector_of_raw_action_referenceToMidpoint_endpointPointwiseNonadj_fields
    (k : ZMod 19)
    (referenceToMidpoint :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k))
    (endpointPointwiseNonadj :
      BranchOrbitABCReflectionLabeling.MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        (h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k)) :
    RemainingLabeledReflectionMatchingEquationConnector h :=
  let labeling := h.fixedCenterLeafDefaultBaseLabeling_of_raw_action k
  h.remainingLabeledReflectionMatchingEquationConnector_of_raw_action_fields k
    labeling.midpointMiddleSupportCardTwoBoundary_of_raw_action
    referenceToMidpoint
    (labeling.midpointExceptionDisjointAFixingSupportBoundary_of_raw_action_endpointPointwiseNonadj
      endpointPointwiseNonadj)

end D19ActsOnMoore57

end

end Moore57
