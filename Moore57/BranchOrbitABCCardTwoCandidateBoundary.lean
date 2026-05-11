import Moore57.BranchOrbitABCCardTwoGapSummaryBoundary
import Moore57.Foundations.ZMod19.AvoidanceBoundary
import Moore57.BranchOrbitABCSupportPairVertexBoundary
import Moore57.BranchOrbitABCSupportPairEndpointMatchingBoundary

/-!
# Named candidate vertices for the card-two gap

This file strengthens `BranchOrbitABCCardTwoGapSummaryBoundary` by naming the
candidate non-adjacent endpoint pair and the two candidate common neighbors.
The remaining coordinate construction is kept as adjacency/nonadjacency/
distinctness fields.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Two offsets, both nonzero and avoiding a prescribed nonzero offset. -/
theorem exists_cardTwoCandidateOffsetPair
    (d : ZMod 19) (hd : d ≠ 0) :
    ∃ kl : ZMod 19 × ZMod 19,
      kl.1 ≠ 0 ∧ kl.2 ≠ 0 ∧ kl.1 ≠ d ∧ kl.2 ≠ d ∧ kl.1 ≠ kl.2 := by
  rcases zmod19_card_two_avoidance_witnesses d hd with
    ⟨k, l, hk, hl, hkd, hld, hkl⟩
  exact ⟨(k, l), hk, hl, hkd, hld, hkl⟩

/-- The ordered pair of candidate offsets used for the two common-neighbor
vertices. -/
noncomputable def cardTwoCandidateOffsetPair
    (d : ZMod 19) (hd : d ≠ 0) : ZMod 19 × ZMod 19 :=
  Classical.choose (exists_cardTwoCandidateOffsetPair d hd)

theorem cardTwoCandidateOffsetPair_spec
    (d : ZMod 19) (hd : d ≠ 0) :
    (cardTwoCandidateOffsetPair d hd).1 ≠ 0 ∧
      (cardTwoCandidateOffsetPair d hd).2 ≠ 0 ∧
      (cardTwoCandidateOffsetPair d hd).1 ≠ d ∧
      (cardTwoCandidateOffsetPair d hd).2 ≠ d ∧
      (cardTwoCandidateOffsetPair d hd).1 ≠
        (cardTwoCandidateOffsetPair d hd).2 :=
  Classical.choose_spec (exists_cardTwoCandidateOffsetPair d hd)

/-- The first candidate common-neighbor offset. -/
noncomputable def cardTwoFirstCandidateOffset
    (d : ZMod 19) (hd : d ≠ 0) : ZMod 19 :=
  (cardTwoCandidateOffsetPair d hd).1

/-- The second candidate common-neighbor offset. -/
noncomputable def cardTwoSecondCandidateOffset
    (d : ZMod 19) (hd : d ≠ 0) : ZMod 19 :=
  (cardTwoCandidateOffsetPair d hd).2

theorem cardTwoFirstCandidateOffset_ne_zero
    (d : ZMod 19) (hd : d ≠ 0) :
    cardTwoFirstCandidateOffset d hd ≠ 0 :=
  (cardTwoCandidateOffsetPair_spec d hd).1

theorem cardTwoSecondCandidateOffset_ne_zero
    (d : ZMod 19) (hd : d ≠ 0) :
    cardTwoSecondCandidateOffset d hd ≠ 0 :=
  (cardTwoCandidateOffsetPair_spec d hd).2.1

theorem cardTwoFirstCandidateOffset_ne
    (d : ZMod 19) (hd : d ≠ 0) :
    cardTwoFirstCandidateOffset d hd ≠ d :=
  (cardTwoCandidateOffsetPair_spec d hd).2.2.1

theorem cardTwoSecondCandidateOffset_ne
    (d : ZMod 19) (hd : d ≠ 0) :
    cardTwoSecondCandidateOffset d hd ≠ d :=
  (cardTwoCandidateOffsetPair_spec d hd).2.2.2.1

theorem cardTwoFirstCandidateOffset_ne_second
    (d : ZMod 19) (hd : d ≠ 0) :
    cardTwoFirstCandidateOffset d hd ≠ cardTwoSecondCandidateOffset d hd :=
  (cardTwoCandidateOffsetPair_spec d hd).2.2.2.2

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Pair endpoint adjacency in the exact shape used by the card-two gap. -/
def cardTwoPairEndpointAdj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) : Prop :=
  Γ.Adj
    (labeling.endpointCommonNeighborReferenceVertex p)
    (labeling.endpointCommonNeighborReflectedEndpointVertex d p) ∧
  Γ.Adj
    (labeling.endpointCommonNeighborReferenceVertex
      (labeling.aFiberReflectionCoordPerm p))
    (labeling.endpointCommonNeighborReflectedEndpointVertex d
      (labeling.aFiberReflectionCoordPerm p))

/-- The left endpoint of the named non-adjacent candidate pair. -/
def cardTwoCandidateLeftEndpointVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  labeling.endpointCommonNeighborReferenceVertex p

/-- The right endpoint of the named non-adjacent candidate pair.  It is the
same-coordinate rotated endpoint, not the A-reflected target from the endpoint
adjacency hypothesis. -/
def cardTwoCandidateRightEndpointVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord (0 + d)
      (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a (0 + d))}) : V)

/-- Candidate common-neighbor vertex obtained as the matching mate of the left
endpoint in the A-fiber over `0 + k`. -/
def cardTwoCandidateCommonNeighborVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (k : ZMod 19) (hk : k ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord (0 + k)
      (AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + k)
        (index_ne_add_of_ne_zero hk) p) :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a (0 + k))}) : V)

/-- The first named candidate common neighbor. -/
def cardTwoFirstCandidateCommonNeighborVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  labeling.cardTwoCandidateCommonNeighborVertex
    (cardTwoFirstCandidateOffset d hd)
    (cardTwoFirstCandidateOffset_ne_zero d hd) p

/-- The second named candidate common neighbor. -/
def cardTwoSecondCandidateCommonNeighborVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  labeling.cardTwoCandidateCommonNeighborVertex
    (cardTwoSecondCandidateOffset d hd)
    (cardTwoSecondCandidateOffset_ne_zero d hd) p

/-- The generic candidate common neighbor is adjacent to the left endpoint by
definition of the branch-fiber matching. -/
theorem cardTwoCandidateCommonNeighbor_adj_left
    (labeling : BranchOrbitABCReflectionLabeling h)
    (k : ZMod 19) (hk : k ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    Γ.Adj
      (labeling.cardTwoCandidateLeftEndpointVertex p)
      (labeling.cardTwoCandidateCommonNeighborVertex k hk p) := by
  simpa [cardTwoCandidateLeftEndpointVertex,
    cardTwoCandidateCommonNeighborVertex,
    endpointCommonNeighborReferenceVertex] using
    (AFiberCoordinates.adj_coord_matchingEquiv
      (hΓ := h.isMoore)
      (coords := labeling.data.toAFiberCoordinates)
      (i := 0) (j := 0 + k)
      (hij := index_ne_add_of_ne_zero hk) p)

/-- The named endpoint pair lies in distinct A-fibers, hence has distinct
underlying vertices. -/
theorem cardTwoCandidateEndpoints_ne
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    labeling.cardTwoCandidateLeftEndpointVertex p ≠
      labeling.cardTwoCandidateRightEndpointVertex d p := by
  intro hxy
  let coords := labeling.data.toAFiberCoordinates
  have hxmem :
      labeling.cardTwoCandidateLeftEndpointVertex p ∈
        branchFiber Γ coords.u (coords.a 0) := by
    simpa [cardTwoCandidateLeftEndpointVertex,
      endpointCommonNeighborReferenceVertex, coords] using
      coords.coord_mem 0 p
  have hybranch :
      Γ.Adj (coords.a (0 + d))
        (labeling.cardTwoCandidateRightEndpointVertex d p) := by
    have hymem :
        labeling.cardTwoCandidateRightEndpointVertex d p ∈
          branchFiber Γ coords.u (coords.a (0 + d)) := by
      simpa [cardTwoCandidateRightEndpointVertex, coords] using
        coords.coord_mem (0 + d)
          (labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p)
    exact (mem_branchFiber.mp hymem).2
  have hx_adj_target :
      Γ.Adj (labeling.cardTwoCandidateLeftEndpointVertex p)
        (coords.a (0 + d)) := by
    simpa [hxy] using hybranch.symm
  exact
    (h.isMoore.not_adj_other_branch_of_mem_branchFiber
      (coords.hub 0) (coords.hub (0 + d))
      (coords.a_ne (index_ne_add_of_ne_zero hd)) hxmem)
      hx_adj_target

/-- The two support-pair reference endpoints are distinct as vertices. -/
theorem cardTwoSupportPairLeftEndpoint_ne_reflected
    {labeling : BranchOrbitABCReflectionLabeling h}
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    labeling.cardTwoCandidateLeftEndpointVertex p ≠
      labeling.cardTwoCandidateLeftEndpointVertex
        (labeling.aFiberReflectionCoordPerm p) := by
  simpa [cardTwoCandidateLeftEndpointVertex,
    endpointCommonNeighborReferenceVertex] using
    supportCard.reference_coord_ne_reflection_of_mem hp

/-- Pair endpoint adjacency forces the named endpoint pair to be non-adjacent:
otherwise the support-pair matching target would identify `p` with its
A-fixing reflection mate. -/
theorem cardTwoCandidateEndpoints_not_adj_of_pair_endpoint_adj
    {labeling : BranchOrbitABCReflectionLabeling h}
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport)
    (d : ZMod 19) (hd : d ≠ 0)
    (hpair : labeling.cardTwoPairEndpointAdj d p) :
    ¬ Γ.Adj
      (labeling.cardTwoCandidateLeftEndpointVertex p)
      (labeling.cardTwoCandidateRightEndpointVertex d p) := by
  intro hadj
  let coords := labeling.data.toAFiberCoordinates
  have hmatchRight :
      AFiberCoordinates.matchingEquiv h.isMoore coords 0 (0 + d)
          (index_ne_add_of_ne_zero hd) p =
        labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p := by
    exact
      AFiberCoordinates.matchingEquiv_eq_of_adj
        h.isMoore coords (index_ne_add_of_ne_zero hd)
        (p := p)
        (q := labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p)
        (by
          simpa [cardTwoCandidateLeftEndpointVertex,
            cardTwoCandidateRightEndpointVertex,
            endpointCommonNeighborReferenceVertex, coords] using hadj)
  have htargets :=
    supportCard.pair_endpoint_adj_to_matching_targets_of_mem hp d hd
      (by
        simpa [cardTwoPairEndpointAdj,
          endpointCommonNeighborReferenceVertex,
          endpointCommonNeighborReflectedEndpointVertex] using hpair)
  have hrot :
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0
          (labeling.aFiberReflectionCoordPerm p) =
        labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p :=
    htargets.1.symm.trans hmatchRight
  have hfixed : labeling.aFiberReflectionCoordPerm p = p :=
    (labeling.data.toAFiberRotationEquivariance.coordPerm d 0).injective hrot
  exact supportCard.aFiberReflectionCoordPerm_ne_of_mem hp hfixed

/-- Common-neighbor candidates in different chosen A-fibers are distinct. -/
theorem cardTwoCandidateCommonNeighbor_ne_of_offset_ne
    (labeling : BranchOrbitABCReflectionLabeling h)
    {k l : ZMod 19} (hk : k ≠ 0) (hl : l ≠ 0) (hkl : k ≠ l)
    (p : labeling.data.toAFiberCoordinates.P) :
    labeling.cardTwoCandidateCommonNeighborVertex k hk p ≠
      labeling.cardTwoCandidateCommonNeighborVertex l hl p := by
  intro hxy
  let coords := labeling.data.toAFiberCoordinates
  have hxmem :
      labeling.cardTwoCandidateCommonNeighborVertex k hk p ∈
        branchFiber Γ coords.u (coords.a (0 + k)) := by
    simpa [cardTwoCandidateCommonNeighborVertex, coords] using
      coords.coord_mem (0 + k)
        (AFiberCoordinates.matchingEquiv h.isMoore coords 0 (0 + k)
          (index_ne_add_of_ne_zero hk) p)
  have hybranch :
      Γ.Adj (coords.a (0 + l))
        (labeling.cardTwoCandidateCommonNeighborVertex l hl p) := by
    have hymem :
        labeling.cardTwoCandidateCommonNeighborVertex l hl p ∈
          branchFiber Γ coords.u (coords.a (0 + l)) := by
      simpa [cardTwoCandidateCommonNeighborVertex, coords] using
        coords.coord_mem (0 + l)
          (AFiberCoordinates.matchingEquiv h.isMoore coords 0 (0 + l)
            (index_ne_add_of_ne_zero hl) p)
    exact (mem_branchFiber.mp hymem).2
  have hx_adj_target :
      Γ.Adj (labeling.cardTwoCandidateCommonNeighborVertex k hk p)
        (coords.a (0 + l)) := by
    simpa [hxy] using hybranch.symm
  have hidx : (0 + k : ZMod 19) ≠ 0 + l := by
    intro hidx
    exact hkl (by simpa using hidx)
  exact
    (h.isMoore.not_adj_other_branch_of_mem_branchFiber
      (coords.hub (0 + k)) (coords.hub (0 + l))
      (coords.a_ne hidx) hxmem)
      hx_adj_target

/-- The two named common-neighbor candidates are distinct. -/
theorem cardTwoFirstCandidateCommonNeighbor_ne_second
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (hd : d ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    labeling.cardTwoFirstCandidateCommonNeighborVertex d hd p ≠
      labeling.cardTwoSecondCandidateCommonNeighborVertex d hd p := by
  simpa [cardTwoFirstCandidateCommonNeighborVertex,
    cardTwoSecondCandidateCommonNeighborVertex] using
    labeling.cardTwoCandidateCommonNeighbor_ne_of_offset_ne
      (cardTwoFirstCandidateOffset_ne_zero d hd)
      (cardTwoSecondCandidateOffset_ne_zero d hd)
      (cardTwoFirstCandidateOffset_ne_second d hd) p

/-- Named-candidate strengthening of the card-two hard-gap summary.  The
fields are exactly the endpoint nonadjacency, endpoint/common-neighbor
distinctness, and the four common-neighbor adjacencies for the two named
candidates. -/
structure BranchOrbitABCCardTwoCandidateBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  candidate_endpoints_ne :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.cardTwoPairEndpointAdj d p →
            labeling.cardTwoCandidateLeftEndpointVertex p ≠
              labeling.cardTwoCandidateRightEndpointVertex d p
  candidate_endpoints_not_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.cardTwoPairEndpointAdj d p →
            ¬ Γ.Adj
              (labeling.cardTwoCandidateLeftEndpointVertex p)
              (labeling.cardTwoCandidateRightEndpointVertex d p)
  first_candidate_adj_left :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.cardTwoPairEndpointAdj d p →
            Γ.Adj
              (labeling.cardTwoCandidateLeftEndpointVertex p)
              (labeling.cardTwoFirstCandidateCommonNeighborVertex d hd p)
  first_candidate_adj_right :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.cardTwoPairEndpointAdj d p →
            Γ.Adj
              (labeling.cardTwoCandidateRightEndpointVertex d p)
              (labeling.cardTwoFirstCandidateCommonNeighborVertex d hd p)
  second_candidate_adj_left :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.cardTwoPairEndpointAdj d p →
            Γ.Adj
              (labeling.cardTwoCandidateLeftEndpointVertex p)
              (labeling.cardTwoSecondCandidateCommonNeighborVertex d hd p)
  second_candidate_adj_right :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.cardTwoPairEndpointAdj d p →
            Γ.Adj
              (labeling.cardTwoCandidateRightEndpointVertex d p)
              (labeling.cardTwoSecondCandidateCommonNeighborVertex d hd p)
  candidate_commonNeighbors_ne :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.cardTwoPairEndpointAdj d p →
            labeling.cardTwoFirstCandidateCommonNeighborVertex d hd p ≠
              labeling.cardTwoSecondCandidateCommonNeighborVertex d hd p

namespace BranchOrbitABCCardTwoCandidateBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Forget the named candidates and recover the current card-two hard-gap
summary. -/
def toBranchOrbitABCCardTwoGapSummaryBoundary
    (boundary : BranchOrbitABCCardTwoCandidateBoundary labeling) :
    BranchOrbitABCCardTwoGapSummaryBoundary labeling where
  two_commonNeighbors_of_pair_endpoint_adj := by
    intro d hd p hp hpairRaw
    have hpair : labeling.cardTwoPairEndpointAdj d p := by
      simpa [cardTwoPairEndpointAdj,
        endpointCommonNeighborReferenceVertex,
        endpointCommonNeighborReflectedEndpointVertex] using hpairRaw
    refine
      ⟨labeling.cardTwoCandidateLeftEndpointVertex p,
        labeling.cardTwoCandidateRightEndpointVertex d p,
        labeling.cardTwoFirstCandidateCommonNeighborVertex d hd p,
        labeling.cardTwoSecondCandidateCommonNeighborVertex d hd p,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact boundary.candidate_endpoints_ne d hd p hp hpair
    · exact boundary.candidate_endpoints_not_adj d hd p hp hpair
    · exact boundary.candidate_commonNeighbors_ne d hd p hp hpair
    · exact boundary.first_candidate_adj_left d hd p hp hpair
    · exact boundary.first_candidate_adj_right d hd p hp hpair
    · exact boundary.second_candidate_adj_left d hd p hp hpair
    · exact boundary.second_candidate_adj_right d hd p hp hpair

/-- Direct connector to the support-pair two-common-neighbor boundary consumed
by the existing card-two pipeline. -/
def toMidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
    (boundary : BranchOrbitABCCardTwoCandidateBoundary labeling) :
    MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
      labeling :=
  boundary.toBranchOrbitABCCardTwoGapSummaryBoundary
    |>.toMidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary

end BranchOrbitABCCardTwoCandidateBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
