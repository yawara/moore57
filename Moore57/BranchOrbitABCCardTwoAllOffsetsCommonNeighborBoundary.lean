import Moore57.BranchOrbitABCCardTwoCandidateAdjacencyBoundary
import Moore57.BranchOrbitABCCardTwoCandidateDistinctBoundary
import Moore57.BranchOrbitABCCardTwoCommonNeighborBoundary
import Moore57.BranchOrbitABCCardTwoEndpointNonadjBoundary
import Moore57.BranchOrbitABCSupportPairEndpointMatchingBoundary
import Moore57.Foundations.ZMod19.CardTwoCandidateIndices

/-!
# Card-two common neighbors from all endpoint offsets

The natural-language card-two construction uses endpoint matching equations at
several offsets.  From all-offset endpoint adjacency on the two-point support,
we choose a nonzero endpoint separation `j` and two candidate offsets `k,l`
avoiding `0` and `j`.  The endpoint equations at `k`, `l`, `k-j`, and `l-j`
then produce two distinct common neighbors for the endpoint pair
`(0,p)` and `(j,p)`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- All-offset endpoint adjacency on the two-point A-fixing support produces
a non-adjacent endpoint pair with two distinct common neighbors. -/
theorem two_commonNeighbors_of_all_offsets_endpoint_adj
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (hall :
      ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          p ∈ labeling.aFiberReflectionSupport →
            Γ.Adj
              (((labeling.data.toAFiberCoordinates.coord 0 p :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a 0)}) : V))
              (((labeling.data.toAFiberCoordinates.coord
                  (0 + (midpointOf d + midpointOf d))
                  (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a
                      (0 + (midpointOf d + midpointOf d)))}) : V))) :
    ∃ x y z w : V,
      x ≠ y ∧
      ¬ Γ.Adj x y ∧
      z ≠ w ∧
      Γ.Adj x z ∧ Γ.Adj y z ∧
      Γ.Adj x w ∧ Γ.Adj y w := by
  classical
  let coords := labeling.data.toAFiberCoordinates
  let rot := labeling.data.toAFiberRotationEquivariance
  rcases supportCard.exists_mem_aFiberReflectionSupport with ⟨p, hp⟩
  let q := labeling.aFiberReflectionCoordPerm p
  have hq : q ∈ labeling.aFiberReflectionSupport := by
    simpa [q] using labeling.aFiberReflectionCoordPerm_mem_support_of_mem hp
  let j : ZMod 19 := 1
  have hj : j ≠ 0 := by
    decide
  let indices := zmod19_card_two_candidate_indices j hj
  let k := indices.k
  let l := indices.l
  have hk : k ≠ 0 := indices.k_ne_zero
  have hl : l ≠ 0 := indices.l_ne_zero
  have hkj : k - j ≠ 0 := indices.k_sub_j_ne_zero
  have hlj : l - j ≠ 0 := indices.l_sub_j_ne_zero
  have hkl : k ≠ l := indices.k_ne_l
  have hpair :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        Γ.Adj
          (((coords.coord 0 p :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
          (((coords.coord (0 + (midpointOf d + midpointOf d))
              (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
            {x : V // x ∈
              branchFiber Γ coords.u
                (coords.a (0 + (midpointOf d + midpointOf d)))}) : V)) ∧
        Γ.Adj
          (((coords.coord 0 q :
            {x : V // x ∈ branchFiber Γ coords.u (coords.a 0)}) : V))
          (((coords.coord (0 + (midpointOf d + midpointOf d))
              (labeling.midpointReflectionCoordPerm (midpointOf d) q) :
            {x : V // x ∈
              branchFiber Γ coords.u
                (coords.a (0 + (midpointOf d + midpointOf d)))}) : V)) := by
    intro d hd
    exact
      ⟨by simpa [coords] using hall d hd p hp,
        by simpa [coords, q] using hall d hd q hq⟩
  have hmatch_k :=
    supportCard.pair_endpoint_adj_to_matching_targets_of_mem hp k hk
      (hpair k hk)
  have hmatch_l :=
    supportCard.pair_endpoint_adj_to_matching_targets_of_mem hp l hl
      (hpair l hl)
  have hmatch_kj :=
    supportCard.pair_endpoint_adj_to_matching_targets_of_mem hp (k - j) hkj
      (hpair (k - j) hkj)
  have hmatch_lj :=
    supportCard.pair_endpoint_adj_to_matching_targets_of_mem hp (l - j) hlj
      (hpair (l - j) hlj)
  have hxz :
      Γ.Adj (AFiberCoordinates.baseEndpointVertex coords p)
        (AFiberCoordinates.rotatedCandidateVertex rot k q) := by
    exact
      AFiberCoordinates.base_adj_rotatedCandidateVertex_of_endpoint_matching
        (hΓ := h.isMoore) (rot := rot) hk p q hmatch_k.1
  have hyz :
      Γ.Adj (AFiberCoordinates.rotatedEndpointVertex rot j p)
        (AFiberCoordinates.rotatedCandidateVertex rot k q) := by
    exact
      AFiberCoordinates.rotatedEndpoint_adj_rotatedCandidateVertex_of_difference_matching
        (hΓ := h.isMoore) (rot := rot) hkj p q hmatch_kj.1
  have hxw :
      Γ.Adj (AFiberCoordinates.baseEndpointVertex coords p)
        (AFiberCoordinates.rotatedCandidateVertex rot l q) := by
    exact
      AFiberCoordinates.base_adj_rotatedCandidateVertex_of_endpoint_matching
        (hΓ := h.isMoore) (rot := rot) hl p q hmatch_l.1
  have hyv :
      Γ.Adj (AFiberCoordinates.rotatedEndpointVertex rot j p)
        (AFiberCoordinates.rotatedCandidateVertex rot l q) := by
    exact
      AFiberCoordinates.rotatedEndpoint_adj_rotatedCandidateVertex_of_difference_matching
        (hΓ := h.isMoore) (rot := rot) hlj p q hmatch_lj.1
  have hxy :=
    AFiberCoordinates.baseEndpointVertex_rotatedEndpointVertex_ne_and_not_adj_of_matching_candidate
      (hΓ := h.isMoore) (rot := rot) hj hk hkj p q hmatch_k.1 hmatch_kj.1
  have hzw :
      AFiberCoordinates.rotatedCandidateVertex rot k q ≠
        AFiberCoordinates.rotatedCandidateVertex rot l q :=
    AFiberCoordinates.rotatedCandidateVertex_ne_of_index_ne
      (rot := rot) hkl q
  exact
    ⟨AFiberCoordinates.baseEndpointVertex coords p,
      AFiberCoordinates.rotatedEndpointVertex rot j p,
      AFiberCoordinates.rotatedCandidateVertex rot k q,
      AFiberCoordinates.rotatedCandidateVertex rot l q,
      hxy.1, hxy.2, hzw, hxz, hyz, hxw, hyv⟩

end AFixingReflectionFixedNeighborCardBoundary

/-- Boundary form: all-offset endpoint adjacency on the A-fixing support
forces a two-common-neighbor contradiction. -/
structure MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  two_commonNeighbors_of_all_offsets_endpoint_adj :
    (∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V))) →
      ∃ x y z w : V,
        x ≠ y ∧
        ¬ Γ.Adj x y ∧
        z ≠ w ∧
        Γ.Adj x z ∧ Γ.Adj y z ∧
        Γ.Adj x w ∧ Γ.Adj y w

/-- Boundary form denying simultaneous endpoint adjacency at every nonzero
offset on the A-fixing support. -/
structure MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_offsets_support_endpoint_adj :
    ¬ ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V))

namespace MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The all-offset two-common-neighbor construction denies simultaneous
endpoint adjacency at every nonzero offset. -/
def toMidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary
    (boundary :
      MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
        labeling) :
    MidpointExceptionAFixingSupportNoAllOffsetsEndpointAdjBoundary labeling where
  not_all_offsets_support_endpoint_adj := by
    intro hall
    rcases boundary.two_commonNeighbors_of_all_offsets_endpoint_adj hall with
      ⟨x, y, z, w, hxy, hnadj, hzw, hxz, hyz, hxw, hyw⟩
    exact
      h.isMoore.no_two_commonNeighbors_of_not_adj
        hxy hnadj hzw hxz hyz hxw hyw

end MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The two-point support boundary supplies the all-offset common-neighbor
construction. -/
def toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
      labeling where
  two_commonNeighbors_of_all_offsets_endpoint_adj :=
    supportCard.two_commonNeighbors_of_all_offsets_endpoint_adj

end AFixingReflectionFixedNeighborCardBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
