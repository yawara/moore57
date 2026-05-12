import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointSignAdjacencyBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairEndpointBoundary

/-!
# Matching equations from endpoint adjacency on the support pair

Endpoint adjacency for a chosen support point says that the matching target is
the rotated A-fiber reflection mate.  In the card-two support pair, applying
the same statement to the mate and using involutivity gives the complementary
target equation.
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

/-- Pair endpoint adjacency gives the two endpoint matching equations in the
sign-swapped normal form: `p` targets `A p`, while `A p` targets `p`. -/
theorem pair_endpoint_adj_to_matching_targets_of_mem
    (_supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (_hp : p ∈ labeling.aFiberReflectionSupport)
    (d : ZMod 19) (hd : d ≠ 0)
    (hpair :
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
                (0 + (midpointOf d + midpointOf d)))}) : V)) ∧
      Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord 0
            (labeling.aFiberReflectionCoordPerm p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V))
        (((labeling.data.toAFiberCoordinates.coord
            (0 + (midpointOf d + midpointOf d))
            (labeling.midpointReflectionCoordPerm (midpointOf d)
              (labeling.aFiberReflectionCoordPerm p)) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a
                (0 + (midpointOf d + midpointOf d)))}) : V))) :
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0
        (labeling.aFiberReflectionCoordPerm p) ∧
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd)
        (labeling.aFiberReflectionCoordPerm p) =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p := by
  have hfirst :=
    labeling.endpoint_targetSign_hyp_of_endpoint_adj d hd p hpair.1
  have hsecond_raw :=
    labeling.endpoint_targetSign_hyp_of_endpoint_adj d hd
      (labeling.aFiberReflectionCoordPerm p) hpair.2
  have hinv :
      labeling.aFiberReflectionCoordPerm
          (labeling.aFiberReflectionCoordPerm p) = p :=
    labeling.aFiberReflectionCoordPerm_involutive p
  exact ⟨hfirst, by simpa [hinv] using hsecond_raw⟩

/-- All-support endpoint adjacency gives the same sign-swapped matching target
normal form after choosing a support point. -/
theorem all_support_endpoint_adj_to_matching_targets_of_mem
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport)
    (d : ZMod 19) (hd : d ≠ 0)
    (hall :
      ∀ r : labeling.data.toAFiberCoordinates.P,
        r ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (((labeling.data.toAFiberCoordinates.coord 0 r :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))
            (((labeling.data.toAFiberCoordinates.coord
                (0 + (midpointOf d + midpointOf d))
                (labeling.midpointReflectionCoordPerm (midpointOf d) r) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + (midpointOf d + midpointOf d)))}) : V))) :
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd) p =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0
        (labeling.aFiberReflectionCoordPerm p) ∧
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates 0 (0 + d)
        (index_ne_add_of_ne_zero hd)
        (labeling.aFiberReflectionCoordPerm p) =
      labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p := by
  exact supportCard.pair_endpoint_adj_to_matching_targets_of_mem hp d hd
    ((supportCard.all_support_endpoint_adj_iff_pair_endpoint_adj_of_mem
      hp d hd).1 hall)

end AFixingReflectionFixedNeighborCardBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
