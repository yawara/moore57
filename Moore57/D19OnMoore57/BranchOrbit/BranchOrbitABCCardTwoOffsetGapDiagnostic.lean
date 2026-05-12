import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCCardTwoAllOffsetsCommonNeighborBoundary

/-!
# Card-two endpoint-offset gap diagnostic

This diagnostic records the offset-shape mismatch in the card-two
two-common-neighbor boundary.  The existing
`MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary` has a
one-offset antecedent: for a fixed endpoint separation `d`, it assumes endpoint
adjacency only at that same `d`.

The candidate construction encoded in
`MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary`
uses the stronger all-offset antecedent.  In the proof
`AFixingReflectionFixedNeighborCardBoundary.two_commonNeighbors_of_all_offsets_endpoint_adj`,
the two candidate common neighbors require endpoint equations at the four
offsets `k`, `l`, `k - j`, and `l - j` for a nonzero endpoint separation `j`.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The current one-offset boundary shape under inspection. -/
abbrev CardTwoOneOffsetEndpointBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop :=
  MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary labeling

/-- The corrected stronger all-offset boundary shape for the card-two
common-neighbor construction. -/
abbrev CardTwoAllOffsetsEndpointBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop :=
  MidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary
    labeling

/-- All-offset endpoint adjacency supplies the four endpoint offsets used by
the candidate common-neighbor construction: `k`, `l`, `k - j`, and `l - j`. -/
theorem all_offsets_endpoint_adj_supplies_cardTwo_candidate_offsets
    {labeling : BranchOrbitABCReflectionLabeling h}
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
                      (0 + (midpointOf d + midpointOf d)))}) : V)))
    (j : ZMod 19) (hj : j ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    let indices := zmod19_card_two_candidate_indices j hj
    Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V))
        (((labeling.data.toAFiberCoordinates.coord
            (0 + (midpointOf indices.k + midpointOf indices.k))
            (labeling.midpointReflectionCoordPerm (midpointOf indices.k) p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a
                (0 + (midpointOf indices.k + midpointOf indices.k)))}) : V)) ∧
      Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V))
        (((labeling.data.toAFiberCoordinates.coord
            (0 + (midpointOf indices.l + midpointOf indices.l))
            (labeling.midpointReflectionCoordPerm (midpointOf indices.l) p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a
                (0 + (midpointOf indices.l + midpointOf indices.l)))}) : V)) ∧
      Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V))
        (((labeling.data.toAFiberCoordinates.coord
            (0 + (midpointOf (indices.k - j) +
              midpointOf (indices.k - j)))
            (labeling.midpointReflectionCoordPerm
              (midpointOf (indices.k - j)) p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a
                (0 + (midpointOf (indices.k - j) +
                  midpointOf (indices.k - j))))}) : V)) ∧
      Γ.Adj
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V))
        (((labeling.data.toAFiberCoordinates.coord
            (0 + (midpointOf (indices.l - j) +
              midpointOf (indices.l - j)))
            (labeling.midpointReflectionCoordPerm
              (midpointOf (indices.l - j)) p) :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a
                (0 + (midpointOf (indices.l - j) +
                  midpointOf (indices.l - j))))}) : V)) := by
  intro indices
  exact
    ⟨hall indices.k indices.k_ne_zero p hp,
      hall indices.l indices.l_ne_zero p hp,
      hall (indices.k - j) indices.k_sub_j_ne_zero p hp,
      hall (indices.l - j) indices.l_sub_j_ne_zero p hp⟩

/-- The existing support-card API produces the corrected all-offset boundary,
not merely the one-offset diagnostic shape. -/
def corrected_all_offsets_endpoint_boundary_of_supportCard
    {labeling : BranchOrbitABCReflectionLabeling h}
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    CardTwoAllOffsetsEndpointBoundary labeling :=
  supportCard.toMidpointExceptionAFixingSupportAllOffsetsEndpointTwoCommonNeighborsBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
