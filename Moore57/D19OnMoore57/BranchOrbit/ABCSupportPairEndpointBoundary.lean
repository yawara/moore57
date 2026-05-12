import Moore57.D19OnMoore57.BranchOrbit.ABCSupportPairBoundary

/-!
# Endpoint adjacency on a two-point A-fixing reflection support

In the card-two support case, all-support endpoint adjacency is equivalent to
checking a chosen support point and its A-fiber reflection mate.
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

/-- In the two-point support case, all-support endpoint adjacency is exactly
endpoint adjacency for a chosen support point and its reflection mate. -/
theorem all_support_endpoint_adj_iff_pair_endpoint_adj_of_mem
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {p : labeling.data.toAFiberCoordinates.P}
    (hp : p ∈ labeling.aFiberReflectionSupport)
    (d : ZMod 19) (_hd : d ≠ 0) :
    (∀ r : labeling.data.toAFiberCoordinates.P,
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
                    (0 + (midpointOf d + midpointOf d)))}) : V))) ↔
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
                (0 + (midpointOf d + midpointOf d)))}) : V)) := by
  constructor
  · intro hall
    exact
      ⟨hall p hp,
        hall (labeling.aFiberReflectionCoordPerm p)
          (labeling.aFiberReflectionCoordPerm_mem_support_of_mem hp)⟩
  · intro hpair r hr
    rcases
      (supportCard.mem_aFiberReflectionSupport_iff_eq_or_eq_reflection_of_mem hp).1
        hr with rfl | rfl
    · exact hpair.1
    · exact hpair.2

end AFixingReflectionFixedNeighborCardBoundary

/-- Boundary form for the card-two endpoint obstruction reduced to one chosen
support point and its reflection mate. -/
structure MidpointExceptionAFixingSupportPairEndpointNonadjBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_pair_endpoint_adj_of_support :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬
            (Γ.Adj
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
                      (0 + (midpointOf d + midpointOf d)))}) : V)))

namespace MidpointExceptionAFixingSupportPairEndpointNonadjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the pairwise card-two endpoint obstruction to the existing
all-support endpoint obstruction. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairEndpointNonadjBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling where
  not_all_support_endpoint_adj := by
    intro d hd hall
    rcases supportCard.exists_mem_aFiberReflectionSupport with ⟨p, hp⟩
    exact boundary.not_pair_endpoint_adj_of_support d hd p hp
      ((supportCard.all_support_endpoint_adj_iff_pair_endpoint_adj_of_mem
        hp d hd).1 hall)

/-- Direct conversion to the non-containment boundary used to exclude the
card-two midpoint-exception case. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairEndpointNonadjBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  (boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      supportCard)
    |>.toMidpointExceptionAFixingSupportNoCardTwoBoundary criterion

end MidpointExceptionAFixingSupportPairEndpointNonadjBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
