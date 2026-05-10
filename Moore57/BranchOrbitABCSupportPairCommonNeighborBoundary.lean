import Moore57.BranchOrbitABCCardTwoCommonNeighborBoundary
import Moore57.BranchOrbitABCSupportPairEndpointBoundary

/-!
# Card-two common-neighbor obstruction reduced to the support pair

This module connects the graph-theoretic two-common-neighbor contradiction to
the card-two support API: in the two-point support case it is enough to build
the two common neighbors from endpoint adjacency for a chosen support point and
its A-fiber reflection mate.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Pair-reduced geometric input for the card-two endpoint obstruction.  If a
chosen support point and its reflection mate both satisfy the endpoint
adjacency, then the natural-language coordinate construction should produce a
non-adjacent pair with two distinct common neighbors. -/
structure MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  two_commonNeighbors_of_pair_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
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
                    (0 + (midpointOf d + midpointOf d)))}) : V))) →
            ∃ x y z w : V,
              x ≠ y ∧
              ¬ Γ.Adj x y ∧
              z ≠ w ∧
              Γ.Adj x z ∧ Γ.Adj y z ∧
              Γ.Adj x w ∧ Γ.Adj y w

namespace MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The pair-reduced common-neighbor construction gives the existing
all-support two-common-neighbor boundary in the card-two support case. -/
def toMidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
        labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
      labeling where
  two_commonNeighbors_of_all_endpoint_adj := by
    intro d hd hall
    rcases supportCard.exists_mem_aFiberReflectionSupport with ⟨p, hp⟩
    exact boundary.two_commonNeighbors_of_pair_endpoint_adj d hd p hp
      ((supportCard.all_support_endpoint_adj_iff_pair_endpoint_adj_of_mem
        hp d hd).1 hall)

/-- Direct conversion to the existing no-all-endpoint-adjacency boundary. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
        labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling :=
  (boundary.toMidpointExceptionAFixingSupportEndpointTwoCommonNeighborsBoundary
      supportCard)
    |>.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

/-- Direct conversion to the non-containment boundary used to exclude the
card-two midpoint-exception case. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
        labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  (boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      supportCard)
    |>.toMidpointExceptionAFixingSupportNoCardTwoBoundary criterion

end MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
