import Moore57.BranchOrbitABCSupportPairBoundary
import Moore57.BranchOrbitABCSupportPairCommonNeighborBoundary
import Moore57.BranchOrbitABCSupportPairEndpointMatchingBoundary

/-!
# Card-two hard-gap summary

After the support-pair and endpoint-matching reductions, the remaining
card-two input is the coordinate construction of two distinct common neighbors
for a non-adjacent endpoint pair, starting from endpoint adjacency on a chosen
support point and its A-fiber reflection mate.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Summary form of the updated hard gap in the card-two branch.  For a
nonzero endpoint offset and a chosen point in the A-fixing reflection support,
pair endpoint adjacency should produce a non-adjacent endpoint pair with two
distinct common neighbors. -/
structure BranchOrbitABCCardTwoGapSummaryBoundary
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

namespace BranchOrbitABCCardTwoGapSummaryBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The summary field is exactly the support-pair two-common-neighbor boundary
expected by the existing card-two pipeline. -/
def toMidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
    (boundary : BranchOrbitABCCardTwoGapSummaryBoundary labeling) :
    MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
      labeling where
  two_commonNeighbors_of_pair_endpoint_adj :=
    boundary.two_commonNeighbors_of_pair_endpoint_adj

/-- Repackage the existing support-pair two-common-neighbor boundary as the
updated hard-gap summary. -/
def ofMidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
    (boundary :
      MidpointExceptionAFixingSupportPairEndpointTwoCommonNeighborsBoundary
        labeling) :
    BranchOrbitABCCardTwoGapSummaryBoundary labeling where
  two_commonNeighbors_of_pair_endpoint_adj :=
    boundary.two_commonNeighbors_of_pair_endpoint_adj

end BranchOrbitABCCardTwoGapSummaryBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
