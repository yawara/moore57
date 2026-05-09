import Moore57.BranchOrbitABCExceptionEndpointWitnessBoundary

/-!
# Pointwise endpoint nonadjacency boundary

This file packages the strongest endpoint obstruction used in the midpoint
exception case: every A-fixing reflection-support coordinate fails the endpoint
adjacency.  Together with the existing two-point support boundary, this gives
the previously defined witness boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Pointwise endpoint-adjacency obstruction on the A-fixing reflection support:
for every nonzero offset and every moved reference A-fiber coordinate, the
endpoint adjacency encoded by the midpoint equation fails. -/
structure MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  endpoint_nonadj_of_mem_support :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬ Γ.Adj
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

namespace AFixingReflectionFixedNeighborCardBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The two-point A-fixing reflection support boundary gives a support point. -/
theorem exists_mem_aFiberReflectionSupport
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    ∃ p : labeling.data.toAFiberCoordinates.P,
      p ∈ labeling.aFiberReflectionSupport := by
  have hpos : 0 < labeling.aFiberReflectionSupport.card := by
    rw [supportCard.aFiberReflectionSupport_card_two]
    norm_num
  exact Finset.card_pos.mp hpos

end AFixingReflectionFixedNeighborCardBoundary

namespace MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the pointwise endpoint obstruction into the witness form by using
the existing card-two support boundary to choose a support point. -/
def toMidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling where
  exists_support_not_endpoint_adj := by
    intro d hd
    rcases supportCard.exists_mem_aFiberReflectionSupport with ⟨p, hp⟩
    exact ⟨p, hp, boundary.endpoint_nonadj_of_mem_support d hd p hp⟩

/-- Convert the pointwise endpoint obstruction into the existing all-support
endpoint-adjacency negation. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling :=
  (boundary.toMidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
      supportCard)
    |>.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary

/-- Direct conversion to the non-containment boundary used to exclude the
card-two midpoint-exception case. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  (boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
      supportCard)
    |>.toMidpointExceptionAFixingSupportNoCardTwoBoundary criterion

end MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
