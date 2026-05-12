import Moore57.D19OnMoore57.BranchOrbit.ABCMatchingTargetReflectionReduced
import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointPointwiseBoundary

/-!
# Endpoint-pointwise constructor for the midpoint exception case boundary

This file packages the canonical finite-set route for the midpoint-exception
support case.  The negative-offset transport reduces the one-point case to the
paired-singleton obstruction, while pointwise endpoint non-adjacency gives the
non-containment input excluding the two-point case.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

namespace MidpointExceptionAFixingSupportNoPairedSingletonBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Combine the paired-singleton obstruction and pointwise endpoint
non-adjacency into the full midpoint-exception/A-fixing support case boundary.

This is the finite-set form needed by `LeanAwareFixedStarFinalBoundary`: the
negative-offset transport gives `no_card_one`, and the endpoint pointwise
obstruction gives `no_card_two` through the existing all-support connector. -/
def toMidpointExceptionAFixingSupportCaseBoundary_endpointPointwiseNonadj
    (boundary :
      MidpointExceptionAFixingSupportNoPairedSingletonBoundary labeling)
    (transport :
      MidpointExceptionAFixingSupportIntersectionNegInvariantBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling)
    (endpointPointwiseNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
        labeling) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  let noCardOne :=
    boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary transport
  let noCardTwo :=
    endpointPointwiseNonadj.toMidpointExceptionAFixingSupportNoCardTwoBoundary
      supportCard criterion
  noCardOne.toMidpointExceptionAFixingSupportCaseBoundary supportCard
    (noCardTwo.no_card_two supportCard)

end MidpointExceptionAFixingSupportNoPairedSingletonBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
