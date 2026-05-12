import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionAllSupportBoundary

/-!
# Endpoint-witness connector for the midpoint-exception boundary

This file packages the pointwise endpoint-adjacency obstruction: for every
nonzero offset, some A-fixing reflection-support coordinate fails the endpoint
adjacency encoded by the midpoint equation.  The witness form immediately
implies the existing `NoAllEndpointAdj` boundary by contradiction.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Pointwise witness form of the endpoint-adjacency obstruction: for each
nonzero offset `d`, at least one A-fixing reflection-support coordinate does
not satisfy the endpoint adjacency for the midpoint reflection by `d / 2`. -/
structure MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  exists_support_not_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∃ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport ∧
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

namespace MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the witness form into the existing boundary denying that every
support point satisfies the endpoint adjacency. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling) :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling where
  not_all_support_endpoint_adj := by
    intro d hd hall
    rcases boundary.exists_support_not_endpoint_adj d hd with ⟨p, hp, hnonadj⟩
    exact hnonadj (hall p hp)

/-- Direct conversion to the non-containment boundary used to exclude the
card-two midpoint-exception case. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    |>.toMidpointExceptionAFixingSupportNoCardTwoBoundary criterion

end MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
