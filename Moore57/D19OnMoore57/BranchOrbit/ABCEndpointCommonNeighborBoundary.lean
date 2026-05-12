import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionEndpointPointwiseBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCReferenceSolutionFixedBoundary
import Moore57.D19OnMoore57.Fixed.CommonNeighbors

/-!
# Endpoint common-neighbor boundary

This file inserts a boundary closer to the natural-language endpoint
common-neighbor contradiction.  Instead of assuming pointwise endpoint
nonadjacency directly, it assumes the contradiction-style statement that an
endpoint adjacency on a moved A-fixing support coordinate would force that
coordinate to be fixed by the A-fixing reflection.  Membership in the support
then converts this immediately to the existing pointwise nonadjacency boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Contradiction-style endpoint boundary: for every moved reference
A-coordinate in the A-fixing reflection support, endpoint adjacency for the
midpoint-reflected endpoint would force that coordinate to be fixed by the
A-fixing reflection. -/
structure MidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflectionCoordPerm_fixed_of_endpoint_adj :
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
                    (0 + (midpointOf d + midpointOf d)))}) : V)) →
          labeling.aFiberReflectionCoordPerm p = p

/-- Vertex-fixed spelling of the same contradiction-style endpoint boundary.
This is the form expected from a common-neighbor argument on the underlying
reference-fiber vertex. -/
structure MidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  aFiberReflection_vertex_fixed_of_endpoint_adj :
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
                    (0 + (midpointOf d + midpointOf d)))}) : V)) →
          h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V)) =
            (((labeling.data.toAFiberCoordinates.coord 0 p :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a 0)}) : V))

namespace MidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the underlying-vertex fixedness conclusion to the coordinate
fixedness conclusion. -/
noncomputable def toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (boundary :
      MidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary labeling) :
    MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling where
  aFiberReflectionCoordPerm_fixed_of_endpoint_adj := by
    intro d hd p hp hadj
    exact
      (labeling.aFiberReflectionCoordPerm_fixed_iff_vertex_fixed p).2
        (boundary.aFiberReflection_vertex_fixed_of_endpoint_adj d hd p hp hadj)

end MidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary

namespace MidpointExceptionEndpointAdjForcesAFixingFixedBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- If endpoint adjacency would force A-fixing fixedness, then no point in the
A-fixing reflection support can satisfy that endpoint adjacency. -/
def toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (boundary :
      MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling where
  endpoint_nonadj_of_mem_support := by
    intro d hd p hp hadj
    have hfixed :
        labeling.aFiberReflectionCoordPerm p = p :=
      boundary.aFiberReflectionCoordPerm_fixed_of_endpoint_adj d hd p hp hadj
    have hmoved : labeling.aFiberReflectionCoordPerm p ≠ p :=
      (labeling.mem_aFiberReflectionSupport p).1 hp
    exact hmoved hfixed

/-- Direct witness-boundary connector after choosing a support point from the
existing card-two support boundary. -/
def toMidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary
    (boundary :
      MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    |>.toMidpointExceptionAFixingSupportEndpointNonadjWitnessBoundary supportCard

/-- Direct all-support endpoint-adjacency negation connector. -/
def toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary
    (boundary :
      MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling) :
    MidpointExceptionAFixingSupportNoAllEndpointAdjBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    |>.toMidpointExceptionAFixingSupportNoAllEndpointAdjBoundary supportCard

/-- Direct non-containment connector used to rule out the card-two midpoint
exception case. -/
def toMidpointExceptionAFixingSupportNoCardTwoBoundary
    (boundary :
      MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (criterion : MidpointReflectionCriterionBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardTwoBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    |>.toMidpointExceptionAFixingSupportNoCardTwoBoundary supportCard criterion

end MidpointExceptionEndpointAdjForcesAFixingFixedBoundary

namespace MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Pointwise endpoint non-adjacency also gives the contradiction-style
endpoint fixedness boundary: the impossible endpoint adjacency proves the
fixedness conclusion vacuously. -/
noncomputable def toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling where
  aFiberReflectionCoordPerm_fixed_of_endpoint_adj := by
    intro d hd p hp hadj
    exact False.elim
      (boundary.endpoint_nonadj_of_mem_support d hd p hp hadj)

end MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
