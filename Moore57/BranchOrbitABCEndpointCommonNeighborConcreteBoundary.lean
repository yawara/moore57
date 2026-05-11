import Moore57.BranchOrbitABCEndpointCommonNeighborBoundary

/-!
# Concrete endpoint common-neighbor boundary

This file makes the endpoint common-neighbor input one step more concrete.
Instead of assuming directly that endpoint adjacency forces the reference
A-fiber vertex to be fixed, it asks for the exact swapped non-adjacent pair
whose common neighbor is that reference vertex.  The fixedness conclusion is
then the formal `fixed_commonNeighbor_of_swap_not_adj` argument.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reference endpoint vertex in the A-fiber `0`. -/
def endpointCommonNeighborReferenceVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord 0 p :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a 0)}) : V)

/-- The midpoint-reflected endpoint vertex paired with the reference endpoint
in the endpoint-adjacency boundary. -/
def endpointCommonNeighborReflectedEndpointVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) : V :=
  ((labeling.data.toAFiberCoordinates.coord
    (0 + (midpointOf d + midpointOf d))
    (labeling.midpointReflectionCoordPerm (midpointOf d) p) :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a
          (0 + (midpointOf d + midpointOf d)))}) : V)

/-- Concrete common-neighbor input for the endpoint argument.  For every moved
reference coordinate, endpoint adjacency must exhibit a non-adjacent pair
swapped by the A-fixing reflection for which the reference endpoint vertex is
a common neighbor. -/
structure MidpointExceptionEndpointAdjCommonNeighborFixedBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  swapped_not_adj_pair_commonNeighbor_of_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.endpointCommonNeighborReferenceVertex p)
            (labeling.endpointCommonNeighborReflectedEndpointVertex d p) →
          ∃ x y : V,
            h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) x = y ∧
            h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex) y = x ∧
            x ≠ y ∧
            ¬ Γ.Adj x y ∧
            Γ.Adj x (labeling.endpointCommonNeighborReferenceVertex p) ∧
            Γ.Adj y (labeling.endpointCommonNeighborReferenceVertex p)

namespace MidpointExceptionEndpointAdjCommonNeighborFixedBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The concrete swapped-pair common-neighbor input implies the vertex-fixed
endpoint boundary used by the existing endpoint obstruction chain. -/
def toMidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary
    (boundary :
      MidpointExceptionEndpointAdjCommonNeighborFixedBoundary labeling) :
    MidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary labeling where
  aFiberReflection_vertex_fixed_of_endpoint_adj := by
    intro d hd p hp hadj
    rcases boundary.swapped_not_adj_pair_commonNeighbor_of_endpoint_adj
        d hd p hp (by
          simpa [endpointCommonNeighborReferenceVertex,
            endpointCommonNeighborReflectedEndpointVertex] using hadj) with
      ⟨x, y, hx, hy, hxy, hnadj, hxz, hyz⟩
    simpa [endpointCommonNeighborReferenceVertex] using
      h.fixed_commonNeighbor_of_swap_not_adj
        (DihedralGroup.sr labeling.aFixingReflectionIndex)
        hx hy hxy hnadj ⟨hxz, hyz⟩

/-- Coordinate-fixed endpoint boundary obtained after the existing formal
vertex-fixed-to-coordinate-fixed conversion. -/
def toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    (boundary :
      MidpointExceptionEndpointAdjCommonNeighborFixedBoundary labeling) :
    MidpointExceptionEndpointAdjForcesAFixingFixedBoundary labeling :=
  boundary.toMidpointExceptionEndpointAdjForcesAFixingVertexFixedBoundary
    |>.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary

/-- Direct connector to pointwise endpoint non-adjacency on the A-fixing
moving support. -/
def toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (boundary :
      MidpointExceptionEndpointAdjCommonNeighborFixedBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling :=
  boundary.toMidpointExceptionEndpointAdjForcesAFixingFixedBoundary
    |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end MidpointExceptionEndpointAdjCommonNeighborFixedBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
