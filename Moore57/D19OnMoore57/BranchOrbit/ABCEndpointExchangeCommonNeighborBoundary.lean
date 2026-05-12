import Moore57.D19OnMoore57.BranchOrbit.ABCEndpointSignAdjacencyBoundary
import Moore57.D19OnMoore57.BranchOrbit.ABCCardTwoCommonNeighborBoundary

/-!
# Endpoint exchange as a two-common-neighbor obstruction

This file records the endpoint-common-neighbor form suggested by the
label-exchange argument.  If endpoint adjacency for `p` also gives adjacency
from the same endpoint to the reflected reference coordinate `A p`, then the
two endpoint targets have two common neighbors, namely the reference vertices
for `p` and `A p`.  The Moore `λ = 0`, `μ = 1` core then rules out the
endpoint adjacency on the A-fixing moving support.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Endpoint-reference exchange boundary: the endpoint edge from the original
reference coordinate also appears from the reflected reference coordinate. -/
structure EndpointReferenceExchangeCommonNeighborBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reflected_reference_adj_endpoint_of_endpoint_adj :
    ∀ d : ZMod 19, ∀ _hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.endpointCommonNeighborReferenceVertex p)
            (labeling.endpointCommonNeighborReflectedEndpointVertex d p) →
          Γ.Adj
            (labeling.endpointCommonNeighborReferenceVertex
              (labeling.aFiberReflectionCoordPerm p))
            (labeling.endpointCommonNeighborReflectedEndpointVertex d p)

/-- Matching-equation form of endpoint-reference exchange.  It says that if
the endpoint target generated from `p` is matched by `p`, then the same endpoint
target is also matched by `A p`. -/
structure EndpointReferenceExchangePositiveMatchingBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  positive_matching_exchange :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd) p =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p) →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + d)
              (index_ne_add_of_ne_zero hd)
              (labeling.aFiberReflectionCoordPerm p) =
            labeling.data.toAFiberRotationEquivariance.coordPerm d 0
              (labeling.aFiberReflectionCoordPerm p)

namespace EndpointReferenceExchangePositiveMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Matching-equation endpoint exchange is the same as the adjacency-form
endpoint-reference exchange. -/
def toEndpointReferenceExchangeCommonNeighborBoundary
    (boundary :
      EndpointReferenceExchangePositiveMatchingBoundary labeling) :
    EndpointReferenceExchangeCommonNeighborBoundary labeling where
  reflected_reference_adj_endpoint_of_endpoint_adj := by
    intro d hd p hp hadj
    have hmatch :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) :=
      (labeling.endpointCommonNeighbor_reference_adj_reflectedEndpoint_iff_matching
        d hd p p).1 hadj
    have hexchange :
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd)
            (labeling.aFiberReflectionCoordPerm p) =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0
            (labeling.aFiberReflectionCoordPerm p) :=
      boundary.positive_matching_exchange d hd p hp hmatch
    exact
      (labeling.endpointCommonNeighbor_reference_adj_reflectedEndpoint_iff_matching
        d hd (labeling.aFiberReflectionCoordPerm p) p).2 hexchange

end EndpointReferenceExchangePositiveMatchingBoundary

namespace EndpointReferenceExchangeCommonNeighborBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The adjacency-form endpoint-reference exchange can be restated as a
matching-equation exchange. -/
def toEndpointReferenceExchangePositiveMatchingBoundary
    (boundary : EndpointReferenceExchangeCommonNeighborBoundary labeling) :
    EndpointReferenceExchangePositiveMatchingBoundary labeling where
  positive_matching_exchange := by
    intro d hd p hp hmatch
    have hadj :
        Γ.Adj
          (labeling.endpointCommonNeighborReferenceVertex p)
          (labeling.endpointCommonNeighborReflectedEndpointVertex d p) :=
      (labeling.endpointCommonNeighbor_reference_adj_reflectedEndpoint_iff_matching
        d hd p p).2 hmatch
    have hexchange :
        Γ.Adj
          (labeling.endpointCommonNeighborReferenceVertex
            (labeling.aFiberReflectionCoordPerm p))
          (labeling.endpointCommonNeighborReflectedEndpointVertex d p) :=
      boundary.reflected_reference_adj_endpoint_of_endpoint_adj d hd p hp hadj
    exact
      (labeling.endpointCommonNeighbor_reference_adj_reflectedEndpoint_iff_matching
        d hd (labeling.aFiberReflectionCoordPerm p) p).1 hexchange

private theorem endpoint_reference_vertices_ne_of_mem_support
    (p : labeling.data.toAFiberCoordinates.P)
    (hp : p ∈ labeling.aFiberReflectionSupport) :
    labeling.endpointCommonNeighborReferenceVertex p ≠
      labeling.endpointCommonNeighborReferenceVertex
        (labeling.aFiberReflectionCoordPerm p) := by
  intro href
  let coords := labeling.data.toAFiberCoordinates
  have hsub :
      coords.coord 0 p =
        coords.coord 0 (labeling.aFiberReflectionCoordPerm p) := by
    apply Subtype.ext
    simpa [endpointCommonNeighborReferenceVertex, coords] using href
  have hp_eq : p = labeling.aFiberReflectionCoordPerm p :=
    (coords.coord 0).injective hsub
  have hp_moved : labeling.aFiberReflectionCoordPerm p ≠ p :=
    (labeling.mem_aFiberReflectionSupport p).1 hp
  exact hp_moved hp_eq.symm

private theorem aFixing_endpoint_adj_reference_of_reflected_reference_adj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (d : ZMod 19) (p : labeling.data.toAFiberCoordinates.P)
    (hadj :
      Γ.Adj
        (labeling.endpointCommonNeighborReferenceVertex
          (labeling.aFiberReflectionCoordPerm p))
        (labeling.endpointCommonNeighborReflectedEndpointVertex d p)) :
    Γ.Adj
      (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
      (labeling.endpointCommonNeighborReferenceVertex p) := by
  have hreflected :
      Γ.Adj
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReferenceVertex
            (labeling.aFiberReflectionCoordPerm p)))
        (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReflectedEndpointVertex d p)) :=
    (h.smul_adj (DihedralGroup.sr labeling.aFixingReflectionIndex)
      (labeling.endpointCommonNeighborReferenceVertex
        (labeling.aFiberReflectionCoordPerm p))
      (labeling.endpointCommonNeighborReflectedEndpointVertex d p)).mp hadj
  have hreference :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReferenceVertex
            (labeling.aFiberReflectionCoordPerm p)) =
        labeling.endpointCommonNeighborReferenceVertex p := by
    have hAA :
        labeling.aFiberReflectionCoordPerm
            (labeling.aFiberReflectionCoordPerm p) = p :=
      labeling.aFiberReflectionCoordPerm_involutive p
    simpa [endpointCommonNeighborReferenceVertex, hAA] using
      (labeling.coord_aFiberReflectionCoordPerm_apply_val
        (labeling.aFiberReflectionCoordPerm p)).symm
  have hendpoint :
      h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
          (labeling.endpointCommonNeighborReflectedEndpointVertex d p) =
        labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p :=
    labeling.aFixingReflection_endpointCommonNeighborReflectedEndpointVertex d p
  rw [hreference, hendpoint] at hreflected
  exact hreflected.symm

/-- The exchange boundary gives the basic common-neighbor boundary by
reflecting the exchanged endpoint edge. -/
def toMidpointExceptionEndpointAdjCommonNeighborBasicBoundary
    (boundary : EndpointReferenceExchangeCommonNeighborBoundary labeling) :
    MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling where
  aFixing_reflected_endpoint_adj_reference_of_endpoint_adj := by
    intro d hd p hp hadj
    exact aFixing_endpoint_adj_reference_of_reflected_reference_adj labeling d p
      (boundary.reflected_reference_adj_endpoint_of_endpoint_adj d hd p hp hadj)

/-- Direct endpoint non-adjacency from the exchange boundary.  This is the
two-common-neighbor contradiction: the endpoint targets would have both
reference vertices `p` and `A p` as common neighbors. -/
def toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (boundary : EndpointReferenceExchangeCommonNeighborBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling where
  endpoint_nonadj_of_mem_support := by
    intro d hd p hp hadj
    let x := labeling.endpointCommonNeighborReflectedEndpointVertex d p
    let y := labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p
    let z := labeling.endpointCommonNeighborReferenceVertex p
    let w :=
      labeling.endpointCommonNeighborReferenceVertex
        (labeling.aFiberReflectionCoordPerm p)
    have hx_ne_y : x ≠ y := by
      simpa [x, y] using
        labeling.endpointCommonNeighbor_reflected_endpoints_ne d hd p
    have hz_ne_w : z ≠ w := by
      simpa [z, w] using
        endpoint_reference_vertices_ne_of_mem_support (labeling := labeling) p hp
    have hxz : Γ.Adj x z := by
      simpa [x, z] using hadj.symm
    have hyz : Γ.Adj y z := by
      have hAdj :=
        aFixing_endpoint_adj_reference_of_reflected_reference_adj labeling d p
          (boundary.reflected_reference_adj_endpoint_of_endpoint_adj
            d hd p hp hadj)
      simpa [y, z] using hAdj
    have hxw : Γ.Adj x w := by
      have hAdj :=
        boundary.reflected_reference_adj_endpoint_of_endpoint_adj
          d hd p hp hadj
      simpa [x, w] using hAdj.symm
    have hyw : Γ.Adj y w := by
      have hAdj :=
        labeling.aFixing_reflected_endpoint_adj_reflected_reference_of_endpoint_adj
          d p hadj
      simpa [y, w] using hAdj
    exact h.isMoore.no_two_commonNeighbors hx_ne_y hz_ne_w hxz hyz hxw hyw

end EndpointReferenceExchangeCommonNeighborBoundary

namespace EndpointReferenceExchangePositiveMatchingBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Matching-equation endpoint exchange gives the same endpoint pointwise
non-adjacency as the adjacency-form exchange. -/
def toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary
    (boundary :
      EndpointReferenceExchangePositiveMatchingBoundary labeling) :
    MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling :=
  boundary.toEndpointReferenceExchangeCommonNeighborBoundary
    |>.toMidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end EndpointReferenceExchangePositiveMatchingBoundary

namespace MidpointExceptionEndpointAdjCommonNeighborBasicBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The basic common-neighbor boundary is equivalent to the endpoint-reference
exchange boundary after reflecting the basic conclusion. -/
def toEndpointReferenceExchangeCommonNeighborBoundary
    (boundary :
      MidpointExceptionEndpointAdjCommonNeighborBasicBoundary labeling) :
    EndpointReferenceExchangeCommonNeighborBoundary labeling where
  reflected_reference_adj_endpoint_of_endpoint_adj := by
    intro d hd p hp hadj
    have hyz :
        Γ.Adj
          (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
          (labeling.endpointCommonNeighborReferenceVertex p) :=
      boundary.aFixing_reflected_endpoint_adj_reference_of_endpoint_adj
        d hd p hp hadj
    have hreflected :
        Γ.Adj
          (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex
              d p))
          (h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (labeling.endpointCommonNeighborReferenceVertex p)) :=
      (h.smul_adj (DihedralGroup.sr labeling.aFixingReflectionIndex)
        (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p)
        (labeling.endpointCommonNeighborReferenceVertex p)).mp hyz
    have hendpoint :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (labeling.endpointCommonNeighborAFixingReflectedEndpointVertex d p) =
          labeling.endpointCommonNeighborReflectedEndpointVertex d p :=
      labeling.aFixingReflection_endpointCommonNeighborAFixingReflectedEndpointVertex
        d p
    have hreference :
        h.smul (DihedralGroup.sr labeling.aFixingReflectionIndex)
            (labeling.endpointCommonNeighborReferenceVertex p) =
          labeling.endpointCommonNeighborReferenceVertex
            (labeling.aFiberReflectionCoordPerm p) := by
      simpa [endpointCommonNeighborReferenceVertex] using
        (labeling.coord_aFiberReflectionCoordPerm_apply_val p).symm
    rw [hendpoint, hreference] at hreflected
    exact hreflected.symm

end MidpointExceptionEndpointAdjCommonNeighborBasicBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
