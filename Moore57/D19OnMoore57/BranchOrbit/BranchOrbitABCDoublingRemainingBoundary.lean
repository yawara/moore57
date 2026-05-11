import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCDoublingCommonNeighborBasic
import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionEndpointPointwiseBoundary

/-!
# Remaining boundary for doubling midpoint common-neighbor facts

This file separates the two fields left in
`MidpointExceptionDoublingMiddleCommonNeighborBasicBoundary`.

The endpoint non-adjacency field is just the existing pointwise endpoint
non-adjacency boundary at offset `d = m + m`.  After that reduction, the only
new common-neighbor input left here is the reflected-reference adjacency of
the middle mate.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Halving `m + m` recovers `m` in `ZMod 19`. -/
theorem midpointOf_add_self_eq (m : ZMod 19) :
    midpointOf (m + m) = m := by
  dsimp [midpointOf]
  rw [← two_mul]
  rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero_zmod19, one_mul]

/-- The existing pointwise endpoint non-adjacency boundary supplies the
endpoint non-adjacency field needed by the midpoint doubling common-neighbor
boundary. -/
theorem midpoint_endpoints_not_adj_of_endpointPointwiseNonadj
    (labeling : BranchOrbitABCReflectionLabeling h)
    (endpointNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hpSupport : p ∈ labeling.aFiberReflectionSupport) :
    ¬ Γ.Adj
      (labeling.midpointExceptionReferenceVertex p)
      (labeling.midpointExceptionReflectedReferenceVertex m p) := by
  have hmid : midpointOf (m + m) = m :=
    midpointOf_add_self_eq m
  have hidx :
      midpointOf (m + m) + midpointOf (m + m) = m + m := by
    rw [hmid]
  have hnonadj :=
    endpointNonadj.endpoint_nonadj_of_mem_support
      (m + m) (add_self_ne_zero_zmod19 hm) p hpSupport
  rw [hidx] at hnonadj
  simpa [midpointExceptionReferenceVertex,
    midpointExceptionReflectedReferenceVertex, hmid] using hnonadj

/-- The reflected-reference adjacency is the only remaining local field once
endpoint non-adjacency is imported from the endpoint pointwise boundary. -/
structure MidpointExceptionDoublingMiddleReflectedAdjBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_middle_adj_reflected_reference :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.midpointExceptionReflectedReferenceVertex m p)
            (labeling.midpointExceptionMiddleMateVertex m hm p)

namespace MidpointExceptionDoublingMiddleReflectedAdjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Combine endpoint pointwise non-adjacency with the single remaining
reflected-reference adjacency input to obtain the previous two-field basic
boundary. -/
def toMidpointExceptionDoublingMiddleCommonNeighborBasicBoundary
    (boundary :
      MidpointExceptionDoublingMiddleReflectedAdjBoundary labeling)
    (endpointNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionDoublingMiddleCommonNeighborBasicBoundary labeling where
  midpoint_endpoints_not_adj := by
    intro m hm p hpSupport
    exact
      labeling.midpoint_endpoints_not_adj_of_endpointPointwiseNonadj
        endpointNonadj m hm p hpSupport
  midpoint_middle_adj_reflected_reference :=
    boundary.midpoint_middle_adj_reflected_reference

/-- Direct connector to the full common-neighbor boundary after the
definition-level fields from `BranchOrbitABCDoublingCommonNeighborBasic` are
filled in. -/
def toMidpointExceptionDoublingMiddleCommonNeighborBoundary
    (boundary :
      MidpointExceptionDoublingMiddleReflectedAdjBoundary labeling)
    (endpointNonadj :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling :=
  (boundary.toMidpointExceptionDoublingMiddleCommonNeighborBasicBoundary
      endpointNonadj)
    |>.toMidpointExceptionDoublingMiddleCommonNeighborBoundary

end MidpointExceptionDoublingMiddleReflectedAdjBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
