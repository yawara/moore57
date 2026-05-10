import Moore57.BranchOrbitABCDoublingReflectedAdjFromEquation

/-!
# Doubling equation/matching boundary

This file records the local obstruction behind the doubling reflected-middle
matching gap.  The midpoint equation already gives the edge from the reference
endpoint to its midpoint-reflected endpoint, while the middle mate is adjacent
to the reference endpoint by definition.  Therefore the reflected-middle
matching equation would create a triangle.

The useful reduction is consequently a no-support-midpoint-equation boundary:
if no A-fixing support coordinate satisfies the midpoint equation, the
equation-to-reflected-matching boundary is vacuous.  The existing endpoint
pointwise non-adjacency boundary supplies that no-equation boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Membership in the midpoint equation set is exactly the endpoint adjacency
between the reference coordinate and its midpoint-reflection image. -/
theorem midpoint_endpoint_adj_of_mem_midpointEquationSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hpEquation : p ∈ labeling.midpointEquationSet m hm) :
    Γ.Adj
      (labeling.midpointExceptionReferenceVertex p)
      (labeling.midpointExceptionReflectedReferenceVertex m p) := by
  simpa [midpointExceptionReferenceVertex,
    midpointExceptionReflectedReferenceVertex] using
    (AFiberCoordinates.adj_iff_matchingEquiv_eq h.isMoore
      labeling.data.toAFiberCoordinates
      (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm))
      p (labeling.midpointReflectionCoordPerm m p)).2
      ((labeling.mem_midpointEquationSet m hm p).1 hpEquation)

/-- The middle mate is adjacent to the reference endpoint by the defining
matching from the reference A-fiber to the middle A-fiber. -/
theorem midpoint_middle_adj_reference_from_matching
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    Γ.Adj
      (labeling.midpointExceptionReferenceVertex p)
      (labeling.midpointExceptionMiddleMateVertex m hm p) := by
  simpa [midpointExceptionReferenceVertex,
    midpointExceptionMiddleMateVertex, midpointExceptionMiddleMate] using
    (AFiberCoordinates.adj_coord_matchingEquiv
      (hΓ := h.isMoore)
      (coords := labeling.data.toAFiberCoordinates)
      (i := 0) (j := 0 + m)
      (hij := index_ne_add_of_ne_zero hm) p)

/-- Triangle-freeness prevents the reflected endpoint from also being adjacent
to the middle mate whenever the midpoint equation holds. -/
theorem not_midpoint_middle_adj_reflected_reference_of_mem_midpointEquationSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hpEquation : p ∈ labeling.midpointEquationSet m hm) :
    ¬ Γ.Adj
      (labeling.midpointExceptionReflectedReferenceVertex m p)
      (labeling.midpointExceptionMiddleMateVertex m hm p) := by
  intro hreflectedMiddle
  exact h.isMoore.no_triangle
    (labeling.midpoint_endpoint_adj_of_mem_midpointEquationSet
      m hm p hpEquation)
    hreflectedMiddle
    (labeling.midpoint_middle_adj_reference_from_matching m hm p).symm

/-- Matching-equation form of the same obstruction: the midpoint equation and
the reflected-middle matching equation cannot both hold. -/
theorem not_midpoint_reflected_middle_matching_of_mem_midpointEquationSet
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hpEquation : p ∈ labeling.midpointEquationSet m hm) :
    AFiberCoordinates.matchingEquiv h.isMoore
        labeling.data.toAFiberCoordinates (0 + (m + m)) (0 + m)
        (midpoint_reflectedReference_index_ne_middle hm)
        (labeling.midpointReflectionCoordPerm m p) ≠
      labeling.midpointExceptionMiddleMate m hm p := by
  intro hmatch
  exact
    (labeling.not_midpoint_middle_adj_reflected_reference_of_mem_midpointEquationSet
      m hm p hpEquation)
    (labeling.midpoint_middle_adj_reflected_reference_of_reflected_middle_matching
      m hm p hmatch)

/-- Boundary form saying no A-fixing support coordinate satisfies the midpoint
equation.  This is strictly smaller than reflected-middle matching: it rules
out the premise of the equation-to-matching boundary rather than restating its
conclusion. -/
structure MidpointExceptionDoublingNoSupportMidpointEquationBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_mem_midpointEquationSet_of_mem_support :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          p ∉ labeling.midpointEquationSet m hm

namespace MidpointExceptionDoublingNoSupportMidpointEquationBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- If the midpoint-equation premise is empty on the A-fixing support, the
equation-to-reflected-middle boundary is vacuous. -/
def toMidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary
    (boundary :
      MidpointExceptionDoublingNoSupportMidpointEquationBoundary labeling) :
    MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary labeling where
  midpoint_reflected_middle_matching_of_midpointEquation := by
    intro m hm p hpSupport hpEquation
    exact False.elim
      ((boundary.not_mem_midpointEquationSet_of_mem_support
        m hm p hpSupport) hpEquation)

end MidpointExceptionDoublingNoSupportMidpointEquationBoundary

namespace MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The existing endpoint pointwise non-adjacency boundary proves that no
A-fixing support coordinate can satisfy the midpoint equation. -/
def toMidpointExceptionDoublingNoSupportMidpointEquationBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionDoublingNoSupportMidpointEquationBoundary labeling where
  not_mem_midpointEquationSet_of_mem_support := by
    intro m hm p hpSupport hpEquation
    exact
      (labeling.midpoint_endpoints_not_adj_of_endpointPointwiseNonadj
        boundary m hm p hpSupport)
      (labeling.midpoint_endpoint_adj_of_mem_midpointEquationSet
        m hm p hpEquation)

/-- Endpoint pointwise non-adjacency supplies the current equation-form
reflected-middle boundary vacuously, via no midpoint equations on support. -/
def toMidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary
    (boundary :
      MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary labeling) :
    MidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary labeling :=
  boundary.toMidpointExceptionDoublingNoSupportMidpointEquationBoundary
    |>.toMidpointExceptionDoublingMiddleReflectedAdjFromEquationBoundary

end MidpointExceptionAFixingSupportEndpointPointwiseNonadjBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
