import Moore57.BranchOrbitABCDoublingCommonNeighborBoundary

/-!
# Basic common-neighbor facts for doubling midpoint exceptions

This file proves the definition-level parts of
`MidpointExceptionDoublingMiddleCommonNeighborBoundary`: the midpoint
reflection swaps the endpoint vertices, those endpoints are distinct, and the
reference endpoint is adjacent to its middle matching mate.  The remaining
geometric inputs are kept in a smaller boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The midpoint reflection sends the reference endpoint to the reflected
endpoint. -/
theorem midpoint_endpoint_swap_left_basic
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (_hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (_hpSupport : p ∈ labeling.aFiberReflectionSupport) :
    h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        (labeling.midpointExceptionReferenceVertex p) =
      labeling.midpointExceptionReflectedReferenceVertex m p := by
  have hidx : (2 : ZMod 19) * m - 0 = 0 + (m + m) := by
    ring
  change
    h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        (((labeling.data.toAFiberCoordinates.coord 0 p :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a 0)}) : V)) =
      (((labeling.data.toAFiberCoordinates.coord (0 + (m + m))
          (labeling.midpointReflectionCoordPerm m p) :
        {x : V // x ∈
          branchFiber Γ labeling.data.toAFiberCoordinates.u
            (labeling.data.toAFiberCoordinates.a (0 + (m + m)))}) : V))
  rw [← hidx]
  exact (labeling.coord_midpointReflectionCoordPerm_apply_val m p).symm

/-- Applying the midpoint reflection again sends the reflected endpoint back to
the reference endpoint. -/
theorem midpoint_endpoint_swap_right_basic
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hpSupport : p ∈ labeling.aFiberReflectionSupport) :
    h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
        (labeling.midpointExceptionReflectedReferenceVertex m p) =
      labeling.midpointExceptionReferenceVertex p := by
  rw [← labeling.midpoint_endpoint_swap_left_basic m hm p hpSupport]
  exact h.reflection_smul_reflection_smul
    (labeling.midpointReflectionIndex m)
    (labeling.midpointExceptionReferenceVertex p)

/-- The reference endpoint and its midpoint-reflection image lie over distinct
A-branches, hence are distinct vertices. -/
theorem midpoint_endpoints_ne_basic
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (_hpSupport : p ∈ labeling.aFiberReflectionSupport) :
    labeling.midpointExceptionReferenceVertex p ≠
      labeling.midpointExceptionReflectedReferenceVertex m p := by
  intro hxy
  let coords := labeling.data.toAFiberCoordinates
  have hxmem :
      labeling.midpointExceptionReferenceVertex p ∈
        branchFiber Γ coords.u (coords.a 0) := by
    simpa [midpointExceptionReferenceVertex, coords] using
      coords.coord_mem 0 p
  have hymem :
      labeling.midpointExceptionReflectedReferenceVertex m p ∈
        branchFiber Γ coords.u (coords.a (0 + (m + m))) := by
    simpa [midpointExceptionReflectedReferenceVertex, coords] using
      coords.coord_mem (0 + (m + m))
        (labeling.midpointReflectionCoordPerm m p)
  have h_adj_target :
      Γ.Adj (labeling.midpointExceptionReferenceVertex p)
        (coords.a (0 + (m + m))) := by
    have htarget :
        Γ.Adj (coords.a (0 + (m + m)))
          (labeling.midpointExceptionReflectedReferenceVertex m p) :=
      (mem_branchFiber.mp hymem).2
    simpa [hxy] using htarget.symm
  exact
    (h.isMoore.not_adj_other_branch_of_mem_branchFiber
      (coords.hub 0) (coords.hub (0 + (m + m)))
      (coords.a_ne
        (index_ne_add_of_ne_zero (add_self_ne_zero_zmod19 hm)))
      hxmem) h_adj_target

/-- The middle mate was defined as the matching mate of the reference endpoint,
so it is adjacent to the reference endpoint. -/
theorem midpoint_middle_adj_reference_basic
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (_hpSupport : p ∈ labeling.aFiberReflectionSupport) :
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

/-- Smaller boundary containing only the common-neighbor fields not discharged
by the definition-level midpoint-reflection and matching APIs. -/
structure MidpointExceptionDoublingMiddleCommonNeighborBasicBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_endpoints_not_adj :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬ Γ.Adj
            (labeling.midpointExceptionReferenceVertex p)
            (labeling.midpointExceptionReflectedReferenceVertex m p)
  midpoint_middle_adj_reflected_reference :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.midpointExceptionReflectedReferenceVertex m p)
            (labeling.midpointExceptionMiddleMateVertex m hm p)

namespace MidpointExceptionDoublingMiddleCommonNeighborBasicBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Fill the full common-neighbor boundary from the two remaining basic
boundary fields and the proved definition-level fields. -/
def toMidpointExceptionDoublingMiddleCommonNeighborBoundary
    (boundary :
      MidpointExceptionDoublingMiddleCommonNeighborBasicBoundary labeling) :
    MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling where
  midpoint_endpoint_swap_left := by
    intro m hm p hpSupport
    exact labeling.midpoint_endpoint_swap_left_basic m hm p hpSupport
  midpoint_endpoint_swap_right := by
    intro m hm p hpSupport
    exact labeling.midpoint_endpoint_swap_right_basic m hm p hpSupport
  midpoint_endpoints_ne := by
    intro m hm p hpSupport
    exact labeling.midpoint_endpoints_ne_basic m hm p hpSupport
  midpoint_endpoints_not_adj := boundary.midpoint_endpoints_not_adj
  midpoint_middle_adj_reference := by
    intro m hm p hpSupport
    exact labeling.midpoint_middle_adj_reference_basic m hm p hpSupport
  midpoint_middle_adj_reflected_reference :=
    boundary.midpoint_middle_adj_reflected_reference

end MidpointExceptionDoublingMiddleCommonNeighborBasicBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
