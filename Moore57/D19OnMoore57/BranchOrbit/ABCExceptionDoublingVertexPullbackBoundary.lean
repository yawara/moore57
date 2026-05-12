import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingCoordinateBoundary

/-!
# Vertex pullback boundary for doubling midpoint exceptions

This file weakens the coordinate fixedness-pullback boundary to a vertex-level
statement.  The bridge is the coordinate-permutation equality iff for the
midpoint reflection on its middle fiber.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionDoublingVertexPullbackBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionDoublingVertexPullbackBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Coordinate equality for the midpoint reflection on the middle fiber is
equivalent to fixedness/equality of the represented middle-fiber vertices. -/
theorem midpointMiddleCoordPerm_eq_iff
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p q : labeling.data.toAFiberCoordinates.P) :
    labeling.midpointMiddleCoordPerm m p = q ↔
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          (((labeling.data.toAFiberCoordinates.coord (0 + m) p :
            {x : V // x ∈
              branchFiber Γ labeling.data.toAFiberCoordinates.u
                (labeling.data.toAFiberCoordinates.a (0 + m))}) : V)) =
        (((labeling.data.toAFiberCoordinates.coord (0 + m) q :
          {x : V // x ∈
            branchFiber Γ labeling.data.toAFiberCoordinates.u
              (labeling.data.toAFiberCoordinates.a (0 + m))}) : V)) := by
  have hmiddle : (2 : ZMod 19) * m - (0 + m) = 0 + m := by
    ring
  have hiff :=
    AFiberReflectionEquivariance.coordPerm_eq_iff
      (ref := labeling.toAFiberMidpointReflectionEquivariance m)
      (i := 0 + m) p q
  rw [hmiddle] at hiff
  simpa [midpointMiddleCoordPerm] using hiff

/-- Vertex-level fixedness pullback sufficient for the coordinate-level
midpoint-exception doubling boundary.

For a reference coordinate in the A-fixing moving support, fixedness of the
vertex represented by the doubled middle mate pulls back to fixedness of the
vertex represented by the original middle mate. -/
structure MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_middle_vertex_fixed_pullback :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          h.smul
              (DihedralGroup.sr
                (labeling.midpointReflectionIndex
                  ((2 : ZMod 19) * m)))
              (((labeling.data.toAFiberCoordinates.coord
                  (0 + ((2 : ZMod 19) * m))
                  (labeling.midpointExceptionMiddleMate
                    ((2 : ZMod 19) * m)
                    (two_mul_ne_zero_zmod19 hm) p) :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a
                      (0 + ((2 : ZMod 19) * m)))}) : V)) =
            (((labeling.data.toAFiberCoordinates.coord
                (0 + ((2 : ZMod 19) * m))
                (labeling.midpointExceptionMiddleMate
                  ((2 : ZMod 19) * m)
                  (two_mul_ne_zero_zmod19 hm) p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a
                    (0 + ((2 : ZMod 19) * m)))}) : V)) →
          h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
              (((labeling.data.toAFiberCoordinates.coord (0 + m)
                  (labeling.midpointExceptionMiddleMate m hm p) :
                {x : V // x ∈
                  branchFiber Γ labeling.data.toAFiberCoordinates.u
                    (labeling.data.toAFiberCoordinates.a (0 + m))}) : V)) =
            (((labeling.data.toAFiberCoordinates.coord (0 + m)
                (labeling.midpointExceptionMiddleMate m hm p) :
              {x : V // x ∈
                branchFiber Γ labeling.data.toAFiberCoordinates.u
                  (labeling.data.toAFiberCoordinates.a (0 + m))}) : V))

namespace MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The vertex fixedness pullback gives the existing coordinate fixedness
pullback by the midpoint-middle coordinate equality iff. -/
def toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    (boundary :
      MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary labeling) :
    MidpointExceptionDoublingMiddleFixedPullbackBoundary labeling where
  midpoint_middle_fixed_pullback := by
    intro m hm p hpSupport hpDoubleFixed
    apply
      (labeling.midpointMiddleCoordPerm_eq_iff m
        (labeling.midpointExceptionMiddleMate m hm p)
        (labeling.midpointExceptionMiddleMate m hm p)).2
    apply boundary.midpoint_middle_vertex_fixed_pullback m hm p hpSupport
    exact
      (labeling.midpointMiddleCoordPerm_eq_iff ((2 : ZMod 19) * m)
        (labeling.midpointExceptionMiddleMate
          ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p)
        (labeling.midpointExceptionMiddleMate
          ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p)).1
        hpDoubleFixed

/-- The vertex fixedness pullback supplies the pointwise middle-support
membership transport. -/
def toMidpointExceptionDoublingMiddleMembershipBoundary
    (boundary :
      MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary labeling) :
    MidpointExceptionDoublingMiddleMembershipBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    |>.toMidpointExceptionDoublingMiddleMembershipBoundary

/-- The vertex fixedness pullback supplies the existing geometric doubling
boundary. -/
def toMidpointExceptionDoublingGeometryBoundary
    (boundary :
      MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary labeling) :
    MidpointExceptionDoublingGeometryBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    |>.toMidpointExceptionDoublingGeometryBoundary

/-- The vertex fixedness pullback supplies the action-level doubling boundary
consumed by the case split. -/
def toMidpointExceptionDoublingBoundary
    (boundary :
      MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary labeling) :
    MidpointExceptionDoublingBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    |>.toMidpointExceptionDoublingBoundary

end MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
