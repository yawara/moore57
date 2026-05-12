import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionDoublingGeometry

/-!
# Coordinate boundary for doubling midpoint exceptions

This file gives a coordinate-level version of the midpoint-exception doubling
gap.  The existing geometric boundary asks directly for membership transport
from the middle moving support at `m` to the middle moving support at `2 * m`.
Here we isolate a slightly stronger fixedness-pullback statement on the actual
middle coordinate permutations.  Since membership in `midpointMiddleSupport`
is just non-fixedness of `midpointMiddleCoordPerm`, the pullback statement
implies the existing geometric boundary by contrapositive.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionDoublingCoordinateBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionDoublingCoordinateBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The middle matching mate used in the definition of `midpointExceptionSet`.

This names the coordinate map whose support-membership transport is the hard
part of the doubling step. -/
noncomputable def midpointExceptionMiddleMate
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0) :
    Equiv.Perm labeling.data.toAFiberCoordinates.P :=
  AFiberCoordinates.matchingEquiv h.isMoore
    labeling.data.toAFiberCoordinates 0 (0 + m)
    (index_ne_add_of_ne_zero hm)

/-- Coordinate fixedness pullback sufficient for midpoint-exception doubling.

For a reference coordinate in the A-fixing moving support, if the doubled
middle mate is fixed by the doubled midpoint reflection, then the original
middle mate is fixed by the original midpoint reflection.  Taking the
contrapositive transports membership in the moving middle support from `m` to
`2 * m`. -/
structure MidpointExceptionDoublingMiddleFixedPullbackBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_middle_fixed_pullback :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.midpointMiddleCoordPerm ((2 : ZMod 19) * m)
              (labeling.midpointExceptionMiddleMate
                ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p) =
            labeling.midpointExceptionMiddleMate
              ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p →
          labeling.midpointMiddleCoordPerm m
              (labeling.midpointExceptionMiddleMate m hm p) =
            labeling.midpointExceptionMiddleMate m hm p

/-- Pointwise middle-support membership transport.  This is the direct
membership-level form consumed by `MidpointExceptionDoublingGeometryBoundary`,
but stated through the named middle-mate coordinate map. -/
structure MidpointExceptionDoublingMiddleMembershipBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_middle_membership_double :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.midpointExceptionMiddleMate m hm p ∈
            labeling.midpointMiddleSupport m →
          labeling.midpointExceptionMiddleMate
              ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p ∈
            labeling.midpointMiddleSupport ((2 : ZMod 19) * m)

namespace MidpointExceptionDoublingMiddleMembershipBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the named middle-mate membership transport into the existing
geometric boundary. -/
def toMidpointExceptionDoublingGeometryBoundary
    (boundary :
      MidpointExceptionDoublingMiddleMembershipBoundary labeling) :
    MidpointExceptionDoublingGeometryBoundary labeling where
  midpoint_middle_support_double := by
    intro m hm p hpSupport hpMiddle
    simpa [midpointExceptionMiddleMate] using
      boundary.midpoint_middle_membership_double m hm p hpSupport
        (by simpa [midpointExceptionMiddleMate] using hpMiddle)

/-- Convert the pointwise membership transport directly to the action-level
doubling boundary. -/
def toMidpointExceptionDoublingBoundary
    (boundary :
      MidpointExceptionDoublingMiddleMembershipBoundary labeling) :
    MidpointExceptionDoublingBoundary labeling :=
  boundary.toMidpointExceptionDoublingGeometryBoundary
    |>.toMidpointExceptionDoublingBoundary

end MidpointExceptionDoublingMiddleMembershipBoundary

namespace MidpointExceptionDoublingMiddleFixedPullbackBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The fixedness-pullback coordinate boundary implies the pointwise
middle-support membership transport by contrapositive. -/
def toMidpointExceptionDoublingMiddleMembershipBoundary
    (boundary :
      MidpointExceptionDoublingMiddleFixedPullbackBoundary labeling) :
    MidpointExceptionDoublingMiddleMembershipBoundary labeling where
  midpoint_middle_membership_double := by
    intro m hm p hpSupport hpMiddle
    have hpMiddleMoved :
        labeling.midpointMiddleCoordPerm m
            (labeling.midpointExceptionMiddleMate m hm p) ≠
          labeling.midpointExceptionMiddleMate m hm p :=
      (labeling.mem_midpointMiddleSupport m
        (labeling.midpointExceptionMiddleMate m hm p)).1 hpMiddle
    have hpDoubleMoved :
        labeling.midpointMiddleCoordPerm ((2 : ZMod 19) * m)
            (labeling.midpointExceptionMiddleMate
              ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p) ≠
          labeling.midpointExceptionMiddleMate
            ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p := by
      intro hpDoubleFixed
      exact hpMiddleMoved
        (boundary.midpoint_middle_fixed_pullback m hm p hpSupport
          hpDoubleFixed)
    exact
      (labeling.mem_midpointMiddleSupport ((2 : ZMod 19) * m)
        (labeling.midpointExceptionMiddleMate
          ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p)).2
        hpDoubleMoved

/-- The fixedness-pullback coordinate boundary supplies the existing geometric
doubling boundary. -/
def toMidpointExceptionDoublingGeometryBoundary
    (boundary :
      MidpointExceptionDoublingMiddleFixedPullbackBoundary labeling) :
    MidpointExceptionDoublingGeometryBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleMembershipBoundary
    |>.toMidpointExceptionDoublingGeometryBoundary

/-- The fixedness-pullback coordinate boundary supplies the action-level
doubling boundary consumed by the case split. -/
def toMidpointExceptionDoublingBoundary
    (boundary :
      MidpointExceptionDoublingMiddleFixedPullbackBoundary labeling) :
    MidpointExceptionDoublingBoundary labeling :=
  boundary.toMidpointExceptionDoublingGeometryBoundary
    |>.toMidpointExceptionDoublingBoundary

end MidpointExceptionDoublingMiddleFixedPullbackBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
