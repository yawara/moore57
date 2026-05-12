import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionDoublingVertexPullbackBoundary
import Moore57.D19OnMoore57.Fixed.FixedCommonNeighbors

/-!
# Common-neighbor boundary for doubling midpoint exceptions

This file inserts a boundary between the vertex fixedness-pullback statement
and the underlying common-neighbor geometry.  It names the vertices involved
in the original and doubled middle mates, records the small midpoint-reflection
index identity used when comparing `m` and `2 * m`, and proves that explicit
swapped-endpoint common-neighbor hypotheses imply the existing vertex
fixedness-pullback boundary.
-/

namespace Moore57

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The reference A-fiber vertex represented by a coordinate `p`. -/
noncomputable def midpointExceptionReferenceVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  (((labeling.data.toAFiberCoordinates.coord 0 p :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a 0)}) : V))

/-- The endpoint obtained from the reference vertex by the midpoint reflection. -/
noncomputable def midpointExceptionReflectedReferenceVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (p : labeling.data.toAFiberCoordinates.P) : V :=
  (((labeling.data.toAFiberCoordinates.coord (0 + (m + m))
      (labeling.midpointReflectionCoordPerm m p) :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a (0 + (m + m)))}) : V))

/-- The original middle mate vertex in the fiber over `0 + m`. -/
noncomputable def midpointExceptionMiddleMateVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  (((labeling.data.toAFiberCoordinates.coord (0 + m)
      (labeling.midpointExceptionMiddleMate m hm p) :
    {x : V // x ∈
      branchFiber Γ labeling.data.toAFiberCoordinates.u
        (labeling.data.toAFiberCoordinates.a (0 + m))}) : V))

/-- The doubled middle mate vertex in the fiber over `0 + 2m`. -/
noncomputable def midpointExceptionDoubledMiddleMateVertex
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) : V :=
  labeling.midpointExceptionMiddleMateVertex
    ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p

/-- Vertex fixedness for the original middle mate. -/
def midpointExceptionMiddleMateVertexFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) : Prop :=
  h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
    (labeling.midpointExceptionMiddleMateVertex m hm p) =
      labeling.midpointExceptionMiddleMateVertex m hm p

/-- Vertex fixedness for the doubled middle mate. -/
def midpointExceptionDoubledMiddleMateVertexFixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) : Prop :=
  h.smul
    (DihedralGroup.sr
      (labeling.midpointReflectionIndex ((2 : ZMod 19) * m)))
    (labeling.midpointExceptionDoubledMiddleMateVertex m hm p) =
      labeling.midpointExceptionDoubledMiddleMateVertex m hm p

/-- The doubled midpoint-reflection parameter is the original one shifted by
`2 * m`. -/
theorem midpointReflectionIndex_two_mul
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    labeling.midpointReflectionIndex ((2 : ZMod 19) * m) =
      labeling.midpointReflectionIndex m - (2 : ZMod 19) * m := by
  simp [midpointReflectionIndex]
  ring

/-- Group form of `midpointReflectionIndex_two_mul`. -/
theorem midpointReflection_two_mul_eq_rotation_mul
    (labeling : BranchOrbitABCReflectionLabeling h) (m : ZMod 19) :
    DihedralGroup.sr
        (labeling.midpointReflectionIndex ((2 : ZMod 19) * m)) =
      DihedralGroup.r ((2 : ZMod 19) * m) *
        DihedralGroup.sr (labeling.midpointReflectionIndex m) := by
  rw [DihedralGroup.r_mul_sr]
  congr 1
  exact labeling.midpointReflectionIndex_two_mul m

/-- Common-neighbor uniqueness fixes the original middle mate once the
midpoint reflection swaps the two endpoint vertices, those endpoints are
non-adjacent and distinct, and the middle mate is their common neighbor. -/
theorem midpointExceptionMiddleMateVertexFixed_of_commonNeighbor
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hswap_left :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          (labeling.midpointExceptionReferenceVertex p) =
        labeling.midpointExceptionReflectedReferenceVertex m p)
    (hswap_right :
      h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
          (labeling.midpointExceptionReflectedReferenceVertex m p) =
        labeling.midpointExceptionReferenceVertex p)
    (hendpoints_ne :
      labeling.midpointExceptionReferenceVertex p ≠
        labeling.midpointExceptionReflectedReferenceVertex m p)
    (hendpoints_not_adj :
      ¬ Γ.Adj
        (labeling.midpointExceptionReferenceVertex p)
        (labeling.midpointExceptionReflectedReferenceVertex m p))
    (hmiddle_adj_ref :
      Γ.Adj
        (labeling.midpointExceptionReferenceVertex p)
        (labeling.midpointExceptionMiddleMateVertex m hm p))
    (hmiddle_adj_reflected :
      Γ.Adj
        (labeling.midpointExceptionReflectedReferenceVertex m p)
        (labeling.midpointExceptionMiddleMateVertex m hm p)) :
    labeling.midpointExceptionMiddleMateVertexFixed m hm p :=
  h.fixed_commonNeighbor_of_swap_not_adj
    (DihedralGroup.sr (labeling.midpointReflectionIndex m))
    hswap_left hswap_right hendpoints_ne hendpoints_not_adj
    ⟨hmiddle_adj_ref, hmiddle_adj_reflected⟩

/-- Boundary form of the explicit common-neighbor hypotheses needed to fix the
original middle mate for moved A-fixing support coordinates.  The doubled
fixedness premise is intentionally absent here: this is the stronger geometric
statement that makes the pullback conclusion automatic once the endpoint
common-neighbor picture has been supplied. -/
structure MidpointExceptionDoublingMiddleCommonNeighborBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpoint_endpoint_swap_left :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
              (labeling.midpointExceptionReferenceVertex p) =
            labeling.midpointExceptionReflectedReferenceVertex m p
  midpoint_endpoint_swap_right :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          h.smul (DihedralGroup.sr (labeling.midpointReflectionIndex m))
              (labeling.midpointExceptionReflectedReferenceVertex m p) =
            labeling.midpointExceptionReferenceVertex p
  midpoint_endpoints_ne :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          labeling.midpointExceptionReferenceVertex p ≠
            labeling.midpointExceptionReflectedReferenceVertex m p
  midpoint_endpoints_not_adj :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          ¬ Γ.Adj
            (labeling.midpointExceptionReferenceVertex p)
            (labeling.midpointExceptionReflectedReferenceVertex m p)
  midpoint_middle_adj_reference :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.midpointExceptionReferenceVertex p)
            (labeling.midpointExceptionMiddleMateVertex m hm p)
  midpoint_middle_adj_reflected_reference :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          Γ.Adj
            (labeling.midpointExceptionReflectedReferenceVertex m p)
            (labeling.midpointExceptionMiddleMateVertex m hm p)

namespace MidpointExceptionDoublingMiddleCommonNeighborBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The common-neighbor boundary proves original middle-mate fixedness
pointwise. -/
theorem midpoint_middle_mate_vertex_fixed
    (boundary :
      MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P)
    (hpSupport : p ∈ labeling.aFiberReflectionSupport) :
    labeling.midpointExceptionMiddleMateVertexFixed m hm p :=
  labeling.midpointExceptionMiddleMateVertexFixed_of_commonNeighbor m hm p
    (boundary.midpoint_endpoint_swap_left m hm p hpSupport)
    (boundary.midpoint_endpoint_swap_right m hm p hpSupport)
    (boundary.midpoint_endpoints_ne m hm p hpSupport)
    (boundary.midpoint_endpoints_not_adj m hm p hpSupport)
    (boundary.midpoint_middle_adj_reference m hm p hpSupport)
    (boundary.midpoint_middle_adj_reflected_reference m hm p hpSupport)

/-- Convert the explicit common-neighbor boundary into the existing vertex
fixedness-pullback boundary. -/
def toMidpointExceptionDoublingMiddleVertexFixedPullbackBoundary
    (boundary :
      MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling) :
    MidpointExceptionDoublingMiddleVertexFixedPullbackBoundary labeling where
  midpoint_middle_vertex_fixed_pullback := by
    intro m hm p hpSupport _hDoubleFixed
    exact boundary.midpoint_middle_mate_vertex_fixed m hm p hpSupport

/-- The common-neighbor boundary also supplies the existing coordinate
fixedness-pullback boundary. -/
def toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    (boundary :
      MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling) :
    MidpointExceptionDoublingMiddleFixedPullbackBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleVertexFixedPullbackBoundary
    |>.toMidpointExceptionDoublingMiddleFixedPullbackBoundary

/-- The common-neighbor boundary supplies the pointwise middle-support
membership transport. -/
def toMidpointExceptionDoublingMiddleMembershipBoundary
    (boundary :
      MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling) :
    MidpointExceptionDoublingMiddleMembershipBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    |>.toMidpointExceptionDoublingMiddleMembershipBoundary

/-- The common-neighbor boundary supplies the geometric doubling boundary. -/
def toMidpointExceptionDoublingGeometryBoundary
    (boundary :
      MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling) :
    MidpointExceptionDoublingGeometryBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    |>.toMidpointExceptionDoublingGeometryBoundary

/-- The common-neighbor boundary supplies the action-level doubling boundary
consumed downstream. -/
def toMidpointExceptionDoublingBoundary
    (boundary :
      MidpointExceptionDoublingMiddleCommonNeighborBoundary labeling) :
    MidpointExceptionDoublingBoundary labeling :=
  boundary.toMidpointExceptionDoublingMiddleFixedPullbackBoundary
    |>.toMidpointExceptionDoublingBoundary

end MidpointExceptionDoublingMiddleCommonNeighborBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
