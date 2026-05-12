import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionDoublingBoundary

/-!
# Geometric input for doubling midpoint exceptions on the A-fixing support

This file records the missing geometry behind the natural-language inclusion
`S_m ∩ E ⊆ S_{2m} ∩ E`, where `S_m` is `midpointExceptionSet m` and `E` is
`aFiberReflectionSupport`.

The existing midpoint-exception API expands membership in `S_m` to a middle
matching mate lying in `midpointMiddleSupport m`.  There is not currently an
API theorem transporting that middle-support membership from `m` to `2 * m`
for points in `E`; the boundary below isolates exactly that compatibility.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionDoublingGeometryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionDoublingGeometryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Geometric compatibility needed to prove midpoint-exception doubling on the
A-fixing support.

The field is the expanded form of the natural-language implication
`p ∈ S_m ∩ E → p ∈ S_{2m} ∩ E`: since `p ∈ S_m` means
`matchingEquiv 0 (0 + m) p ∈ midpointMiddleSupport m`, the field states that
for `p ∈ E` this middle-support membership doubles to
`matchingEquiv 0 (0 + 2m) p ∈ midpointMiddleSupport (2m)`. -/
structure MidpointExceptionDoublingGeometryBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  /-- Natural-language formula:
  `p ∈ E ∧ q_m(p) ∈ supp(τ_m on L_m) →
    q_{2m}(p) ∈ supp(τ_{2m} on L_{2m})`.

  Here `E` is `aFiberReflectionSupport`, `q_m(p)` is the matching mate
  `matchingEquiv 0 (0 + m) p`, and `supp(τ_m on L_m)` is
  `midpointMiddleSupport m`. -/
  midpoint_middle_support_double :
    ∀ m : ZMod 19, ∀ hm : m ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        p ∈ labeling.aFiberReflectionSupport →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates 0 (0 + m)
              (index_ne_add_of_ne_zero hm) p ∈
            labeling.midpointMiddleSupport m →
          AFiberCoordinates.matchingEquiv h.isMoore
              labeling.data.toAFiberCoordinates
              0 (0 + ((2 : ZMod 19) * m))
              (index_ne_add_of_ne_zero (two_mul_ne_zero_zmod19 hm)) p ∈
            labeling.midpointMiddleSupport ((2 : ZMod 19) * m)

namespace MidpointExceptionDoublingGeometryBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The geometric middle-support compatibility gives the packaged finite-set
doubling inclusion `S_m ∩ E ⊆ S_{2m} ∩ E`. -/
theorem double_subset
    (boundary : MidpointExceptionDoublingGeometryBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0) :
    labeling.midpointExceptionAFixingSupportIntersection m hm ⊆
      labeling.midpointExceptionAFixingSupportIntersection
        ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) := by
  intro p hp
  rcases (labeling.mem_midpointExceptionAFixingSupportIntersection m hm p).1 hp
    with ⟨hpException, hpSupport⟩
  have hpMiddle :
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates 0 (0 + m)
          (index_ne_add_of_ne_zero hm) p ∈
        labeling.midpointMiddleSupport m :=
    (labeling.mem_midpointExceptionSet m hm p).1 hpException
  have hpDoubleMiddle :
      AFiberCoordinates.matchingEquiv h.isMoore
          labeling.data.toAFiberCoordinates
          0 (0 + ((2 : ZMod 19) * m))
          (index_ne_add_of_ne_zero (two_mul_ne_zero_zmod19 hm)) p ∈
        labeling.midpointMiddleSupport ((2 : ZMod 19) * m) :=
    boundary.midpoint_middle_support_double m hm p hpSupport hpMiddle
  have hpDoubleException :
      p ∈ labeling.midpointExceptionSet
        ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) :=
    (labeling.mem_midpointExceptionSet
      ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p).2
      hpDoubleMiddle
  exact
    (labeling.mem_midpointExceptionAFixingSupportIntersection
      ((2 : ZMod 19) * m) (two_mul_ne_zero_zmod19 hm) p).2
      ⟨hpDoubleException, hpSupport⟩

/-- Constructor from the geometric compatibility boundary to the existing
`MidpointExceptionDoublingBoundary` consumed by the action-level argument. -/
def toMidpointExceptionDoublingBoundary
    (boundary : MidpointExceptionDoublingGeometryBoundary labeling) :
    MidpointExceptionDoublingBoundary labeling where
  double_subset := boundary.double_subset

end MidpointExceptionDoublingGeometryBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
