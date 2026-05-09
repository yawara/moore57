import Moore57.BranchOrbitABCExceptionDisjointBoundary

/-!
# Cardinality cases for midpoint exceptions meeting the A-fixing support

This file isolates the finite combinatorics behind the remaining
`S_h ∩ E = ∅` boundary.  The formal part is that
`S_h ∩ E` has cardinality at most two because `E` is the two-point
A-fixing reflection support; once the one- and two-point cases are excluded,
the intersection is empty and hence the finsets are disjoint.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionCaseBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionCaseBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- The finite intersection `S_m ∩ E`, where `S_m` is the midpoint-exception
set and `E` is the A-fixing reflection support on the reference A-fiber. -/
noncomputable def midpointExceptionAFixingSupportIntersection
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0) :
    Finset labeling.data.toAFiberCoordinates.P :=
  labeling.midpointExceptionSet m hm ∩ labeling.aFiberReflectionSupport

@[simp] theorem mem_midpointExceptionAFixingSupportIntersection
    (labeling : BranchOrbitABCReflectionLabeling h)
    (m : ZMod 19) (hm : m ≠ 0)
    (p : labeling.data.toAFiberCoordinates.P) :
    p ∈ labeling.midpointExceptionAFixingSupportIntersection m hm ↔
      p ∈ labeling.midpointExceptionSet m hm ∧
        p ∈ labeling.aFiberReflectionSupport := by
  simp [midpointExceptionAFixingSupportIntersection]

/-- Cardinality zero for the finite intersection is exactly the disjointness
needed by `MidpointExceptionDisjointAFixingSupportBoundary`. -/
theorem midpointException_disjoint_aFiberReflectionSupport_of_intersection_card_zero
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m : ZMod 19} {hm : m ≠ 0}
    (hcard :
      (labeling.midpointExceptionAFixingSupportIntersection m hm).card = 0) :
    Disjoint (labeling.midpointExceptionSet m hm)
      labeling.aFiberReflectionSupport := by
  classical
  rw [Finset.disjoint_iff_inter_eq_empty]
  rw [← Finset.card_eq_zero]
  simpa [midpointExceptionAFixingSupportIntersection] using hcard

/-- The intersection has size at most two because it is contained in the
two-point A-fixing reflection support. -/
theorem midpointExceptionAFixingSupportIntersection_card_le_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    (boundary : AFixingReflectionFixedNeighborCardBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection m hm).card ≤ 2 := by
  classical
  calc
    (labeling.midpointExceptionAFixingSupportIntersection m hm).card ≤
        labeling.aFiberReflectionSupport.card := by
          exact Finset.card_le_card (by
            intro p hp
            exact (Finset.mem_inter.mp hp).2)
    _ = 2 := boundary.aFiberReflectionSupport_card_two

/-- Boundary package for the two geometric exclusions still missing from the
case split.  The formal support-size input supplies `card ≤ 2`; the fields
exclude the only positive cardinalities left. -/
structure MidpointExceptionAFixingSupportCaseBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  support_card_boundary : AFixingReflectionFixedNeighborCardBoundary labeling
  no_card_one :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1
  no_card_two :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2

namespace MidpointExceptionAFixingSupportCaseBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The case boundary forces the intersection cardinality to be zero. -/
theorem intersection_card_zero
    (boundary : MidpointExceptionAFixingSupportCaseBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card = 0 := by
  have hle :
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≤ 2 :=
    labeling.midpointExceptionAFixingSupportIntersection_card_le_two
      boundary.support_card_boundary (midpointOf d) (midpointOf_ne_zero hd)
  have hne1 :
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
    boundary.no_card_one d hd
  have hne2 :
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2 :=
    boundary.no_card_two d hd
  omega

/-- The combinatorial case boundary gives the disjointness boundary used by
the downstream exception-disjoint pipeline. -/
def toMidpointExceptionDisjointAFixingSupportBoundary
    (boundary : MidpointExceptionAFixingSupportCaseBoundary labeling) :
    MidpointExceptionDisjointAFixingSupportBoundary labeling where
  midpointException_disjoint_aFiberReflectionSupport d hd := by
    exact
      labeling.midpointException_disjoint_aFiberReflectionSupport_of_intersection_card_zero
        (boundary.intersection_card_zero d hd)

end MidpointExceptionAFixingSupportCaseBoundary

end BranchOrbitABCReflectionLabeling

end

end Moore57
