import Moore57.D19OnMoore57.BranchOrbit.BranchOrbitABCExceptionCaseBoundary

/-!
# Boundary form for the two-point midpoint exception/support case

This file isolates the purely finite-set part of the remaining
`S_m ∩ E` card-two geometry.  If the intersection with the two-point
A-fixing reflection support also has cardinality two, then the whole
support is contained in the midpoint-exception set.  Thus a geometric
boundary excluding `E ⊆ S_m` gives the `no_card_two` field used by
`MidpointExceptionAFixingSupportCaseBoundary`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionCardTwoBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionCardTwoBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- If `S_m ∩ E` has the same cardinality as `E`, then the two finsets agree
on `E`: every A-fixing moved coordinate belongs to the midpoint-exception
set. -/
theorem aFiberReflectionSupport_subset_midpointExceptionSet_of_intersection_card_eq
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m : ZMod 19} {hm : m ≠ 0}
    (hcard :
      (labeling.midpointExceptionAFixingSupportIntersection m hm).card =
        labeling.aFiberReflectionSupport.card) :
    labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm := by
  classical
  have hsubset :
      labeling.midpointExceptionAFixingSupportIntersection m hm ⊆
        labeling.aFiberReflectionSupport := by
    intro p hp
    exact (labeling.mem_midpointExceptionAFixingSupportIntersection m hm p).1 hp |>.2
  have heq :
      labeling.midpointExceptionAFixingSupportIntersection m hm =
        labeling.aFiberReflectionSupport := by
    exact Finset.eq_of_subset_of_card_le hsubset (by rw [hcard])
  intro p hp
  have hp_inter :
      p ∈ labeling.midpointExceptionAFixingSupportIntersection m hm := by
    simpa [heq] using hp
  exact (labeling.mem_midpointExceptionAFixingSupportIntersection m hm p).1 hp_inter |>.1

/-- Card-two connector: if both `S_m ∩ E` and `E` have cardinality two, then
all of `E` lies in `S_m`. -/
theorem aFiberReflectionSupport_subset_midpointExceptionSet_of_intersection_card_two
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m : ZMod 19} {hm : m ≠ 0}
    (hintersection :
      (labeling.midpointExceptionAFixingSupportIntersection m hm).card = 2)
    (hsupport : labeling.aFiberReflectionSupport.card = 2) :
    labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm := by
  exact
    labeling.aFiberReflectionSupport_subset_midpointExceptionSet_of_intersection_card_eq
      (by rw [hintersection, hsupport])

/-- The same card-two connector using the existing A-fixing support-size
boundary. -/
theorem aFiberReflectionSupport_subset_midpointExceptionSet_of_intersection_card_two'
    (labeling : BranchOrbitABCReflectionLabeling h)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    {m : ZMod 19} {hm : m ≠ 0}
    (hintersection :
      (labeling.midpointExceptionAFixingSupportIntersection m hm).card = 2) :
    labeling.aFiberReflectionSupport ⊆ labeling.midpointExceptionSet m hm := by
  exact
    labeling.aFiberReflectionSupport_subset_midpointExceptionSet_of_intersection_card_two
      hintersection supportCard.aFiberReflectionSupport_card_two

/-- Boundary input for excluding the two-point case: for every nonzero offset,
the whole A-fixing reflection support is not contained in the corresponding
midpoint-exception set. -/
structure MidpointExceptionAFixingSupportNoCardTwoBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_all_support_subset_exception :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ labeling.aFiberReflectionSupport ⊆
        labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)

namespace MidpointExceptionAFixingSupportNoCardTwoBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the geometric non-containment boundary into the `no_card_two`
field expected by `MidpointExceptionAFixingSupportCaseBoundary`. -/
theorem no_card_two
    (boundary : MidpointExceptionAFixingSupportNoCardTwoBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2 := by
  intro hcard
  exact boundary.not_all_support_subset_exception d hd
    (labeling.aFiberReflectionSupport_subset_midpointExceptionSet_of_intersection_card_two'
      supportCard hcard)

/-- Package constructor for the existing case boundary from `no_card_one`,
the A-fixing support-size boundary, and the geometric non-containment
statement excluding card two. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary : MidpointExceptionAFixingSupportNoCardTwoBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1) :
    MidpointExceptionAFixingSupportCaseBoundary labeling where
  support_card_boundary := supportCard
  no_card_one := no_card_one
  no_card_two := boundary.no_card_two supportCard

end MidpointExceptionAFixingSupportNoCardTwoBoundary

/-- Direct constructor for `MidpointExceptionAFixingSupportCaseBoundary` from
the non-containment statement `¬ E ⊆ S_(d/2)`. -/
def midpointExceptionAFixingSupportCaseBoundary_of_not_all_support_subset_exception
    (labeling : BranchOrbitABCReflectionLabeling h)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (no_card_one :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1)
    (not_all_support_subset_exception :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ¬ labeling.aFiberReflectionSupport ⊆
          labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  (MidpointExceptionAFixingSupportNoCardTwoBoundary.mk
      not_all_support_subset_exception)
    |>.toMidpointExceptionAFixingSupportCaseBoundary supportCard no_card_one

/-- Optional singleton helper: card one for `S_m ∩ E` supplies a point whose
singleton is exactly that intersection. -/
theorem exists_midpointExceptionAFixingSupportIntersection_eq_singleton_of_card_one
    (labeling : BranchOrbitABCReflectionLabeling h)
    {m : ZMod 19} {hm : m ≠ 0}
    (hcard :
      (labeling.midpointExceptionAFixingSupportIntersection m hm).card = 1) :
    ∃ p : labeling.data.toAFiberCoordinates.P,
      labeling.midpointExceptionAFixingSupportIntersection m hm = {p} := by
  exact Finset.card_eq_one.mp hcard

end BranchOrbitABCReflectionLabeling

end

end Moore57
