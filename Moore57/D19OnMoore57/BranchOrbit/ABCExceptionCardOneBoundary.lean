import Moore57.D19OnMoore57.BranchOrbit.ABCExceptionCardTwoBoundary

/-!
# Boundary form for the one-point midpoint exception/support case

This file isolates the finite-set connector for excluding the remaining
`card = 1` case of `S_m ∩ E`, where `S_m` is the midpoint-exception set and
`E` is the A-fixing reflection support.  The geometric input can either be a
direct assertion that the intersection is never a singleton, or the more
natural reflection statement: if the intersection is a singleton, then its
unique point is fixed by the A-fixing reflection.  Since every point of the
intersection lies in the A-fixing reflection support, that fixedness
contradicts `p ∈ E ↔ θ p ≠ p`.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instExceptionCardOneBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instExceptionCardOneBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary input for excluding the one-point case: for every nonzero offset,
the corresponding `S_(d/2) ∩ E` is not a singleton. -/
structure MidpointExceptionAFixingSupportNoCardOneBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  not_singleton_intersection :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ¬ ∃ p : labeling.data.toAFiberCoordinates.P,
        labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) = {p}

namespace MidpointExceptionAFixingSupportNoCardOneBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- Convert the no-singleton boundary into the `no_card_one` field expected by
`MidpointExceptionAFixingSupportCaseBoundary`. -/
theorem no_card_one
    (boundary : MidpointExceptionAFixingSupportNoCardOneBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 := by
  intro hcard
  exact boundary.not_singleton_intersection d hd
    (labeling.exists_midpointExceptionAFixingSupportIntersection_eq_singleton_of_card_one
      hcard)

/-- Package constructor for the existing case boundary from a no-singleton
boundary, the A-fixing support-size boundary, and a card-two exclusion. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary : MidpointExceptionAFixingSupportNoCardOneBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (no_card_two :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2) :
    MidpointExceptionAFixingSupportCaseBoundary labeling where
  support_card_boundary := supportCard
  no_card_one := boundary.no_card_one
  no_card_two := no_card_two

end MidpointExceptionAFixingSupportNoCardOneBoundary

/-- Direct constructor for the existing case boundary from the assertion that
`S_(d/2) ∩ E` is never a singleton. -/
def midpointExceptionAFixingSupportCaseBoundary_of_not_singleton_intersection
    (labeling : BranchOrbitABCReflectionLabeling h)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (not_singleton_intersection :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ¬ ∃ p : labeling.data.toAFiberCoordinates.P,
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) = {p})
    (no_card_two :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  (MidpointExceptionAFixingSupportNoCardOneBoundary.mk
      not_singleton_intersection)
    |>.toMidpointExceptionAFixingSupportCaseBoundary supportCard no_card_two

/-- If a singleton intersection forced its unique point to be fixed by the
A-fixing reflection, then that singleton cannot occur: the point also lies in
the A-fixing reflection support, hence is moved by the same reflection. -/
theorem not_singleton_intersection_of_singleton_point_fixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (fixed_of_singleton :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) = {p} →
          labeling.aFiberReflectionCoordPerm p = p)
    (d : ZMod 19) (hd : d ≠ 0) :
    ¬ ∃ p : labeling.data.toAFiberCoordinates.P,
      labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) = {p} := by
  rintro ⟨p, hp_singleton⟩
  have hp_inter :
      p ∈ labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd) := by
    simp [hp_singleton]
  have hp_support : p ∈ labeling.aFiberReflectionSupport :=
    (labeling.mem_midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd) p).1 hp_inter |>.2
  have hp_moved : labeling.aFiberReflectionCoordPerm p ≠ p :=
    (labeling.mem_aFiberReflectionSupport p).1 hp_support
  exact hp_moved (fixed_of_singleton d hd p hp_singleton)

/-- Boundary input matching the geometric card-one story: singleton
intersections would have their unique point fixed by the A-fixing reflection.
The connector below turns this into the no-singleton boundary because points
of `E` are exactly the points moved by that reflection. -/
structure MidpointExceptionAFixingSupportSingletonFixedBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  fixed_of_singleton :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ∀ p : labeling.data.toAFiberCoordinates.P,
        labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd) = {p} →
        labeling.aFiberReflectionCoordPerm p = p

namespace MidpointExceptionAFixingSupportSingletonFixedBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

/-- The singleton-fixedness boundary gives the direct no-singleton boundary. -/
def toMidpointExceptionAFixingSupportNoCardOneBoundary
    (boundary :
      MidpointExceptionAFixingSupportSingletonFixedBoundary labeling) :
    MidpointExceptionAFixingSupportNoCardOneBoundary labeling where
  not_singleton_intersection :=
    labeling.not_singleton_intersection_of_singleton_point_fixed
      boundary.fixed_of_singleton

/-- Convert singleton-fixedness into the `no_card_one` field used by the
case boundary. -/
theorem no_card_one
    (boundary :
      MidpointExceptionAFixingSupportSingletonFixedBoundary labeling)
    (d : ZMod 19) (hd : d ≠ 0) :
    (labeling.midpointExceptionAFixingSupportIntersection
      (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 :=
  boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary.no_card_one d hd

/-- Package constructor for the existing case boundary from singleton
fixedness, the A-fixing support-size boundary, and a card-two exclusion. -/
def toMidpointExceptionAFixingSupportCaseBoundary
    (boundary :
      MidpointExceptionAFixingSupportSingletonFixedBoundary labeling)
    (supportCard : AFixingReflectionFixedNeighborCardBoundary labeling)
    (no_card_two :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (labeling.midpointExceptionAFixingSupportIntersection
          (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 2) :
    MidpointExceptionAFixingSupportCaseBoundary labeling :=
  boundary.toMidpointExceptionAFixingSupportNoCardOneBoundary
    |>.toMidpointExceptionAFixingSupportCaseBoundary supportCard no_card_two

end MidpointExceptionAFixingSupportSingletonFixedBoundary

/-- Direct `no_card_one` connector from the natural reflection fixedness
statement. -/
theorem no_card_one_of_singleton_point_fixed
    (labeling : BranchOrbitABCReflectionLabeling h)
    (fixed_of_singleton :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∀ p : labeling.data.toAFiberCoordinates.P,
          labeling.midpointExceptionAFixingSupportIntersection
            (midpointOf d) (midpointOf_ne_zero hd) = {p} →
          labeling.aFiberReflectionCoordPerm p = p) :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (labeling.midpointExceptionAFixingSupportIntersection
        (midpointOf d) (midpointOf_ne_zero hd)).card ≠ 1 := by
  intro d hd
  exact
    (MidpointExceptionAFixingSupportSingletonFixedBoundary.mk
        fixed_of_singleton).no_card_one d hd

end BranchOrbitABCReflectionLabeling

end

end Moore57
