import Moore57.BranchOrbitABCMidpointReflection

/-!
# Reference exception sets from midpoint reflections

This file connects the midpoint-reflection criterion to the existing reference
matching exception-set boundary.  The only remaining non-formal input is the
comparison between the reference rotation equation and the midpoint reflection
equation.
-/

namespace Moore57

open Finset

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instMidpointExceptionSetBoundaryPFintype
    {h : D19ActsOnMoore57 V Γ}
    (labeling : BranchOrbitABCReflectionLabeling h) :
    Fintype labeling.data.toAFiberCoordinates.P :=
  labeling.data.toAFiberCoordinates.P_fintype

local instance instMidpointExceptionSetBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- The midpoint index for an offset `d`, using that `2` is invertible in
`ZMod 19`. -/
noncomputable def midpointOf (d : ZMod 19) : ZMod 19 :=
  (2 : ZMod 19)⁻¹ * d

theorem two_mul_midpointOf (d : ZMod 19) :
    (2 : ZMod 19) * midpointOf d = d := by
  dsimp [midpointOf]
  rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero_zmod19, one_mul]

theorem midpointOf_add_self (d : ZMod 19) :
    midpointOf d + midpointOf d = d := by
  rw [← two_mul, two_mul_midpointOf]

theorem midpointOf_ne_zero {d : ZMod 19} (hd : d ≠ 0) :
    midpointOf d ≠ 0 := by
  intro hm
  apply hd
  rw [← two_mul_midpointOf d, hm, mul_zero]

namespace BranchOrbitABCReflectionLabeling

variable {h : D19ActsOnMoore57 V Γ}

/-- Boundary saying the midpoint reflection has a two-point moving support on
each nonzero middle A-fiber. -/
structure MidpointMiddleSupportCardTwoBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  midpointMiddleSupport_card_two :
    ∀ m : ZMod 19, ∀ _hm : m ≠ 0,
      (labeling.midpointMiddleSupport m).card = 2

namespace MidpointMiddleSupportCardTwoBoundary

variable {labeling : BranchOrbitABCReflectionLabeling h}

theorem midpointExceptionSet_card_two
    (cardTwo : MidpointMiddleSupportCardTwoBoundary labeling)
    (m : ZMod 19) (hm : m ≠ 0) :
    (labeling.midpointExceptionSet m hm).card = 2 := by
  calc
    (labeling.midpointExceptionSet m hm).card =
        (labeling.midpointMiddleSupport m).card :=
          labeling.midpointExceptionSet_card_eq_midpointMiddleSupport_card m hm
    _ = 2 := cardTwo.midpointMiddleSupport_card_two m hm

end MidpointMiddleSupportCardTwoBoundary

/-- Boundary comparing the existing reference rotation equation with the
midpoint reflection equation at `midpointOf d`. -/
structure ReferenceRotationToMidpointReflectionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h) : Prop where
  reference_matching_subset_midpoint_equation :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ : Finset labeling.data.toAFiberCoordinates.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore
            labeling.data.toAFiberCoordinates 0 (0 + d)
            (index_ne_add_of_ne_zero hd) p =
          labeling.data.toAFiberRotationEquivariance.coordPerm d 0 p) ⊆
        labeling.midpointEquationSet (midpointOf d) (midpointOf_ne_zero hd)

end BranchOrbitABCReflectionLabeling

namespace ReferenceFiberMatchingExceptionSetTwo

variable {h : D19ActsOnMoore57 V Γ}

/-- Build the existing reference two-point exception-set boundary from the
midpoint-reflection criterion, the two-point midpoint support bound, and the
comparison from the reference rotation equation to the midpoint equation. -/
noncomputable def of_midpointReflectionBoundary
    (labeling : BranchOrbitABCReflectionLabeling h)
    (criterion :
      BranchOrbitABCReflectionLabeling.MidpointReflectionCriterionBoundary
        labeling)
    (cardTwo :
      BranchOrbitABCReflectionLabeling.MidpointMiddleSupportCardTwoBoundary
        labeling)
    (rhs :
      BranchOrbitABCReflectionLabeling.ReferenceRotationToMidpointReflectionBoundary
        labeling) :
    ReferenceFiberMatchingExceptionSetTwo
      labeling.data.toAFiberRotationEquivariance where
  exceptionSet d hd :=
    labeling.midpointExceptionSet (midpointOf d) (midpointOf_ne_zero hd)
  exception_card_two d hd :=
    cardTwo.midpointExceptionSet_card_two (midpointOf d) (midpointOf_ne_zero hd)
  reference_matching_subset_exception d hd := by
    intro p hp
    have hpEq :
        p ∈ labeling.midpointEquationSet
          (midpointOf d) (midpointOf_ne_zero hd) :=
      rhs.reference_matching_subset_midpoint_equation d hd hp
    exact
      (criterion.midpoint_equation_iff_exception
        (midpointOf d) (midpointOf_ne_zero hd) p).1 hpEq

end ReferenceFiberMatchingExceptionSetTwo

end

end Moore57
