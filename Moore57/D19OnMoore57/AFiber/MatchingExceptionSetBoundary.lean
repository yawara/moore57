import Moore57.D19OnMoore57.AFiber.MatchingSupportEquations
import Moore57.D19OnMoore57.AFiber.ContributionRotationInvariance

/-!
# Reference A-fiber matching exception-set boundary

This file exposes the midpoint-reflection step in a weak, reusable form: for
each nonzero rotation offset, the reference matching equation has its solutions
inside a two-point exception set.  Exact two-solution statements can be added
later; this boundary already gives the support-complement upper bound consumed
by existing A-fiber cardinality constructors.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberMatchingExceptionSetBoundaryPFintype
    (coords : AFiberCoordinates.{u, uP} Γ) : Fintype coords.P :=
  coords.P_fintype

local instance instAFiberMatchingExceptionSetBoundaryDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Weak reference-fiber boundary for the matching equation: for every nonzero
rotation offset, the reference matching equation solution set is contained in a
two-point exception set. -/
structure ReferenceFiberMatchingExceptionSetTwo
    {h : D19ActsOnMoore57 V Γ}
    {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords) where
  exceptionSet :
    ∀ d : ZMod 19, d ≠ 0 → Finset coords.P
  exception_card_two :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      (exceptionSet d hd).card = 2
  reference_matching_subset_exception :
    ∀ d : ZMod 19, ∀ hd : d ≠ 0,
      ((Finset.univ : Finset coords.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore coords
            0 (0 + d) (index_ne_add_of_ne_zero hd) p =
          rot.coordPerm d 0 p) ⊆
        exceptionSet d hd

namespace ReferenceFiberMatchingExceptionSetTwo

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {rot : AFiberRotationEquivariance h coords}

/-- The reference matching-equation solution set has cardinality at most two. -/
theorem referenceMatchingEquation_card_le_two
    (boundary : ReferenceFiberMatchingExceptionSetTwo rot)
    (d : ZMod 19) (hd : d ≠ 0) :
    ((Finset.univ : Finset coords.P).filter fun p =>
      AFiberCoordinates.matchingEquiv h.isMoore coords
          0 (0 + d) (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d 0 p).card ≤ 2 := by
  calc
    ((Finset.univ : Finset coords.P).filter fun p =>
      AFiberCoordinates.matchingEquiv h.isMoore coords
          0 (0 + d) (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d 0 p).card ≤
        (boundary.exceptionSet d hd).card :=
      Finset.card_le_card (boundary.reference_matching_subset_exception d hd)
    _ = 2 := by
      rw [boundary.exception_card_two d hd]

/-- The reference matching-rotation support complement has cardinality at most
two. -/
theorem referenceMatchingSupportCompl_card_le_two
    (boundary : ReferenceFiberMatchingExceptionSetTwo rot)
    (d : ZMod 19) (hd : d ≠ 0) :
    (rot.matchingRotationPerm d 0 hd).supportᶜ.card ≤ 2 := by
  rw [AFiberRotationEquivariance.matchingRotationPerm_support_compl_card_eq_filter_card
    rot d 0 hd]
  exact boundary.referenceMatchingEquation_card_le_two d hd

/-- By rotation invariance, the support-complement upper bound holds on every
A-fiber index. -/
theorem matchingSupportCompl_card_le_two
    (boundary : ReferenceFiberMatchingExceptionSetTwo rot)
    (d : ZMod 19) (hd : d ≠ 0) (i : ZMod 19) :
    (rot.matchingRotationPerm d i hd).supportᶜ.card ≤ 2 := by
  calc
    (rot.matchingRotationPerm d i hd).supportᶜ.card =
        (rot.matchingRotationPerm d (0 + i) hd).supportᶜ.card := by
      simp
    _ = (rot.matchingRotationPerm d 0 hd).supportᶜ.card := by
      exact (rot.matchingRotationPerm_support_compl_card_eq_shift
        d 0 i hd).symm
    _ ≤ 2 := boundary.referenceMatchingSupportCompl_card_le_two d hd

end ReferenceFiberMatchingExceptionSetTwo

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- Full-A-fiber boundary from a reference two-point exception-set upper bound
and the existing lower bound on the total support-complement sum. -/
noncomputable def of_allFibers_referenceMatchingExceptionSetTwo_of_sum_ge
    (rot : AFiberRotationEquivariance h coords)
    (boundary : ReferenceFiberMatchingExceptionSetTwo rot)
    (hsum_ge :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        38 ≤
          ∑ i ∈ (Finset.univ : Finset (ZMod 19)),
            (rot.matchingRotationPerm d i hd).supportᶜ.card) :
    AFiberCardinality38Boundary h coords
      (Finset.univ : Finset (ZMod 19)) :=
  of_matchingRotationPerm_support_compl_card_le_two_of_sum_ge rot
    (by simp)
    (by
      intro d hd i _hi
      exact boundary.matchingSupportCompl_card_le_two d hd i)
    hsum_ge

end AFiberCardinality38Boundary

end

end Moore57
