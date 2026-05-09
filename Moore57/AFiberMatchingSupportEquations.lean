import Moore57.AFiberMatchingFixedCountSupport

/-!
# A-fiber matching support equations

This file rewrites the support-complement sums used for A-fiber cardinality
boundaries into explicit coordinate equations.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberMatchingSupportEquationsPFintype
    (coords : AFiberCoordinates.{u, uP} Γ) : Fintype coords.P :=
  coords.P_fintype

local instance instAFiberMatchingSupportEquationsDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace AFiberRotationEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- Expands the matching-rotation permutation on coordinates. -/
theorem matchingRotationPerm_apply
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) (p : coords.P) :
    rot.matchingRotationPerm d i hd p =
      (rot.coordPerm d i).symm
        (AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
          (index_ne_add_of_ne_zero hd) p) :=
  rfl

/-- A coordinate is fixed by the matching-rotation permutation exactly when
the matching coordinate agrees with the rotation transport coordinate. -/
theorem matchingRotationPerm_fixed_iff
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) (p : coords.P) :
    rot.matchingRotationPerm d i hd p = p ↔
      AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
          (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d i p := by
  rw [matchingRotationPerm_apply]
  exact
    (Equiv.symm_apply_eq (rot.coordPerm d i)
      (x := AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
        (index_ne_add_of_ne_zero hd) p)
      (y := p))

/-- Membership in the support complement of the matching-rotation permutation
as an explicit coordinate equation. -/
theorem mem_matchingRotationPerm_support_compl_iff
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) (p : coords.P) :
    p ∈ (rot.matchingRotationPerm d i hd).supportᶜ ↔
      AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
          (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d i p := by
  classical
  constructor
  · intro hp
    have hpnot : p ∉ (rot.matchingRotationPerm d i hd).support := by
      simpa using (Finset.mem_compl.mp hp)
    have hfixed : rot.matchingRotationPerm d i hd p = p := by
      by_contra hne
      exact hpnot ((Equiv.Perm.mem_support).mpr hne)
    exact (matchingRotationPerm_fixed_iff rot d i hd p).mp hfixed
  · intro hmatch
    rw [Finset.mem_compl]
    intro hsupport
    exact (Equiv.Perm.mem_support.mp hsupport)
      ((matchingRotationPerm_fixed_iff rot d i hd p).mpr hmatch)

/-- The support-complement cardinality as a filtered count of the explicit
coordinate equation. -/
theorem matchingRotationPerm_support_compl_card_eq_filter_card
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    (rot.matchingRotationPerm d i hd).supportᶜ.card =
      ((Finset.univ : Finset coords.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
            (index_ne_add_of_ne_zero hd) p =
          rot.coordPerm d i p).card := by
  apply congrArg Finset.card
  ext p
  rw [mem_matchingRotationPerm_support_compl_iff]
  simp

/-- A local support-complement upper bound gives the same upper bound for the
explicit matching-equation solution set. -/
theorem matchingEquationFilter_card_le_two_of_support_compl_card_le_two
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0)
    (hle : (rot.matchingRotationPerm d i hd).supportᶜ.card ≤ 2) :
    ((Finset.univ : Finset coords.P).filter fun p =>
      AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
          (index_ne_add_of_ne_zero hd) p =
        rot.coordPerm d i p).card ≤ 2 := by
  rw [← matchingRotationPerm_support_compl_card_eq_filter_card rot d i hd]
  exact hle

end AFiberRotationEquivariance

theorem fiber_filter_adjacent_rotation_card_eq_matchingRotationPerm_filter_card
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      ((Finset.univ : Finset coords.P).filter fun p =>
        AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
            (index_ne_add_of_ne_zero hd) p =
          rot.coordPerm d i p).card := by
  rw [fiber_filter_adjacent_rotation_card_eq_matchingRotationPerm_support_compl_card
    rot d i hd]
  exact
    AFiberRotationEquivariance.matchingRotationPerm_support_compl_card_eq_filter_card
      rot d i hd

theorem fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_filter_card
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (indices : Finset (ZMod 19)) (d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberAFiberCard h (coords.fiberUnion indices) d =
      ∑ i ∈ indices,
        ((Finset.univ : Finset coords.P).filter fun p =>
          AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
              (index_ne_add_of_ne_zero hd) p =
            rot.coordPerm d i p).card := by
  rw [fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_support_compl_card
    rot indices d hd]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    AFiberRotationEquivariance.matchingRotationPerm_support_compl_card_eq_filter_card
      rot d i hd

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Build the boundary package from explicit coordinate-equation filter sums. -/
noncomputable def of_matchingEquationFilterCardSum
    (rot : AFiberRotationEquivariance h coords)
    (hsum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          ((Finset.univ : Finset coords.P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd) p =
              rot.coordPerm d i p).card = 38) :
    AFiberCardinality38Boundary h coords indices :=
  of_card_eq_thirtyEight (by
    intro d hd
    rw [fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_filter_card
      rot indices d hd]
    exact hsum d hd)

/-- Build the boundary package when each selected matching-rotation
permutation has exactly two fixed coordinates. -/
noncomputable def of_matchingRotationPerm_support_compl_card_eq_two
    (rot : AFiberRotationEquivariance h coords)
    (hindices : indices.card = 19)
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        i ∈ indices → (rot.matchingRotationPerm d i hd).supportᶜ.card = 2) :
    AFiberCardinality38Boundary h coords indices :=
  of_matchingSupportComplSum rot (by
    intro d hd
    calc
      ∑ i ∈ indices, (rot.matchingRotationPerm d i hd).supportᶜ.card =
          ∑ i ∈ indices, 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hfixed d hd i hi
      _ = 38 := by
            rw [Finset.sum_const, hindices]
            norm_num)

/-- Build the boundary package from the weaker local condition that each
selected matching-rotation permutation has at most two fixed coordinates,
together with a matching lower bound on the support-complement sum. -/
noncomputable def of_matchingRotationPerm_support_compl_card_le_two_of_sum_ge
    (rot : AFiberRotationEquivariance h coords)
    (hindices : indices.card = 19)
    (hfixed_le :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        i ∈ indices → (rot.matchingRotationPerm d i hd).supportᶜ.card ≤ 2)
    (hsum_ge :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        38 ≤
          ∑ i ∈ indices,
            (rot.matchingRotationPerm d i hd).supportᶜ.card) :
    AFiberCardinality38Boundary h coords indices :=
  of_matchingSupportComplSum rot (by
    intro d hd
    have hsum_le :
        ∑ i ∈ indices, (rot.matchingRotationPerm d i hd).supportᶜ.card ≤
          38 := by
      calc
        ∑ i ∈ indices, (rot.matchingRotationPerm d i hd).supportᶜ.card ≤
            ∑ i ∈ indices, 2 := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact hfixed_le d hd i hi
        _ = 38 := by
              rw [Finset.sum_const, hindices]
              norm_num
    exact le_antisymm hsum_le (hsum_ge d hd))

/-- Build the boundary package when each selected explicit coordinate equation
has exactly two solutions. -/
noncomputable def of_matchingEquationFilterCard_eq_two
    (rot : AFiberRotationEquivariance h coords)
    (hindices : indices.card = 19)
    (hfixed :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0, ∀ i : ZMod 19,
        i ∈ indices →
          ((Finset.univ : Finset coords.P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd) p =
              rot.coordPerm d i p).card = 2) :
    AFiberCardinality38Boundary h coords indices :=
  of_matchingEquationFilterCardSum rot (by
    intro d hd
    calc
      ∑ i ∈ indices,
          ((Finset.univ : Finset coords.P).filter fun p =>
            AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
                (index_ne_add_of_ne_zero hd) p =
              rot.coordPerm d i p).card =
          ∑ i ∈ indices, 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hfixed d hd i hi
      _ = 38 := by
            rw [Finset.sum_const, hindices]
            norm_num)

end AFiberCardinality38Boundary

end

end Moore57
