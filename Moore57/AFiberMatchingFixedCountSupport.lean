import Moore57.AFiberRotationMatchingCardinality

/-!
# A-fiber matching fixed counts as support complements

This file names the matching-then-rotation coordinate permutation used by
`AFiberRotationMatchingCardinality` and restates the fixed-count sums in forms
that are easier to feed into arithmetic arguments.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberCoordinatesPFintype
    (coords : AFiberCoordinates.{u, uP} Γ) : Fintype coords.P :=
  coords.P_fintype

local instance instClassicalDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace AFiberRotationEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- The coordinate permutation that detects vertices in the `i`-th A-fiber
adjacent to their rotation by `d`: first match from the `i`-fiber to the
`i + d`-fiber, then transport back along the rotation coordinate permutation. -/
noncomputable def matchingRotationPerm
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) : Equiv.Perm coords.P :=
  (AFiberCoordinates.matchingEquiv h.isMoore coords i (i + d)
      (index_ne_add_of_ne_zero hd)).trans
    (rot.coordPerm d i).symm

/-- The fixed-point count of the matching-rotation permutation as the
cardinality of its fixed subtype. -/
theorem fixedVertexCount_matchingRotationPerm_eq_fixedSubtype_card
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
        (rot.matchingRotationPerm d i hd) =
      Fintype.card {p : coords.P // rot.matchingRotationPerm d i hd p = p} := by
  classical
  letI := coords.P_fintype
  simpa using
    (fixedVertexCount_eq_fintype_card_fixedSubtype
      (σ := rot.matchingRotationPerm d i hd))

/-- The fixed-point count of the matching-rotation permutation as the
cardinality of the complement of its support. -/
theorem fixedVertexCount_matchingRotationPerm_eq_support_compl_card
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
        (rot.matchingRotationPerm d i hd) =
      (rot.matchingRotationPerm d i hd).supportᶜ.card := by
  classical
  letI := coords.P_fintype
  simpa using
    (D19ActsOnMoore57.fixedVertexCount_eq_support_compl_card
      (V := coords.P) (rot.matchingRotationPerm d i hd))

end AFiberRotationEquivariance

theorem fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_matchingRotationPerm
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
        (rot.matchingRotationPerm d i hd) := by
  simpa [AFiberRotationEquivariance.matchingRotationPerm] using
    fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_of_equivariance
      rot d i hd

theorem fiber_filter_adjacent_rotation_card_eq_matchingRotationPerm_fixedSubtype_card
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      Fintype.card {p : coords.P // rot.matchingRotationPerm d i hd p = p} := by
  rw [fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_matchingRotationPerm
    rot d i hd]
  exact
    AFiberRotationEquivariance.fixedVertexCount_matchingRotationPerm_eq_fixedSubtype_card
      rot d i hd

theorem fiber_filter_adjacent_rotation_card_eq_matchingRotationPerm_support_compl_card
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (d i : ZMod 19) (hd : d ≠ 0) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      (rot.matchingRotationPerm d i hd).supportᶜ.card := by
  rw [fiber_filter_adjacent_rotation_card_eq_fixedVertexCount_matchingRotationPerm
    rot d i hd]
  exact
    AFiberRotationEquivariance.fixedVertexCount_matchingRotationPerm_eq_support_compl_card
      rot d i hd

theorem fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_fixedVertexCount
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (indices : Finset (ZMod 19)) (d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberAFiberCard h (coords.fiberUnion indices) d =
      ∑ i ∈ indices,
        @fixedVertexCount coords.P (Classical.decEq coords.P) coords.P_fintype
          (rot.matchingRotationPerm d i hd) := by
  simpa [AFiberRotationEquivariance.matchingRotationPerm] using
    fixedAFiberAFiberCard_fiberUnion_eq_sum_fixedVertexCount
      rot indices d hd

theorem fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_fixedSubtype_card
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (indices : Finset (ZMod 19)) (d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberAFiberCard h (coords.fiberUnion indices) d =
      ∑ i ∈ indices,
        Fintype.card {p : coords.P // rot.matchingRotationPerm d i hd p = p} := by
  rw [fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_fixedVertexCount
    rot indices d hd]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    AFiberRotationEquivariance.fixedVertexCount_matchingRotationPerm_eq_fixedSubtype_card
      rot d i hd

theorem fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_support_compl_card
    {h : D19ActsOnMoore57 V Γ} {coords : AFiberCoordinates.{u, uP} Γ}
    (rot : AFiberRotationEquivariance h coords)
    (indices : Finset (ZMod 19)) (d : ZMod 19) (hd : d ≠ 0) :
    fixedAFiberAFiberCard h (coords.fiberUnion indices) d =
      ∑ i ∈ indices,
        (rot.matchingRotationPerm d i hd).supportᶜ.card := by
  rw [fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_fixedVertexCount
    rot indices d hd]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact
    AFiberRotationEquivariance.fixedVertexCount_matchingRotationPerm_eq_support_compl_card
      rot d i hd

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}
variable {indices : Finset (ZMod 19)}

/-- Build the boundary package from matching-rotation support-complement sums. -/
noncomputable def of_matchingSupportComplSum
    (rot : AFiberRotationEquivariance h coords)
    (hsum :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        ∑ i ∈ indices,
          (rot.matchingRotationPerm d i hd).supportᶜ.card = 38) :
    AFiberCardinality38Boundary h coords indices :=
  of_card_eq_thirtyEight (by
    intro d hd
    rw [fixedAFiberAFiberCard_fiberUnion_eq_sum_matchingRotationPerm_support_compl_card
      rot indices d hd]
    exact hsum d hd)

end AFiberCardinality38Boundary

end

end Moore57
