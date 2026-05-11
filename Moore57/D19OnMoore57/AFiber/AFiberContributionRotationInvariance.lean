import Moore57.D19OnMoore57.AFiber.AFiberAllFibersCardinalityBoundary

/-!
# Rotation invariance of A-fiber adjacent-moved counts

For a fixed nonzero rotation step `d`, the adjacent-moved count in the
`i`-th A-fiber is independent of `i`: rotation by `k` transports the filtered
set in fiber `i` to the filtered set in fiber `i + k`.  This lets the
all-A-fiber cardinality boundary be supplied by checking one reference fiber.
-/

namespace Moore57

open Finset

noncomputable section

universe u uP

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

local instance instAFiberContributionRotationInvariancePFintype
    (coords : AFiberCoordinates.{u, uP} Γ) : Fintype coords.P :=
  coords.P_fintype

local instance instAFiberContributionRotationInvarianceDecidableEq
    (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace D19ActsOnMoore57

variable (h : D19ActsOnMoore57 V Γ)

/-- Rotations in the cyclic subgroup commute on vertices. -/
theorem rotation_comm_apply (d k : ZMod 19) (x : V) :
    h.rotation k (h.rotation d x) =
      h.rotation d (h.rotation k x) := by
  calc
    h.rotation k (h.rotation d x)
        = (h.rotation k * h.rotation d) x := by
          simp [Equiv.Perm.mul_apply]
    _ = h.rotation (k + d) x := by
          rw [← h.rotation_add]
    _ = h.rotation (d + k) x := by
          rw [add_comm]
    _ = (h.rotation d * h.rotation k) x := by
          rw [h.rotation_add]
    _ = h.rotation d (h.rotation k x) := by
          simp [Equiv.Perm.mul_apply]

/-- Rotation by `-k` after rotation by `k` is the identity on vertices. -/
theorem rotation_neg_apply_rotation_cancel (k : ZMod 19) (x : V) :
    h.rotation (-k) (h.rotation k x) = x := by
  calc
    h.rotation (-k) (h.rotation k x)
        = (h.rotation (-k) * h.rotation k) x := by
          simp [Equiv.Perm.mul_apply]
    _ = h.rotation ((-k) + k) x := by
          rw [← h.rotation_add]
    _ = x := by
          simp

/-- Rotation by `k` after rotation by `-k` is the identity on vertices. -/
theorem rotation_apply_neg_rotation_cancel (k : ZMod 19) (x : V) :
    h.rotation k (h.rotation (-k) x) = x := by
  calc
    h.rotation k (h.rotation (-k) x)
        = (h.rotation k * h.rotation (-k)) x := by
          simp [Equiv.Perm.mul_apply]
    _ = h.rotation (k + (-k)) x := by
          rw [← h.rotation_add]
    _ = x := by
          simp

end D19ActsOnMoore57

namespace AFiberRotationEquivariance

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- Rotation by `k` transports the adjacent-`d` filtered part of fiber `i`
to the adjacent-`d` filtered part of fiber `i + k`. -/
noncomputable def fiberAdjacentRotationEquiv
    (rot : AFiberRotationEquivariance h coords)
    (d i k : ZMod 19) :
    {y : V // y ∈ coords.fiber i ∧ Γ.Adj y (h.rotation d y)} ≃
      {y : V // y ∈ coords.fiber (i + k) ∧ Γ.Adj y (h.rotation d y)} where
  toFun y := by
    refine ⟨h.rotation k y.1, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [add_comm] using rot.rotation_mem_fiber_of_mem k i y.2.1
    · have hyAdj :
          Γ.Adj (h.rotation k y.1)
            (h.rotation k (h.rotation d y.1)) := by
        simpa [D19ActsOnMoore57.rotation] using
          (h.smul_adj (DihedralGroup.r k) y.1 (h.rotation d y.1)).mp y.2.2
      simpa [h.rotation_comm_apply d k y.1] using hyAdj
  invFun y := by
    refine ⟨h.rotation (-k) y.1, ?_⟩
    refine ⟨?_, ?_⟩
    · have hyMem :
          h.rotation (-k) y.1 ∈ coords.fiber ((i + k) + (-k)) :=
        rot.rotation_mem_fiber_of_mem (-k) (i + k) y.2.1
      simpa [add_assoc] using hyMem
    · have hyAdj :
          Γ.Adj (h.rotation (-k) y.1)
            (h.rotation (-k) (h.rotation d y.1)) := by
        simpa [D19ActsOnMoore57.rotation] using
          (h.smul_adj (DihedralGroup.r (-k)) y.1 (h.rotation d y.1)).mp y.2.2
      simpa [h.rotation_comm_apply d (-k) y.1] using hyAdj
  left_inv y := by
    ext
    exact h.rotation_neg_apply_rotation_cancel k y.1
  right_inv y := by
    ext
    exact h.rotation_apply_neg_rotation_cancel k y.1

/-- The adjacent-`d` filtered cardinality is independent of the fiber index,
up to translating the index by a rotation. -/
theorem fiber_filter_adjacent_rotation_card_eq_shift
    (rot : AFiberRotationEquivariance h coords)
    (d i k : ZMod 19) :
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
      ((coords.fiber (i + k)).filter fun y =>
        Γ.Adj y (h.rotation d y)).card := by
  classical
  let e := rot.fiberAdjacentRotationEquiv d i k
  calc
    ((coords.fiber i).filter fun y => Γ.Adj y (h.rotation d y)).card =
        Fintype.card {y : V // y ∈ coords.fiber i ∧
          Γ.Adj y (h.rotation d y)} := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext y
      simp
    _ = Fintype.card {y : V // y ∈ coords.fiber (i + k) ∧
          Γ.Adj y (h.rotation d y)} :=
      Fintype.card_congr e
    _ = ((coords.fiber (i + k)).filter fun y =>
          Γ.Adj y (h.rotation d y)).card := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext y
      simp

/-- The support-complement cardinality of `matchingRotationPerm d i` is
independent of the fiber index. -/
theorem matchingRotationPerm_support_compl_card_eq_shift
    (rot : AFiberRotationEquivariance h coords)
    (d i k : ZMod 19) (hd : d ≠ 0) :
    (rot.matchingRotationPerm d i hd).supportᶜ.card =
      (rot.matchingRotationPerm d (i + k) hd).supportᶜ.card := by
  rw [← fiber_filter_adjacent_rotation_card_eq_matchingRotationPerm_support_compl_card
      rot d i hd,
    ← fiber_filter_adjacent_rotation_card_eq_matchingRotationPerm_support_compl_card
      rot d (i + k) hd]
  exact rot.fiber_filter_adjacent_rotation_card_eq_shift d i k

end AFiberRotationEquivariance

namespace AFiberCardinality38Boundary

variable {h : D19ActsOnMoore57 V Γ}
variable {coords : AFiberCoordinates.{u, uP} Γ}

/-- Full-A-fiber constructor from checking the matching-rotation fixed count
on the reference fiber `0` only. -/
noncomputable def of_allFibers_matchingRotationPerm_zero_support_compl_card_eq_two
    (rot : AFiberRotationEquivariance h coords)
    (hfixed_zero :
      ∀ d : ZMod 19, ∀ hd : d ≠ 0,
        (rot.matchingRotationPerm d 0 hd).supportᶜ.card = 2) :
    AFiberCardinality38Boundary h coords
      (Finset.univ : Finset (ZMod 19)) :=
  of_allFibers_matchingRotationPerm_support_compl_card_eq_two rot (by
    intro d hd i
    calc
      (rot.matchingRotationPerm d i hd).supportᶜ.card =
          (rot.matchingRotationPerm d (0 + i) hd).supportᶜ.card := by
            simp
      _ = (rot.matchingRotationPerm d 0 hd).supportᶜ.card := by
            exact (rot.matchingRotationPerm_support_compl_card_eq_shift
              d 0 i hd).symm
      _ = 2 := hfixed_zero d hd)

end AFiberCardinality38Boundary

end

end Moore57
