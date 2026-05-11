import Moore57.D19OnMoore57.Rotation.RotationBranchFiberPerm
import Moore57.Foundations.ZMod19.Lemmas

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The fixed part of a branch fiber is nonempty when the rotation fixes the endpoints. -/
theorem card_fixedBranchFiberFinset_rotation_ne_zero
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b) (hub : Γ.Adj u b) :
    (h.fixedBranchFiberFinset d u b).card ≠ 0 := by
  have hmod := h.card_fixedBranchFiberFinset_rotation_modEq_fiftySix d hu hb hub
  by_contra hzero
  rw [hzero] at hmod
  norm_num at hmod

/-- The fixed part of a branch fiber has at least `18` vertices under a fixed rotation. -/
theorem eighteen_le_card_fixedBranchFiberFinset_rotation
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19) {u b : V}
    (hu : h.rotation d u = u) (hb : h.rotation d b = b) (hub : Γ.Adj u b) :
    18 ≤ (h.fixedBranchFiberFinset d u b).card := by
  let n := (h.fixedBranchFiberFinset d u b).card
  have hmod : n ≡ 56 [MOD 19] :=
    h.card_fixedBranchFiberFinset_rotation_modEq_fiftySix d hu hb hub
  by_contra hnot
  have hnlt : n < 18 := Nat.lt_of_not_ge hnot
  have hnlt19 : n < 19 := lt_trans hnlt (by norm_num)
  have hmod18 : n ≡ 18 [MOD 19] := by
    norm_num [Nat.ModEq] at hmod ⊢
    exact hmod
  have heq : n = 18 := Nat.ModEq.eq_of_lt_of_lt hmod18 hnlt19 (by norm_num)
  omega

end D19ActsOnMoore57

end Moore57
