import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

namespace Moore57

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

theorem two_ne_zero_zmod19 : (2 : ZMod 19) ≠ 0 := by
  intro h
  have hdiv : 19 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 19).mp h
  norm_num at hdiv

theorem two_is_unit_zmod19 : IsUnit (2 : ZMod 19) := by
  exact isUnit_iff_ne_zero.mpr two_ne_zero_zmod19

theorem two_pow_ne_zero_zmod19 (k : Nat) :
    ((2 : ZMod 19) ^ k) ≠ 0 := by
  exact pow_ne_zero k two_ne_zero_zmod19

theorem two_pow_nine_zmod19 :
    ((2 : ZMod 19) ^ 9) = -1 := by
  norm_num
  change ((512 : Int) : ZMod 19) = ((-1 : Int) : ZMod 19)
  rw [ZMod.intCast_eq_intCast_iff]
  norm_num [Int.ModEq]

theorem two_pow_eighteen_zmod19 :
    ((2 : ZMod 19) ^ 18) = 1 := by
  norm_num
  change ((262144 : Int) : ZMod 19) = ((1 : Int) : ZMod 19)
  rw [ZMod.intCast_eq_intCast_iff]
  norm_num [Int.ModEq]

theorem two_pow_add_nine_zmod19 (k : Nat) :
    ((2 : ZMod 19) ^ (k + 9)) = -((2 : ZMod 19) ^ k) := by
  rw [pow_add, two_pow_nine_zmod19, mul_neg_one]

theorem two_pow_add_eighteen_zmod19 (k : Nat) :
    ((2 : ZMod 19) ^ (k + 18)) = ((2 : ZMod 19) ^ k) := by
  rw [pow_add, two_pow_eighteen_zmod19, mul_one]

theorem two_mul_ne_zero_zmod19 {a : ZMod 19} (ha : a ≠ 0) :
    (2 : ZMod 19) * a ≠ 0 := by
  exact mul_ne_zero two_ne_zero_zmod19 ha

theorem two_pow_mul_ne_zero_zmod19 {a : ZMod 19} (ha : a ≠ 0) (k : Nat) :
    ((2 : ZMod 19) ^ k) * a ≠ 0 := by
  exact mul_ne_zero (two_pow_ne_zero_zmod19 k) ha

theorem two_pow_nine_mul_zmod19 (a : ZMod 19) :
    ((2 : ZMod 19) ^ 9) * a = -a := by
  rw [two_pow_nine_zmod19, neg_one_mul]

theorem two_pow_eighteen_mul_zmod19 (a : ZMod 19) :
    ((2 : ZMod 19) ^ 18) * a = a := by
  rw [two_pow_eighteen_zmod19, one_mul]

theorem two_pow_add_nine_mul_zmod19 (k : Nat) (a : ZMod 19) :
    ((2 : ZMod 19) ^ (k + 9)) * a = -(((2 : ZMod 19) ^ k) * a) := by
  rw [two_pow_add_nine_zmod19, neg_mul]

theorem two_pow_add_eighteen_mul_zmod19 (k : Nat) (a : ZMod 19) :
    ((2 : ZMod 19) ^ (k + 18)) * a = ((2 : ZMod 19) ^ k) * a := by
  rw [two_pow_add_eighteen_zmod19]

theorem add_self_ne_zero_zmod19 {a : ZMod 19} (ha : a ≠ 0) :
    a + a ≠ 0 := by
  rw [← two_mul]
  exact two_mul_ne_zero_zmod19 ha

theorem neg_ne_self_zmod19 {a : ZMod 19} (ha : a ≠ 0) :
    -a ≠ a := by
  intro h
  exact add_self_ne_zero_zmod19 ha (by
    calc
      a + a = -a + a := by rw [h]
      _ = 0 := neg_add_cancel a)

theorem ne_neg_self_zmod19 {a : ZMod 19} (ha : a ≠ 0) :
    a ≠ -a := by
  exact (neg_ne_self_zmod19 ha).symm

theorem nonzero_mul_ne_zero_zmod19 {a b : ZMod 19} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  exact mul_ne_zero ha hb

end Moore57
