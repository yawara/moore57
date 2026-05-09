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

theorem two_mul_ne_zero_zmod19 {a : ZMod 19} (ha : a ≠ 0) :
    (2 : ZMod 19) * a ≠ 0 := by
  exact mul_ne_zero two_ne_zero_zmod19 ha

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
