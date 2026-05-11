import Moore57.Foundations.GroupAction.FixedPointBasics
import Mathlib.Algebra.Field.ZMod

namespace Moore57

theorem fixedVertexSet_pow_of_mem {V : Type*} {σ : Equiv.Perm V} {v : V}
    (hv : v ∈ fixedVertexSet σ) (n : ℕ) :
    v ∈ fixedVertexSet (σ ^ n) := by
  induction n with
  | zero =>
      simp [fixedVertexSet]
  | succ n ih =>
      rw [mem_fixedVertexSet] at hv ih ⊢
      rw [pow_succ]
      simp [Equiv.Perm.mul_apply, hv, ih]

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Natural scalar multiplication in the additive rotation parameter corresponds
to taking powers of the induced permutation. -/
theorem rotation_nsmul (h : D19ActsOnMoore57 V Γ) (n : ℕ) (d : ZMod 19) :
    h.rotation (n • d) = h.rotation d ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, h.rotation_add, ih, pow_succ]

/-- In `ZMod 19`, every element is a natural multiple of any nonzero element. -/
theorem exists_nsmul_eq_of_ne_zero {d e : ZMod 19} (hd : d ≠ 0) :
    ∃ n : ℕ, n • d = e := by
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  refine ⟨(e * d⁻¹).val, ?_⟩
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  calc
    (e * d⁻¹) * d = e * (d⁻¹ * d) := by rw [mul_assoc]
    _ = e * 1 := by rw [inv_mul_cancel₀ hd]
    _ = e := by rw [mul_one]

/-- If two rotation parameters are natural multiples of each other, their fixed
vertex sets coincide. -/
theorem fixedVertexSet_rotation_eq_of_mutual_nsmul
    (h : D19ActsOnMoore57 V Γ) {d e : ZMod 19}
    (hde : ∃ n : ℕ, n • d = e) (hed : ∃ m : ℕ, m • e = d) :
    fixedVertexSet (h.rotation d) = fixedVertexSet (h.rotation e) := by
  rcases hde with ⟨n, hn⟩
  rcases hed with ⟨m, hm⟩
  ext v
  constructor
  · intro hv
    have hpow : v ∈ fixedVertexSet (h.rotation d ^ n) :=
      fixedVertexSet_pow_of_mem hv n
    have hrot : h.rotation e = h.rotation d ^ n := by
      rw [← hn, h.rotation_nsmul]
    simpa [hrot] using hpow
  · intro hv
    have hpow : v ∈ fixedVertexSet (h.rotation e ^ m) :=
      fixedVertexSet_pow_of_mem hv m
    have hrot : h.rotation d = h.rotation e ^ m := by
      rw [← hm, h.rotation_nsmul]
    simpa [hrot] using hpow

/-- All nontrivial rotations of the order-19 rotation subgroup have the same
fixed vertex set. -/
theorem fixedVertexSet_rotation_eq_of_nonzero
    (h : D19ActsOnMoore57 V Γ) {d e : ZMod 19} (hd : d ≠ 0) (he : e ≠ 0) :
    fixedVertexSet (h.rotation d) = fixedVertexSet (h.rotation e) :=
  h.fixedVertexSet_rotation_eq_of_mutual_nsmul
    (exists_nsmul_eq_of_ne_zero hd)
    (exists_nsmul_eq_of_ne_zero he)

end D19ActsOnMoore57

end Moore57
