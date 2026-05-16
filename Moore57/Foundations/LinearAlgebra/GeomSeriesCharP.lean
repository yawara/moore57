import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# (X - 1)^(p-1) = Σ_{k=0}^{p-1} X^k over F_p

`p` 素数 + char-p 環で `(X - 1)^{p-1} = 1 + X + X^2 + ... + X^{p-1}`.

証明: `X^p - 1 = (X - 1)^p` (Frobenius char-p) と
`(X - 1)(1 + X + ... + X^{p-1}) = X^p - 1` (geom_sum_mul) を比較し,
`X - 1 ≠ 0` で cancel.

応用: 任意の F_p-algebra 元 `a` に対し `(a - 1)^{p-1} = Σ a^k`.

## 主な結果

* `X_sub_one_pow_prime_sub_one_eq_geom_sum`: 多項式環上の identity.
* `sub_one_pow_prime_sub_one_eq_geom_sum`: aeval 経由で任意の F_p-algebra 元へ転送.
-/

namespace Moore57
namespace LinearAlgebra

open Polynomial Finset

/-- F_p 多項式環上の core identity: `(X - 1)^{p-1} = Σ_{k=0}^{p-1} X^k`. -/
theorem X_sub_one_pow_prime_sub_one_eq_geom_sum
    {p : ℕ} [Fact p.Prime] :
    ((Polynomial.X - 1 : Polynomial (ZMod p)))^(p - 1) =
      ∑ k ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p))^k := by
  haveI hp : Fact p.Prime := inferInstance
  have hp_pos : 0 < p := hp.out.pos
  haveI : CharP (Polynomial (ZMod p)) p := by
    haveI := ZMod.charP p
    exact charP_of_injective_ringHom
      (f := Polynomial.C (R := ZMod p)) Polynomial.C_injective p
  -- (X - 1)^p = X^p - 1 (Frobenius char p)
  have h1 : ((Polynomial.X - 1 : Polynomial (ZMod p)))^p = Polynomial.X^p - 1 := by
    have hX_one : (1 : Polynomial (ZMod p))^p = 1 := one_pow p
    have := sub_pow_char (R := Polynomial (ZMod p)) (p := p)
      (x := (Polynomial.X : Polynomial (ZMod p))) (y := (1 : Polynomial (ZMod p)))
    rw [hX_one] at this
    exact this
  -- (Σ X^k) (X - 1) = X^p - 1 (geom_sum_mul)
  have h2 : (∑ k ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p))^k) *
      (Polynomial.X - 1) = Polynomial.X^p - 1 :=
    geom_sum_mul Polynomial.X p
  -- (X - 1)^p = (X - 1) * (X - 1)^(p - 1)
  have h3 : ((Polynomial.X - 1 : Polynomial (ZMod p)))^p =
      (Polynomial.X - 1) * ((Polynomial.X - 1)^(p - 1)) := by
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
    calc ((Polynomial.X - 1 : Polynomial (ZMod p)))^p
        = ((Polynomial.X - 1 : Polynomial (ZMod p)))^(p - 1 + 1) := by rw [hp1]
      _ = ((Polynomial.X - 1 : Polynomial (ZMod p)))^(p - 1) * (Polynomial.X - 1) :=
          pow_succ _ _
      _ = (Polynomial.X - 1) * ((Polynomial.X - 1)^(p - 1)) := mul_comm _ _
  -- Equate: (X - 1) * (X - 1)^(p - 1) = (X - 1) * (Σ X^k)
  have h4 : (Polynomial.X - 1 : Polynomial (ZMod p)) * ((Polynomial.X - 1)^(p - 1)) =
      (Polynomial.X - 1) * (∑ k ∈ Finset.range p, Polynomial.X^k) := by
    rw [← h3, h1, ← h2, mul_comm]
  -- Cancel (X - 1) ≠ 0 (ZMod p is a field for p prime so Polynomial has no zero divisors)
  have h_ne_zero : (Polynomial.X - 1 : Polynomial (ZMod p)) ≠ 0 := by
    have h := Polynomial.X_sub_C_ne_zero (R := ZMod p) 1
    simpa using h
  exact mul_left_cancel₀ h_ne_zero h4

/-- F_p-algebra 元 `a` に対する identity 形: `(a - 1)^{p-1} = Σ a^k`. -/
theorem sub_one_pow_prime_sub_one_eq_geom_sum
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Ring R] [Algebra (ZMod p) R] (a : R) :
    (a - 1)^(p - 1) = ∑ k ∈ Finset.range p, a^k := by
  have h_poly := X_sub_one_pow_prime_sub_one_eq_geom_sum (p := p)
  have h_apply := congrArg (Polynomial.aeval a) h_poly
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one, map_sum] at h_apply
  exact h_apply

end LinearAlgebra
end Moore57
