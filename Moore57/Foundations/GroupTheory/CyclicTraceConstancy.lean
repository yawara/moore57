import Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace

/-!
# Trace constancy for cyclic group action of prime order

任意の素数 `p` について, 有限次元 ℚ-vec `W` 上の Q-linear endomorphism `σ` で
`σ^p = 1` を満たすものについて, k = 1..p-1 で `tr(σ^k)` が一定である事を示す.

これは Tk_constant の rep theory 部分の抽象的核心.

主結果:
* `LinearMap.trace_pow_eq_of_pow_eq_one`: σ^p = 1, k, k' ∈ {1,...,p-1} のとき
  `tr σ^k = tr σ^k'`.

証明戦略:
* W = ker(σ - 1) ⊕ ker Φ_p(σ) (Bezout: X-1 と Φ_p は ℚ[X] で互いに素).
* ker(σ - 1) 上: σ = 1, σ^k = 1, trace = dim ker(σ - 1) (k によらず一定).
* ker Φ_p(σ) 上: `trace_package_of_cyclotomic_prime_aeval_eq_zero` を σ^k に適用.
  σ^k は k coprime to p なので同じ min poly Φ_p を持つ. 次元同じより γ が k に依らず一定.
-/

namespace Moore57

namespace LinearMap

open Polynomial

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

/-- σ^p = 1 のとき Φ_p(σ) を作用させた endomorphism の像は ker(σ - 1) に含まれる.
これは Bezout: (X-1) ⋅ Φ_p = X^p - 1 から従う. -/
private theorem range_aeval_cyclotomic_le_ker_sub_one
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (σ : W →ₗ[ℚ] W) (hσ : σ ^ p = 1) :
    LinearMap.range (Polynomial.aeval σ (Polynomial.cyclotomic p ℚ)) ≤
      LinearMap.ker (σ - 1) := by
  -- (X-1) * Φ_p = X^p - 1. aeval gives (σ - 1) ∘ Φ_p(σ) = σ^p - 1 = 0.
  rintro y ⟨x, rfl⟩
  -- (σ - 1) (Φ_p(σ) x) = (σ^p - 1) x = 0
  have h1 : ((Polynomial.X - 1 : ℚ[X]) * Polynomial.cyclotomic p ℚ) =
      ((Polynomial.X : ℚ[X]) ^ p - 1) := by
    rw [mul_comm]
    exact Polynomial.cyclotomic_prime_mul_X_sub_one ℚ p
  have h2 : Polynomial.aeval σ ((Polynomial.X - 1 : ℚ[X]) *
      Polynomial.cyclotomic p ℚ) = (σ ^ p - 1) := by
    rw [h1]
    rw [map_sub, Polynomial.aeval_X_pow, map_one]
  have h3 : Polynomial.aeval σ (Polynomial.X - 1 : ℚ[X]) *
      Polynomial.aeval σ (Polynomial.cyclotomic p ℚ) = σ ^ p - 1 := by
    rw [← map_mul, h2]
  have h4 : (σ - 1) ∘ₗ Polynomial.aeval σ (Polynomial.cyclotomic p ℚ) = σ ^ p - 1 := by
    rw [show Polynomial.aeval σ (Polynomial.X - 1 : ℚ[X]) = σ - 1 from by
      rw [map_sub, Polynomial.aeval_X, map_one]] at h3
    exact h3
  rw [hσ] at h4
  show (σ - 1) (Polynomial.aeval σ (Polynomial.cyclotomic p ℚ) x) = 0
  have : ((σ - 1) ∘ₗ Polynomial.aeval σ (Polynomial.cyclotomic p ℚ)) x = (0 : W →ₗ[ℚ] W) x := by
    rw [h4]; simp
  simpa using this

/-- σ^p = 1 のとき, W = ker(σ - 1) ⊕ ker Φ_p(σ) (Bezout による直和分解).

(X - 1) と Φ_p(X) は ℚ[X] で互いに素 (Bezout で 1 = a(X-1) + bΦ_p),
両者の積は X^p - 1 で σ^p = 1 より 0. -/
theorem isCompl_ker_sub_one_and_ker_aeval_cyclotomic
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (σ : W →ₗ[ℚ] W) (hσ : σ ^ p = 1) :
    IsCompl (LinearMap.ker (σ - 1)) (LinearMap.ker
      (Polynomial.aeval σ (Polynomial.cyclotomic p ℚ))) := by
  -- TODO (Stage 3 完了に必要): Bezout argument の Lean 化.
  -- 1 = a (X-1) + b Φ_p ⟹ id = a(σ)(σ-1) + b(σ)Φ_p(σ).
  -- intersection: σ v = v かつ Φ_p(σ) v = 0 ⟹ p v = 0 ⟹ v = 0.
  sorry

/-- **抽象 trace constancy theorem (Stage 3 ターゲット)**.

W が finite-dim ℚ-vec, σ : W →ₗ W が σ^p = 1 を満たすとき (p 素数),
k = 1..p-1 で `tr σ^k` は一定.

証明: W = ker(σ - 1) ⊕ ker Φ_p(σ) で分解.
* ker(σ - 1) 上 σ^k = 1, trace = dim ker(σ - 1).
* ker Φ_p(σ) 上 trace_package_of_cyclotomic_prime_aeval_eq_zero で trace = -γ.

これを使って Tk_constant に到達. -/
theorem trace_pow_eq_of_pow_eq_one
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (σ : W →ₗ[ℚ] W) (hσ : σ ^ p = 1)
    {j k : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) (hk1 : 1 ≤ k) (hkp : k < p) :
    LinearMap.trace ℚ W (σ ^ j) = LinearMap.trace ℚ W (σ ^ k) := by
  -- TODO (Stage 3 完了に必要): 上記分解 + trace_package を組み合わせて完成.
  sorry

end LinearMap

end Moore57
