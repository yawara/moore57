import Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace
import Mathlib.Algebra.DirectSum.LinearMap

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

/-- (X - 1) と Φ_p (cyclotomic p) は ℚ[X] で互いに素. -/
theorem isCoprime_X_sub_one_cyclotomic
    (p : ℕ) [hp : Fact (Nat.Prime p)] :
    IsCoprime ((Polynomial.X : ℚ[X]) - 1) (Polynomial.cyclotomic p ℚ) := by
  -- Φ_p(1) = p ≠ 0 in ℚ, so X - 1 doesn't divide Φ_p, hence coprime.
  have hΦp_one : (Polynomial.cyclotomic p ℚ).eval 1 = (p : ℚ) := by
    rw [Polynomial.cyclotomic_prime ℚ p]
    simp
  set Q := Polynomial.cyclotomic p ℚ
  have hp_ne : (p : ℚ) ≠ 0 := by
    have hp_pos : 0 < p := hp.out.pos
    exact_mod_cast hp_pos.ne'
  let b : ℚ[X] := Polynomial.C (1 / (p : ℚ))
  have hb_eval : (b * Q).eval 1 = 1 := by
    simp [b, hΦp_one, hp_ne]
  have hroot : ((1 : ℚ[X]) - b * Q).IsRoot 1 := by
    show ((1 : ℚ[X]) - b * Q).eval 1 = 0
    simp [hb_eval]
  obtain ⟨a, ha⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  refine ⟨a, b, ?_⟩
  -- ha : 1 - b * Q = (X - C 1) * a
  -- Goal: a * (X - 1) + b * Q = 1
  have hC1 : (Polynomial.C 1 : ℚ[X]) = 1 := Polynomial.C_1
  rw [hC1] at ha
  linear_combination -ha

/-- σ^p = 1 のとき, W = ker(σ - 1) ⊕ ker Φ_p(σ) (Bezout による直和分解).

(X - 1) と Φ_p(X) は ℚ[X] で互いに素 (Bezout で 1 = a(X-1) + bΦ_p),
両者の積は X^p - 1 で σ^p = 1 より 0. -/
theorem isCompl_ker_sub_one_and_ker_aeval_cyclotomic
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (σ : W →ₗ[ℚ] W) (hσ : σ ^ p = 1) :
    IsCompl (LinearMap.ker (σ - 1)) (LinearMap.ker
      (Polynomial.aeval σ (Polynomial.cyclotomic p ℚ))) := by
  have hcop := isCoprime_X_sub_one_cyclotomic p
  -- σ - 1 = aeval σ (X - 1)
  have hσ_sub_one_aeval :
      Polynomial.aeval σ ((Polynomial.X : ℚ[X]) - 1) = σ - 1 := by
    rw [map_sub, Polynomial.aeval_X, map_one]
  have hker_eq : LinearMap.ker (σ - 1) =
      LinearMap.ker (Polynomial.aeval σ ((Polynomial.X : ℚ[X]) - 1)) := by
    rw [hσ_sub_one_aeval]
  -- (X - 1) * Φ_p = X^p - 1, and aeval σ (X^p - 1) = σ^p - 1 = 0
  have hmul_eq : ((Polynomial.X : ℚ[X]) - 1) * Polynomial.cyclotomic p ℚ =
      (Polynomial.X : ℚ[X]) ^ p - 1 := by
    rw [mul_comm]
    exact Polynomial.cyclotomic_prime_mul_X_sub_one ℚ p
  have haeval_mul : Polynomial.aeval σ
      (((Polynomial.X : ℚ[X]) - 1) * Polynomial.cyclotomic p ℚ) = 0 := by
    rw [hmul_eq, map_sub, Polynomial.aeval_X_pow, map_one, hσ, sub_self]
  refine ⟨?_, ?_⟩
  · -- Disjoint
    rw [hker_eq]
    exact Polynomial.disjoint_ker_aeval_of_isCoprime σ hcop
  · -- Codisjoint: ker (σ - 1) ⊔ ker Φ_p(σ) = ⊤
    rw [codisjoint_iff, hker_eq,
        Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime σ hcop, haeval_mul]
    exact LinearMap.ker_zero

/-- **Key abstract identity**: σ^p = 1, 1 ≤ j < p のとき Φ_p(σ^j) = Φ_p(σ).

Φ_p(X) = 1 + X + ... + X^{p-1}. σ^p = 1 から
∑_i σ^{ij} = ∑_i σ^{(ij) mod p} = ∑_k σ^k (mul-j mod p が p-prime, j coprime で bijection). -/
private theorem aeval_cyclotomic_pow_eq_self_of_pow_eq_one
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    {S : Type*} [Semiring S] [Algebra ℚ S]
    (σ : S) (hσ : σ ^ p = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) :
    Polynomial.aeval (σ ^ j) (Polynomial.cyclotomic p ℚ) =
    Polynomial.aeval σ (Polynomial.cyclotomic p ℚ) := by
  -- gcd(j, p) = 1
  have hcop_pj : Nat.gcd p j = 1 := by
    apply (Nat.Prime.coprime_iff_not_dvd hp.out).mpr
    intro hdvd
    exact absurd (Nat.le_of_dvd hj1 hdvd) (not_le.mpr hjp)
  -- σ^(a) = σ^(a % p) using σ^p = 1
  have hpow_mod : ∀ a : ℕ, σ ^ a = σ ^ (a % p) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a p, pow_add, pow_mul, hσ, one_pow, mul_one]
  -- Expand cyclotomic
  rw [Polynomial.cyclotomic_prime ℚ p, map_sum, map_sum]
  simp only [Polynomial.aeval_X_pow]
  -- LHS: ∑ i in range p, (σ^j)^i
  -- RHS: ∑ i in range p, σ^i
  -- Rewrite (σ^j)^i = σ^(j*i) = σ^((j*i) % p)
  have hLHS : ∀ i ∈ Finset.range p, (σ ^ j) ^ i = σ ^ ((j * i) % p) := fun i _ => by
    rw [← pow_mul]; exact hpow_mod _
  rw [Finset.sum_congr rfl hLHS]
  -- Now: ∑ i, σ^((j*i) % p) = ∑ i, σ^i via bijection (j * ·) % p
  -- Define f i = (j * i) % p
  let f : ℕ → ℕ := fun i => (j * i) % p
  show ∑ i ∈ Finset.range p, σ ^ f i = ∑ i ∈ Finset.range p, σ ^ i
  -- f is injective on Finset.range p
  have hf_inj : Set.InjOn f (Finset.range p) := by
    intros i₁ hi₁ i₂ hi₂ hfeq
    simp only [Finset.coe_range, Set.mem_Iio] at hi₁ hi₂
    -- f i₁ = f i₂ → j * i₁ ≡ j * i₂ [MOD p]
    have hmodeq : j * i₁ ≡ j * i₂ [MOD p] := hfeq
    have : i₁ ≡ i₂ [MOD p] :=
      Nat.ModEq.cancel_left_of_coprime hcop_pj hmodeq
    exact Nat.ModEq.eq_of_lt_of_lt this hi₁ hi₂
  -- f maps Finset.range p into itself
  have hf_maps : ∀ i ∈ Finset.range p, f i ∈ Finset.range p := fun i _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ hp.out.pos)
  -- Image of f over Finset.range p equals Finset.range p
  have h_image : (Finset.range p).image f = Finset.range p := by
    apply Finset.eq_of_subset_of_card_le
    · intros k hk
      rw [Finset.mem_image] at hk
      obtain ⟨i, hi, rfl⟩ := hk
      exact hf_maps i hi
    · rw [Finset.card_image_of_injOn hf_inj]
  -- Now reindex via Finset.sum_image
  conv_rhs => rw [← h_image]
  rw [Finset.sum_image (fun i hi j hj => hf_inj hi hj)]

/-- σ^n は (σ - 1) と可換. -/
private theorem commute_sub_one_pow (σ : W →ₗ[ℚ] W) (n : ℕ) :
    Commute (σ - 1) (σ ^ n) := by
  have h1 : Commute σ (σ ^ n) := (Commute.refl σ).pow_right n
  exact h1.sub_left (Commute.one_left _)

/-- σ^n は ker(σ - 1) を保つ. -/
private theorem mapsTo_pow_ker_sub_one (σ : W →ₗ[ℚ] W) (n : ℕ) :
    Set.MapsTo (σ ^ n) (LinearMap.ker (σ - 1)) (LinearMap.ker (σ - 1)) := by
  intro v hv
  have hv' : (σ - 1) v = 0 := hv
  show (σ - 1) ((σ ^ n) v) = 0
  -- (σ - 1) (σ^n v) = σ^n ((σ - 1) v) = σ^n 0 = 0
  have hcomm := (commute_sub_one_pow σ n).eq
  have heq := congrArg (· v) hcomm
  simp only [Module.End.mul_apply] at heq
  rw [heq, hv', map_zero]

/-- σ^n は (aeval σ f) と可換 (f : ℚ[X]). -/
private theorem commute_aeval_pow (σ : W →ₗ[ℚ] W) (f : ℚ[X]) (n : ℕ) :
    Commute (Polynomial.aeval σ f) (σ ^ n) := by
  have h_sigma_n : σ ^ n = Polynomial.aeval σ ((Polynomial.X : ℚ[X]) ^ n) := by
    rw [Polynomial.aeval_X_pow]
  rw [h_sigma_n, Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

/-- σ^n は ker (aeval σ f) を保つ (f 任意). -/
private theorem mapsTo_pow_ker_aeval
    (σ : W →ₗ[ℚ] W) (f : ℚ[X]) (n : ℕ) :
    Set.MapsTo (σ ^ n) (LinearMap.ker (Polynomial.aeval σ f))
      (LinearMap.ker (Polynomial.aeval σ f)) := by
  intro v hv
  have hv' : Polynomial.aeval σ f v = 0 := hv
  show Polynomial.aeval σ f ((σ ^ n) v) = 0
  have hcomm := (commute_aeval_pow σ f n).eq
  have heq := congrArg (· v) hcomm
  simp only [Module.End.mul_apply] at heq
  rw [heq, hv', map_zero]

/-- **抽象 trace constancy theorem (Stage 3 ターゲット)**.

W が finite-dim ℚ-vec, σ : W →ₗ W が σ^p = 1 を満たすとき (p 素数),
k = 1..p-1 で `tr σ^k` は一定.

証明: W = ker(σ - 1) ⊕ ker Φ_p(σ) で分解.
* ker(σ - 1) 上 σ^k = id, trace = dim ker(σ - 1).
* ker Φ_p(σ) 上 trace_package_of_cyclotomic_prime_aeval_eq_zero で trace = -γ_k.
* dim ker Φ_p(σ) = (p-1) γ_k から γ_k は k に依らず一定. -/
theorem trace_pow_eq_of_pow_eq_one
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (σ : W →ₗ[ℚ] W) (hσ : σ ^ p = 1)
    {j k : ℕ} (hj1 : 1 ≤ j) (hjp : j < p) (hk1 : 1 ≤ k) (hkp : k < p) :
    LinearMap.trace ℚ W (σ ^ j) = LinearMap.trace ℚ W (σ ^ k) := by
  classical
  set W₁ : Submodule ℚ W := LinearMap.ker (σ - 1) with hW₁_def
  set W₂ : Submodule ℚ W :=
    LinearMap.ker (Polynomial.aeval σ (Polynomial.cyclotomic p ℚ)) with hW₂_def
  have hcompl : IsCompl W₁ W₂ := isCompl_ker_sub_one_and_ker_aeval_cyclotomic p σ hσ
  -- Bool 添字
  let N : Bool → Submodule ℚ W := fun b => bif b then W₂ else W₁
  have hN_univ : (Set.univ : Set Bool) = {false, true} := by
    ext b; cases b <;> simp
  have hIsInternal : DirectSum.IsInternal N := by
    rw [DirectSum.isInternal_submodule_iff_isCompl N
        (i := false) (j := true) (by decide) hN_univ]
    exact hcompl
  -- σ^n が両 component を保つ
  have hMaps_W₁ : ∀ n : ℕ, Set.MapsTo (σ ^ n) W₁ W₁ := fun n => mapsTo_pow_ker_sub_one σ n
  have hMaps_W₂ : ∀ n : ℕ, Set.MapsTo (σ ^ n) W₂ W₂ := fun n =>
    mapsTo_pow_ker_aeval σ (Polynomial.cyclotomic p ℚ) n
  have hMaps : ∀ n : ℕ, ∀ b : Bool, Set.MapsTo (σ ^ n) (N b) (N b) := by
    intros n b
    cases b
    · exact hMaps_W₁ n
    · exact hMaps_W₂ n
  -- W₁ 上 σ^n v = v (値レベル)
  have h_W₁_pow_val : ∀ n : ℕ, ∀ v : W₁, (σ ^ n) v.val = v.val := by
    intros n v
    have hv : (σ - 1) v.val = 0 := v.property
    have hv' : σ v.val = v.val := by
      rw [LinearMap.sub_apply, sub_eq_zero] at hv
      simpa using hv
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hv', ih]
  -- W₁ 上 (σ^n).restrict = id
  have h_W₁_restrict_id : ∀ n : ℕ,
      (σ ^ n).restrict (hMaps_W₁ n) = (LinearMap.id : W₁ →ₗ[ℚ] W₁) := by
    intro n
    ext v
    show ((σ ^ n).restrict (hMaps_W₁ n) v : W) = v.val
    rw [LinearMap.restrict_apply]
    exact h_W₁_pow_val n v
  -- trace 分解
  have htrace_decomp : ∀ n : ℕ,
      LinearMap.trace ℚ W (σ ^ n) =
        LinearMap.trace ℚ W₁ ((σ ^ n).restrict (hMaps_W₁ n)) +
        LinearMap.trace ℚ W₂ ((σ ^ n).restrict (hMaps_W₂ n)) := by
    intro n
    rw [LinearMap.trace_eq_sum_trace_restrict hIsInternal (hMaps n)]
    rw [Fintype.sum_bool]
    -- After: trace (N true) + trace (N false) = trace W₁ + trace W₂
    -- N true = W₂, N false = W₁ (definitional via bif)
    exact add_comm _ _
  -- W₁ 上 トレースは等しい
  have htrace_W₁_eq : LinearMap.trace ℚ W₁ ((σ ^ j).restrict (hMaps_W₁ j)) =
      LinearMap.trace ℚ W₁ ((σ ^ k).restrict (hMaps_W₁ k)) := by
    rw [h_W₁_restrict_id j, h_W₁_restrict_id k]
  -- W₂ 上: aeval (σ^n.restrict) Φ_p = 0
  have h_aeval_zero_on_W₂ : ∀ {n : ℕ} (hn1 : 1 ≤ n) (hnp : n < p),
      Polynomial.aeval ((σ ^ n).restrict (hMaps_W₂ n)) (Polynomial.cyclotomic p ℚ) = 0 := by
    intros n hn1 hnp
    ext v
    show ((Polynomial.aeval ((σ ^ n).restrict (hMaps_W₂ n))
          (Polynomial.cyclotomic p ℚ)) v : W) = 0
    -- Expand Φ_p = ∑ X^i, then push restrict inside via Module.End.pow_restrict
    rw [Polynomial.cyclotomic_prime, map_sum]
    simp only [Polynomial.aeval_X_pow]
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    have hpow_apply : ∀ i ∈ Finset.range p,
        (↑((((σ ^ n).restrict (hMaps_W₂ n)) ^ i) v) : W) = ((σ ^ n) ^ i) v.val := by
      intros i _
      rw [Module.End.pow_restrict, LinearMap.restrict_coe_apply]
    rw [Finset.sum_congr rfl hpow_apply]
    -- ∑ i ∈ range p, (σ^n)^i v.val = 0
    -- これは (aeval (σ^n) Φ_p) v.val に等しい. key lemma で aeval σ Φ_p v.val に変換, v.property で 0.
    have h_unfolded : ∑ i ∈ Finset.range p, ((σ ^ n) ^ i) v.val =
        Polynomial.aeval (σ ^ n) (Polynomial.cyclotomic p ℚ) v.val := by
      rw [Polynomial.cyclotomic_prime, map_sum]
      simp [Polynomial.aeval_X_pow]
    rw [h_unfolded]
    rw [aeval_cyclotomic_pow_eq_self_of_pow_eq_one σ hσ hn1 hnp]
    exact v.property
  -- W₂ 上 trace_package
  obtain ⟨γ_j, hdim_j, htrace_j⟩ :=
    trace_package_of_cyclotomic_prime_aeval_eq_zero p _ (h_aeval_zero_on_W₂ hj1 hjp)
  obtain ⟨γ_k, hdim_k, htrace_k⟩ :=
    trace_package_of_cyclotomic_prime_aeval_eq_zero p _ (h_aeval_zero_on_W₂ hk1 hkp)
  have hp_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  have hγ_eq : γ_j = γ_k := by
    have := hdim_j.symm.trans hdim_k
    exact Nat.eq_of_mul_eq_mul_left hp_pos this
  have htrace_W₂_eq : LinearMap.trace ℚ W₂ ((σ ^ j).restrict (hMaps_W₂ j)) =
      LinearMap.trace ℚ W₂ ((σ ^ k).restrict (hMaps_W₂ k)) := by
    rw [htrace_j, htrace_k, hγ_eq]
  rw [htrace_decomp j, htrace_decomp k, htrace_W₁_eq, htrace_W₂_eq]

end LinearMap

end Moore57
