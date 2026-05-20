import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.FixedCount
import Moore57.Moore57Graph.Aut.OrderElevenIsC5

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 3

> Let `X` be a subgroup of odd prime order in `G = Aut(Γ)`. Then one of the
> following holds:
>
> (1) Fix(X) is empty and `|X|` divides `5 · 13`;
>
> (2) `|Fix(X)| = 1` and `|X|` divides `3 · 19`;
>
> (3) Fix(X) is a star, `|Fix(X)| ≥ 2`, and `|X|` divides `7`;
>
> (4) Fix(X) is a pentagon and `|X|` divides `5 · 11`;
>
> (5) Fix(X) is Petersen's graph and `|X|` divides `3`;
>
> (6) Fix(X) is Hoffman–Singleton's graph and `|X|` divides `5`.

Status:
* The full 6-way classification is a skeleton (= Mačaj–Širáň Lem 4, depends
  on the Aschbacher fix-classification).
* Two specific rows are wrapped from existing Moore57 infrastructure:
  - Order 19 (case 2): `lem3_order19_case2`.
  - Order 11 (case 4): `lem3_order11_case4`.
-/

open Moore57

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 3 (general 6-way classification).** [deferred-heavy] -/
theorem lem3_odd_prime_fix (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 3, case (2): order 19, `|Fix| = 1`.**
Any order-19 automorphism of Moore57 has exactly one fixed vertex. -/
theorem lem3_order19_case2 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 19 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 1 :=
  order19_aut_fixedVertexCount_eq_one hΓ σ hAut hpow hne

/-- **Lemma 3, case (4): order 11, `|Fix|` is a pentagon (5 vertices).**
Any order-11 automorphism of Moore57 has fixed-vertex set of size 5
(induced subgraph is the pentagon `C₅`). -/
theorem lem3_order11_case4 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hpow : σ ^ 11 = 1) (hne : σ ≠ 1) :
    fixedVertexCount σ = 5 :=
  aut_order_eleven_fixedVertexCount_eq_five hΓ σ hAut hpow hne

/-- **Lemma 3, case (1) arithmetic core: odd prime divisors of `3250`.** [done]

For `p` an odd prime dividing `3250`, conclude `p ∈ {5, 13}`.  Proof:
factor `3250 = 2 · 5^3 · 13` and apply `Nat.Prime.dvd_mul` /
`Nat.Prime.dvd_of_dvd_pow` plus `Nat.Prime.eq_one_or_self_of_dvd` for
the prime factors. -/
theorem lem3_case1_arithmetic_core
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : 2 < p)
    (hdvd : p ∣ 3250) :
    p = 5 ∨ p = 13 := by
  have h1 : p ∣ 2 ∨ p ∣ 5 * 5 * 5 * 13 := by
    have h_eq : (3250 : ℕ) = 2 * (5 * 5 * 5 * 13) := by norm_num
    rw [h_eq] at hdvd
    exact (hp_prime.dvd_mul).mp hdvd
  rcases h1 with h2 | h_rest
  · have := Nat.le_of_dvd (by norm_num) h2
    omega
  have h2 : p ∣ 5 * 5 * 5 ∨ p ∣ 13 := by
    have h_eq : (5 * 5 * 5 * 13 : ℕ) = (5 * 5 * 5) * 13 := by norm_num
    rw [h_eq] at h_rest
    exact (hp_prime.dvd_mul).mp h_rest
  rcases h2 with h_5pow | h13
  · have hp5 : p ∣ 5 := by
      have h_pow : (5 * 5 * 5 : ℕ) = 5 ^ 3 := by norm_num
      rw [h_pow] at h_5pow
      exact hp_prime.dvd_of_dvd_pow h_5pow
    have : p = 1 ∨ p = 5 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 5)) p hp5
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · left; exact h
  · have : p = 1 ∨ p = 13 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 13)) p h13
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · right; exact h

/-- **Lemma 3, case (1) conditional: empty fix odd-prime is in `{5, 13}`.** [done]

For a Moore57 graph automorphism `σ` of odd prime order `p` with
`Fix(σ) = ∅`, conclude `p ∈ {5, 13}`.

Proof: combine the generic mod-`p` constraint
`fixedVertexCount σ ≡ |V| [MOD p]` (= `3250` for Moore57) with
`fixedVertexCount σ = 0` to get `p ∣ 3250`, then apply the arithmetic
core `lem3_case1_arithmetic_core`. -/
theorem lem3_case1_empty_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (h_fix_empty : fixedVertexCount σ = 0) :
    p = 5 ∨ p = 13 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_card_of_pow_prime σ p hpow
  rw [hΓ.card, h_fix_empty] at hmod
  -- hmod : 0 ≡ 3250 [MOD p]; flip to get 3250 ≡ 0 [MOD p], hence p ∣ 3250.
  have hdvd : p ∣ 3250 := Nat.modEq_zero_iff_dvd.mp hmod.symm
  exact lem3_case1_arithmetic_core p Fact.out hp_odd hdvd

/-- **Lemma 3, case (6) arithmetic core: odd prime divisors of `3200`.** [done]

For `p` an odd prime dividing `3200 = 2^7 · 5^2`, conclude `p = 5`.
Proof: factor `3200 = 2^7 · 5^2`, apply `Nat.Prime.dvd_mul` /
`Nat.Prime.dvd_of_dvd_pow`; the 2-power branch gives `p ≤ 2` (excluded
by `p > 2`), and the 5-power branch gives `p = 5`. -/
theorem lem3_case6_arithmetic_core
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : 2 < p)
    (hdvd : p ∣ 3200) :
    p = 5 := by
  have h_eq : (3200 : ℕ) = 2^7 * 5^2 := by norm_num
  rw [h_eq] at hdvd
  have h1 : p ∣ 2^7 ∨ p ∣ 5^2 := (hp_prime.dvd_mul).mp hdvd
  rcases h1 with h2pow | h5pow
  · have hp_dvd_2 : p ∣ 2 := hp_prime.dvd_of_dvd_pow h2pow
    have := Nat.le_of_dvd (by norm_num) hp_dvd_2
    omega
  · have hp_dvd_5 : p ∣ 5 := hp_prime.dvd_of_dvd_pow h5pow
    have : p = 1 ∨ p = 5 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 5)) p hp_dvd_5
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · exact h

/-- **Lemma 3, case (6) conditional: Hoffman-Singleton fix forces `p = 5`.** [done]

For a Moore57 graph automorphism `σ` of odd prime order `p` with
`|Fix(σ)| = 50` (the Hoffman-Singleton case), conclude `p = 5`.

Proof: the generic mod-`p` constraint gives `50 ≡ 3250 [MOD p]`, so
`p ∣ 3200 = 3250 − 50`.  Apply `lem3_case6_arithmetic_core`. -/
theorem lem3_case6_hs_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (h_fix_50 : fixedVertexCount σ = 50) :
    p = 5 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_card_of_pow_prime σ p hpow
  rw [hΓ.card, h_fix_50] at hmod
  -- hmod : 50 ≡ 3250 [MOD p]; convert to p ∣ 3200 via modEq_iff_dvd'.
  have hdvd : p ∣ 3200 := by
    have h_dvd_diff : p ∣ 3250 - 50 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact lem3_case6_arithmetic_core p Fact.out hp_odd hdvd

/-- **Lemma 3, case (2) arithmetic core: odd prime divisors of `3249`.** [done]

For `p` an odd prime dividing `3249 = 3^2 · 19^2`, conclude `p ∈ {3, 19}`.
Proof: factor `3249 = 3^2 · 19^2`, apply `Nat.Prime.dvd_mul` /
`Nat.Prime.dvd_of_dvd_pow`; each branch gives a prime-divides-prime
collapse via `Nat.Prime.eq_one_or_self_of_dvd`. -/
theorem lem3_case2_arithmetic_core
    (p : ℕ) (hp_prime : Nat.Prime p) (_hp_odd : 2 < p)
    (hdvd : p ∣ 3249) :
    p = 3 ∨ p = 19 := by
  have h_eq : (3249 : ℕ) = 3^2 * 19^2 := by norm_num
  rw [h_eq] at hdvd
  have h1 : p ∣ 3^2 ∨ p ∣ 19^2 := (hp_prime.dvd_mul).mp hdvd
  rcases h1 with h3pow | h19pow
  · have hp_dvd_3 : p ∣ 3 := hp_prime.dvd_of_dvd_pow h3pow
    have : p = 1 ∨ p = 3 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3)) p hp_dvd_3
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · left; exact h
  · have hp_dvd_19 : p ∣ 19 := hp_prime.dvd_of_dvd_pow h19pow
    have : p = 1 ∨ p = 19 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 19)) p hp_dvd_19
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · right; exact h

/-- **Lemma 3, case (2) conditional: singleton fix forces `p ∈ {3, 19}`.** [done]

For a Moore57 graph automorphism `σ` of odd prime order `p` with
`|Fix(σ)| = 1` (singleton), conclude `p ∈ {3, 19}` (matching the
paper's `|X| ∣ 3·19 = 57`).

Proof: the generic mod-`p` constraint gives `1 ≡ 3250 [MOD p]`, so
`p ∣ 3249 = 3250 − 1`.  Apply `lem3_case2_arithmetic_core`. -/
theorem lem3_case2_singleton_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (h_fix_one : fixedVertexCount σ = 1) :
    p = 3 ∨ p = 19 := by
  have hmod := Moore57.aut_fixedVertexCount_modEq_card_of_pow_prime σ p hpow
  rw [hΓ.card, h_fix_one] at hmod
  have hdvd : p ∣ 3249 := by
    have h_dvd_diff : p ∣ 3250 - 1 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact lem3_case2_arithmetic_core p Fact.out hp_odd hdvd

end Moore57.Papers.MakhnevPaduchikh2001
