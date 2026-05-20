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

/-- **Lemma 3 (general 6-way classification).** [deferred-heavy]

Backward-compat True-stub.  Proper-signature dispatch is
`lem3_odd_prime_fix_paper` (below, global Fix dispatch) and
`lem3_unified_p_in_moore57_primes` (local N(a) dispatch). -/
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

/-- **Lemma 3, case (5) arithmetic core: odd prime divisors of `54`.** [done]

For `p` an odd prime dividing `54 = 2 · 3^3`, conclude `p = 3`.
Proof: factor `54 = 2 · 3^3`; the 2-branch is excluded by `p > 2`,
and the 3-power branch gives `p = 3`. -/
theorem lem3_case5_arithmetic_core
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : 2 < p)
    (hdvd : p ∣ 54) :
    p = 3 := by
  have h_eq : (54 : ℕ) = 2 * 3^3 := by norm_num
  rw [h_eq] at hdvd
  have h1 : p ∣ 2 ∨ p ∣ 3^3 := (hp_prime.dvd_mul).mp hdvd
  rcases h1 with h2 | h3pow
  · have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have hp_dvd_3 : p ∣ 3 := hp_prime.dvd_of_dvd_pow h3pow
    have : p = 1 ∨ p = 3 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3)) p hp_dvd_3
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · exact h

/-- **Lemma 3, case (5) conditional: Petersen fix forces `p = 3`.** [done]

For a Moore57 graph automorphism `σ` of odd prime order `p` fixing a
vertex `a` whose σ-fixed-neighbour count is 3 (the Petersen-degree
restriction: in Fix(σ) ≅ Petersen, every vertex has 3 neighbours in
Fix), conclude `p = 3`.

This is the paper-tight restriction (`|X| ∣ 3`) for case (5).

Proof: the local mod-`p` constraint
`(autFixedNeighborFinset).card ≡ deg = 57 [MOD p]` with the
Petersen-degree value 3 gives `p ∣ 54 = 57 − 3`.  Apply the
arithmetic core. -/
theorem lem3_case5_petersen_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_N_fix_petersen : (Moore57.autFixedNeighborFinset Γ σ a).card = 3) :
    p = 3 := by
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime
    σ hAut p hpow ha
  rw [hΓ.regular.degree_eq a, h_N_fix_petersen] at hmod
  -- hmod : 3 ≡ 57 [MOD p]
  have hdvd : p ∣ 54 := by
    have h_dvd_diff : p ∣ 57 - 3 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact lem3_case5_arithmetic_core p Fact.out hp_odd hdvd

/-- **Lemma 3, case (3) arithmetic core: odd prime divisors of `56`.** [done]

For `p` an odd prime dividing `56 = 2^3 · 7`, conclude `p = 7`. -/
theorem lem3_case3_arithmetic_core
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_odd : 2 < p)
    (hdvd : p ∣ 56) :
    p = 7 := by
  have h_eq : (56 : ℕ) = 2^3 * 7 := by norm_num
  rw [h_eq] at hdvd
  have h1 : p ∣ 2^3 ∨ p ∣ 7 := (hp_prime.dvd_mul).mp hdvd
  rcases h1 with h2pow | h7
  · have hp_dvd_2 : p ∣ 2 := hp_prime.dvd_of_dvd_pow h2pow
    have := Nat.le_of_dvd (by norm_num) hp_dvd_2
    omega
  · have : p = 1 ∨ p = 7 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 7)) p h7
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · exact h

/-- **Lemma 3, case (3) conditional: star-leaf fix forces `p = 7`.** [done]

For a Moore57 graph automorphism `σ` of odd prime order `p` fixing a
star-leaf vertex `a` whose σ-fixed-neighbour count is 1 (only the
star centre is fixed and adjacent to `a`), conclude `p = 7`.

This is the paper-tight restriction (`|X| ∣ 7`) for case (3).

Proof: the local mod-`p` constraint at `a` with `|N(a) ∩ Fix| = 1`
gives `p ∣ 56 = 57 − 1`.  Apply the arithmetic core. -/
theorem lem3_case3_star_leaf_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_N_fix_leaf : (Moore57.autFixedNeighborFinset Γ σ a).card = 1) :
    p = 7 := by
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime
    σ hAut p hpow ha
  rw [hΓ.regular.degree_eq a, h_N_fix_leaf] at hmod
  -- hmod : 1 ≡ 57 [MOD p]
  have hdvd : p ∣ 56 := by
    have h_dvd_diff : p ∣ 57 - 1 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact lem3_case3_arithmetic_core p Fact.out hp_odd hdvd

/-- **Lemma 3, case (4) arithmetic core: odd prime divisors of `55`.** [done]

For `p` an odd prime dividing `55 = 5 · 11`, conclude `p ∈ {5, 11}`. -/
theorem lem3_case4_arithmetic_core
    (p : ℕ) (hp_prime : Nat.Prime p) (_hp_odd : 2 < p)
    (hdvd : p ∣ 55) :
    p = 5 ∨ p = 11 := by
  have h_eq : (55 : ℕ) = 5 * 11 := by norm_num
  rw [h_eq] at hdvd
  have h1 : p ∣ 5 ∨ p ∣ 11 := (hp_prime.dvd_mul).mp hdvd
  rcases h1 with h5 | h11
  · have : p = 1 ∨ p = 5 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 5)) p h5
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · left; exact h
  · have : p = 1 ∨ p = 11 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 11)) p h11
    rcases this with h | h
    · exact absurd h hp_prime.one_lt.ne'
    · right; exact h

/-- **Lemma 3, case (4) conditional: pentagon-vertex fix forces `p ∈ {5, 11}`.** [done]

For a Moore57 graph automorphism `σ` of odd prime order `p` fixing a
pentagon-vertex `a` whose σ-fixed-neighbour count is 2 (the pentagon
`C_5` has degree 2), conclude `p ∈ {5, 11}`.

This is the paper-tight restriction (`|X| ∣ 5·11 = 55`) for case (4).

Proof: the local mod-`p` constraint at `a` with `|N(a) ∩ Fix| = 2`
gives `p ∣ 55 = 57 − 2`.  Apply the arithmetic core. -/
theorem lem3_case4_pentagon_fix
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_N_fix_pentagon : (Moore57.autFixedNeighborFinset Γ σ a).card = 2) :
    p = 5 ∨ p = 11 := by
  have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime
    σ hAut p hpow ha
  rw [hΓ.regular.degree_eq a, h_N_fix_pentagon] at hmod
  -- hmod : 2 ≡ 57 [MOD p]
  have hdvd : p ∣ 55 := by
    have h_dvd_diff : p ∣ 57 - 2 :=
      (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
    simpa using h_dvd_diff
  exact lem3_case4_arithmetic_core p Fact.out hp_odd hdvd

/-- **Lemma 3 unified: any of the 5 shape-degree values forces `p` into
the Moore57 odd-prime list `{3, 5, 7, 11, 13, 19}`.** [done]

For a Moore57 graph automorphism `σ` of odd prime order `p` fixing
some vertex `a` whose σ-fixed-neighbour count `c` is one of the
paper-cited Fix-shape degrees `c ∈ {0, 1, 2, 3, 7}` (matching
singleton / star-leaf / pentagon / Petersen / HS), conclude
`p ∈ {3, 5, 7, 11, 13, 19}`.

This combines all five N(a)-based case bridges into a single unified
statement.  The case `c = 0` covers both case (1) (empty fix) and
case (2) (singleton fix at the unique fixed point `a`); the latter
gives the more restrictive `p ∈ {3, 19}`. -/
theorem lem3_unified_p_in_moore57_primes
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1)
    (hAut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {a : V} (ha : σ a = a)
    (h_count_in :
      (Moore57.autFixedNeighborFinset Γ σ a).card = 0 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 1 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 2 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 3 ∨
      (Moore57.autFixedNeighborFinset Γ σ a).card = 7) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 := by
  -- Case (2) singleton uses the GLOBAL Fix count, not N(a); but here
  -- N(a) ∩ Fix = 0 means a is the unique fixed vertex among N(a) ∪ {a},
  -- consistent with the singleton case at `a`.  The arithmetic gives
  -- p | 57 = 3 · 19, p ∈ {3, 19}.
  rcases h_count_in with hc | hc | hc | hc | hc
  · -- |N(a) ∩ Fix| = 0: p | 57, p ∈ {3, 19}
    have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime
      σ hAut p hpow ha
    rw [hΓ.regular.degree_eq a, hc] at hmod
    have hdvd : p ∣ 57 := Nat.modEq_zero_iff_dvd.mp hmod.symm
    have h_eq : (57 : ℕ) = 3 * 19 := by norm_num
    rw [h_eq] at hdvd
    have h1 : p ∣ 3 ∨ p ∣ 19 := ((Fact.out : Nat.Prime p).dvd_mul).mp hdvd
    rcases h1 with h3 | h19
    · have : p = 1 ∨ p = 3 :=
        (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3)) p h3
      rcases this with h | h
      · exact absurd h (Fact.out : Nat.Prime p).one_lt.ne'
      · left; exact h
    · have : p = 1 ∨ p = 19 :=
        (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 19)) p h19
      rcases this with h | h
      · exact absurd h (Fact.out : Nat.Prime p).one_lt.ne'
      · right; right; right; right; right; exact h
  · -- |N(a) ∩ Fix| = 1: p = 7
    have := lem3_case3_star_leaf_fix hΓ σ p hp_odd hpow hAut ha hc
    right; right; left; exact this
  · -- |N(a) ∩ Fix| = 2: p ∈ {5, 11}
    rcases lem3_case4_pentagon_fix hΓ σ p hp_odd hpow hAut ha hc with h | h
    · right; left; exact h
    · right; right; right; left; exact h
  · -- |N(a) ∩ Fix| = 3: p = 3
    have := lem3_case5_petersen_fix hΓ σ p hp_odd hpow hAut ha hc
    left; exact this
  · -- |N(a) ∩ Fix| = 7: p = 5 (via 57 - 7 = 50 = 2 · 5²)
    have hmod := Moore57.aut_card_fixedNeighborFinset_modEq_degree_of_pow_prime
      σ hAut p hpow ha
    rw [hΓ.regular.degree_eq a, hc] at hmod
    have hdvd : p ∣ 50 := by
      have h_dvd_diff : p ∣ 57 - 7 :=
        (Nat.modEq_iff_dvd' (by norm_num)).mp hmod
      simpa using h_dvd_diff
    -- 50 = 2 · 5²; odd prime divisor: 5.
    have h_eq : (50 : ℕ) = 2 * 5^2 := by norm_num
    rw [h_eq] at hdvd
    have h1 : p ∣ 2 ∨ p ∣ 5^2 :=
      ((Fact.out : Nat.Prime p).dvd_mul).mp hdvd
    rcases h1 with h2 | h5pow
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · have hp_dvd_5 : p ∣ 5 :=
        (Fact.out : Nat.Prime p).dvd_of_dvd_pow h5pow
      have : p = 1 ∨ p = 5 :=
        (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 5)) p hp_dvd_5
      rcases this with h | h
      · exact absurd h (Fact.out : Nat.Prime p).one_lt.ne'
      · right; left; exact h

/-- **Lemma 3 (paper-faithful conditional dispatch).** [done]

Proper-signature paper-faithful packaging of three cases of the
classification: for σ an odd-prime-order graph automorphism of Moore57,
the global fixed-vertex count `fixedVertexCount σ ∈ {0, 1, 50}` determines
`p` to within a short list, via cases (1) (empty), (2) (singleton),
(6) (Hoffman-Singleton).

Cases (3) star, (4) pentagon, (5) Petersen are dispatched separately
via local `N(a)` constraints (see `lem3_case3_*`, `lem3_case4_*`,
`lem3_case5_*`) and the unified `lem3_unified_p_in_moore57_primes`. -/
theorem lem3_odd_prime_fix_paper
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_odd : 2 < p) (hpow : σ ^ p = 1) :
    (fixedVertexCount σ = 0 → p = 5 ∨ p = 13) ∧
    (fixedVertexCount σ = 1 → p = 3 ∨ p = 19) ∧
    (fixedVertexCount σ = 50 → p = 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact lem3_case1_empty_fix hΓ σ p hp_odd hpow h
  · intro h; exact lem3_case2_singleton_fix hΓ σ p hp_odd hpow h
  · intro h; exact lem3_case6_hs_fix hΓ σ p hp_odd hpow h

end Moore57.Papers.MakhnevPaduchikh2001
