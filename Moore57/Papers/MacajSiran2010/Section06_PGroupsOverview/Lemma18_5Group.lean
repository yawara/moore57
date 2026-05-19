import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix
import Moore57.Moore57Graph.Aut.NeighborMod

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 18

> Let `X` be a group of automorphisms of Γ such that `|X|` is a 5-group.
> Then one of the following holds:
>
> (1) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `25`;
>
> (2) `Fix(X)` is a pentagon and `|X|` divides `125`;
>
> (3) `Fix(X)` is empty and `|X|` divides `5⁶`.

This is the only lemma in §6 whose full proof the authors include
(orbit counting around `Fix(a)` for `a ∈ Fix(X)`).

Status:
* `lem18_5group_fix` — full classification (deferred-heavy).
* `lem18_case1_arithmetic_5group_dvd_50_implies_25`,
  `lem18_case2_arithmetic_5group_dvd_55_implies_125`: **proven**
  arithmetic cores translating "5-group + small divisor" to the
  stated bound (`|X| ∣ 25` resp. `∣ 125`).
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 18 case (1) arithmetic core: 5-group with `|X| ∣ 50` gives
`|X| ∣ 25`.** [done]

For a 5-group `X` (i.e., `|X| = 5^k` for some `k`), the constraint
`|X| ∣ 50` forces `|X| ≤ 50` hence `k ≤ 2`, hence `|X| = 5^k ∈ {1, 5, 25}`,
all of which divide `25`.

This is the §6 Lem 18 (1) arithmetic step: semi-regular action of `X`
on `N(a) \ Fix(X)` (of size `50` when `Fix(X) = HS`) gives `|X| ∣ 50`,
and the 5-group constraint sharpens to `|X| ∣ 25`. -/
theorem lem18_case1_arithmetic_5group_dvd_50_implies_25
    (k : ℕ) (h_dvd : 5 ^ k ∣ 50) : 5 ^ k ∣ 25 := by
  have h_le : 5 ^ k ≤ 50 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := Nat.lt_of_not_le h
    have h_ge : 5 ^ 3 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    omega
  interval_cases k <;> decide

/-- **Lemma 18 case (2) arithmetic core: 5-group with `|X| ∣ 55` gives
`|X| ∣ 5`.** [done]

For a 5-group `X` (`|X| = 5^k`), `|X| ∣ 55 = 5·11` forces `k ≤ 1`
since `5^2 = 25` does not divide `55`.  Hence `|X| ∈ {1, 5}` and
`|X| ∣ 5`.  Combined with the orbit-stabilizer argument
`|X| = 5·|Y|` and `|Y| ≤ 25` from case (1) gives the paper's
`|X| ∣ 125`. -/
theorem lem18_case2_arithmetic_5group_dvd_55_implies_5
    (k : ℕ) (h_dvd : 5 ^ k ∣ 55) : 5 ^ k ∣ 5 := by
  have h_le : 5 ^ k ≤ 55 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := Nat.lt_of_not_le h
    have h_ge : 5 ^ 3 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    omega
  interval_cases k
  · decide          -- 5^0 = 1 ∣ 5
  · decide          -- 5^1 = 5 ∣ 5
  · -- k = 2: 5^2 = 25, but 25 does not divide 55.  Contradiction.
    exfalso
    revert h_dvd
    decide

/-- **Lemma 18 case (1) modular bridge (geometric).** [done]

For a single graph-automorphism σ with `σ^(5^k) = 1` fixing `a`, the
σ-fixed-neighbour count satisfies `|N(a) ∩ Fix(σ)| ≡ 2 (mod 5)`
(since `57 = 5·11 + 2`).

This is the §6 Lem 18 N(a) modular ingredient: for `Fix(X) = HS`
(7-regular), `|N(a) ∩ Fix(X)| = 7 ≡ 2 (mod 5)` ✓; for empty fix the
constraint must come from another vertex's view. -/
theorem lem18_neighbor_fix_mod_five
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    {a : V} (ha : σ a = a) :
    (Moore57.autFixedNeighborFinset Γ σ a).card ≡ 2 [MOD 5] :=
  Moore57.aut_card_fixedNeighborFinset_modEq_two_of_pow_five_pow
    hΓ σ smul_adj k pow_pk ha

/-- **Lemma 18 case (1) conditional + arithmetic.** [done]

If a single graph-automorphism σ has order a power of 5 (`σ^(5^k) = 1`)
and `orderOf σ ∣ 50` (the geometric Hoffman–Singleton complement
assumption `|N(a) \ Fix(σ)| = 50`), then `orderOf σ ∣ 25`. -/
theorem lem18_case1_orderOf_dvd_25_of_HS_complement
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (h_dvd : orderOf σ ∣ 50) :
    orderOf σ ∣ 25 := by
  have h5k : orderOf σ ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp h5k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  exact lem18_case1_arithmetic_5group_dvd_50_implies_25 j h_dvd

/-- **Lemma 18 case (2) conditional + arithmetic.** [done]

If a single graph-automorphism σ has order a power of 5 (`σ^(5^k) = 1`)
and `orderOf σ ∣ 55` (the geometric pentagon complement assumption
`|N(a) \ Fix(σ)| = 55`), then `orderOf σ ∣ 5`. -/
theorem lem18_case2_orderOf_dvd_5_of_pentagon_complement
    (σ : Equiv.Perm V) (k : ℕ) (pow_pk : σ ^ 5 ^ k = 1)
    (h_dvd : orderOf σ ∣ 55) :
    orderOf σ ∣ 5 := by
  have h5k : orderOf σ ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one pow_pk
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp h5k with ⟨j, _hj, hord⟩
  rw [hord] at h_dvd ⊢
  exact lem18_case2_arithmetic_5group_dvd_55_implies_5 j h_dvd

end Moore57.Papers.MacajSiran2010.S6
