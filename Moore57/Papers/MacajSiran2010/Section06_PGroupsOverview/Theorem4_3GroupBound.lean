import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma17_3Group

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Theorem 4

> Let `X` be a group of automorphisms of Γ of order `3^k`. Then `k ≤ 3`.

Statement only; the full proof is in `Section07_Theorem4Proof/`.

Status:
* `thm4_card_dvd_27_from_dispatch_and_cor2`: **proven** — given the
  Lem 17 dispatch (`n ∣ 27 ∨ n ∣ 81`) plus the Section 7 Cor 2
  exclusion (`n ≠ 81`), the combined `n ∣ 27` follows.
* `thm4_3pow_le_3_from_dispatch`: **proven** — exponent form, for
  a 3-group `3^k`, the dispatch plus `3^k ≠ 81` forces `k ≤ 3`.
* `thm4_card_le_27_from_dispatch_and_cor2`: **proven** — numeric form,
  `n ≤ 27`.
* `thm4_3group_bound`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 4 arithmetic core: `n ∣ 27` from dispatch + Cor 2 exclusion**. [done]

Given the two-case Lem 17 dispatch (`Fix(X) = Petersen ⟹ n ∣ 27` /
`Fix(X) = singleton ⟹ n ∣ 81`), plus the Section 7 Cor 2 exclusion
of `n = 81` (the unique SG(81, 9) is excluded), conclude `n ∣ 27`.

The case-(1) branch is direct. For case (2), `n ∣ 81` with `n ≠ 81`
forces `n ∈ {1, 3, 9, 27}`, all dividing `27`. -/
theorem thm4_card_dvd_27_from_dispatch_and_cor2
    (n : ℕ) (h_dispatch : n ∣ 27 ∨ n ∣ 81)
    (h_cor2 : n ≠ 81) :
    n ∣ 27 := by
  rcases h_dispatch with h | h
  · exact h
  · -- n ∣ 81 and n ≠ 81 forces n ≤ 27.
    have h_le : n ≤ 81 := Nat.le_of_dvd (by norm_num) h
    -- 81 has divisors {1, 3, 9, 27, 81}; exclude 81.
    have h_lt : n < 81 := lt_of_le_of_ne h_le h_cor2
    -- n ∣ 81 with n < 81 means n ∈ {1, 3, 9, 27}.
    -- Use omega-style: a divisor of 81 less than 81 is at most 27.
    have h_le_27 : n ≤ 27 := by
      -- 81 = 27 · 3, so a proper divisor is at most 27.
      rcases Nat.eq_or_lt_of_le (Nat.le_of_dvd (by norm_num) h) with heq | hlt2
      · -- heq : n = 81, contradiction
        exact absurd heq h_cor2
      · -- hlt2 : n < 81
        -- 81 / 2 = 40.5, so largest proper divisor ≤ 40. Actually 81/3 = 27.
        -- Use Nat.le_of_dvd_lt: n ∣ 81 with n < 81 means n ≤ 81 / 2... no.
        -- Cleanest: enumerate divisors.
        -- n ∣ 81 = 3^4, so n is a power of 3 ≤ 81: n ∈ {1, 3, 9, 27, 81}.
        -- Since n < 81, n ≤ 27.
        have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
        rw [h81] at h
        rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp h with ⟨j, hj, hpow⟩
        rw [hpow]
        rw [hpow] at hlt2
        -- 3^j < 81 = 3^4, so j ≤ 3.
        have : j ≤ 3 := by
          by_contra hjgt
          have h4 : 4 ≤ j := Nat.lt_of_not_le hjgt
          have h_ge : (3 : ℕ) ^ 4 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h4
          omega
        interval_cases j <;> decide
    -- Now show n ≤ 27 ∧ n ∣ 81 ⟹ n ∣ 27.
    -- n ∣ 81, n ≤ 27. The divisors of 81 ≤ 27 are {1, 3, 9, 27}, all dvd 27.
    have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
    rw [h81] at h
    rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp h with ⟨j, hj, hpow⟩
    rw [hpow] at h_le_27 ⊢
    have : j ≤ 3 := by
      by_contra hjgt
      have h4 : 4 ≤ j := Nat.lt_of_not_le hjgt
      have h_ge : (3 : ℕ) ^ 4 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h4
      have h81_val : (3 : ℕ) ^ 4 = 81 := by norm_num
      omega
    interval_cases j <;> decide

/-- **Theorem 4 exponent bound: 3-group with dispatch + ≠ 81 has k ≤ 3**. [done]

For a 3-group `|X| = 3^k`, the Lem 17 dispatch plus Cor 2 exclusion
forces `k ≤ 3`. -/
theorem thm4_3pow_le_3_from_dispatch
    (k : ℕ) (h_dispatch : 3 ^ k ∣ 27 ∨ 3 ^ k ∣ 81)
    (h_not_81 : 3 ^ k ≠ 81) :
    k ≤ 3 := by
  by_contra hgt
  have h4 : 4 ≤ k := Nat.lt_of_not_le hgt
  have h_ge : (3 : ℕ) ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h4
  have h81 : (3 : ℕ) ^ 4 = 81 := by norm_num
  rcases h_dispatch with h | h
  · -- 3^k ∣ 27 and 3^k ≥ 81 > 27, contradiction.
    have h_le_27 : 3 ^ k ≤ 27 := Nat.le_of_dvd (by norm_num) h
    omega
  · -- 3^k ∣ 81 and 3^k ≥ 81 forces 3^k = 81, contradicting h_not_81.
    have h_le_81 : 3 ^ k ≤ 81 := Nat.le_of_dvd (by norm_num) h
    have h_eq : 3 ^ k = 81 := by omega
    exact h_not_81 h_eq

/-- **Theorem 4 numeric bound: |X| ≤ 27 from dispatch + Cor 2 exclusion**. [done] -/
theorem thm4_card_le_27_from_dispatch_and_cor2
    (n : ℕ) (h_dispatch : n ∣ 27 ∨ n ∣ 81)
    (h_cor2 : n ≠ 81) :
    n ≤ 27 := by
  have := thm4_card_dvd_27_from_dispatch_and_cor2 n h_dispatch h_cor2
  exact Nat.le_of_dvd (by norm_num) this

/-- **Theorem 4 (3-group order ≤ 27).** [deferred-heavy]

The arithmetic content (Lem 17 dispatch + Cor 2 SG(81, 9) exclusion ⟹
`n ∣ 27` / `k ≤ 3`) is captured by `thm4_card_dvd_27_from_dispatch_and_cor2`,
`thm4_3pow_le_3_from_dispatch`, and `thm4_card_le_27_from_dispatch_and_cor2`.
What remains for the unconditional form is the Cor 2 geometric content. -/
theorem thm4_3group_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
