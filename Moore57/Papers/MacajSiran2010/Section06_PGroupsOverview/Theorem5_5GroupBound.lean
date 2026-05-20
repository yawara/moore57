import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma18_5Group

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Theorem 5

> Let `X` be a group of automorphisms of Γ of order a power of 5. Then one
> of the following holds:
>
> (1) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `5`;
>
> (2) `Fix(X)` is a pentagon and `|X|` divides `25`;
>
> (3) `Fix(X)` is empty and `|X|` divides `125`.

Statement only; the full proof is in `Section08_Theorem5Proof/`.

Status:
* `thm5_card_dvd_125_from_dispatch`: **proven** — given the per-case
  dispatch (|X| ∣ 5, 25, or 125), the combined |X| ∣ 125 follows.
* `thm5_card_le_125_from_dispatch`: **proven** — |X| ≤ 125 from the
  same dispatch.
* `thm5_5pow_le_3_of_dvd_125`: **proven** — for a 5-group |X| = 5^k,
  `|X| ∣ 125` forces `k ≤ 3`.
* `thm5_5group_not_625_from_dispatch`: **proven** — combined dispatch
  excludes |X| = 625.
* `thm5_5group_bound`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 5 arithmetic core: |X| dvd 125 from three-case dispatch**. [done]

Given the dispatch over the three Lem 18 fix-shape cases (HS / pentagon /
empty), each producing the Thm 5 divisibility bound, the combined
`|X| ∣ 125` follows by case analysis. -/
theorem thm5_card_dvd_125_from_dispatch
    (n : ℕ) (h : n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125) :
    n ∣ 125 := by
  rcases h with h | h | h
  · exact dvd_trans h (by decide)
  · exact dvd_trans h (by decide)
  · exact h

/-- **Theorem 5 bound: |X| ≤ 125 from three-case dispatch**. [done]

The numeric form: under the same three-case dispatch, `|X| ≤ 125`. -/
theorem thm5_card_le_125_from_dispatch
    (n : ℕ) (h : n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125) :
    n ≤ 125 := by
  have := thm5_card_dvd_125_from_dispatch n h
  exact Nat.le_of_dvd (by norm_num) this

/-- **Theorem 5 5-group exponent bound: 5^k ∣ 125 ⟹ k ≤ 3**. [done]

The exponent form: for any 5-group `5^k`, `|X| ∣ 125` forces `k ≤ 3`,
hence `|X| ∈ {1, 5, 25, 125}`. -/
theorem thm5_5pow_le_3_of_dvd_125
    (k : ℕ) (h : 5 ^ k ∣ 125) : k ≤ 3 := by
  by_contra hgt
  have h4 : 4 ≤ k := Nat.lt_of_not_le hgt
  have h_dvd_5_4 : (5 : ℕ) ^ 4 ∣ 5 ^ k := pow_dvd_pow 5 h4
  have h_dvd : (5 : ℕ) ^ 4 ∣ 125 := dvd_trans h_dvd_5_4 h
  revert h_dvd
  decide

/-- **Theorem 5 excludes 5-group of order 625**. [done]

For a 5-group `X` (`|X| = 5^k`), the Thm 5 dispatch forces `|X| ≠ 625`
(since `625 = 5^4` would require `k = 4`, but `|X| ∣ 125` gives `k ≤ 3`). -/
theorem thm5_5group_not_625_from_dispatch
    (k : ℕ) (h : 5 ^ k ∣ 5 ∨ 5 ^ k ∣ 25 ∨ 5 ^ k ∣ 125) :
    5 ^ k ≠ 625 := by
  have h_le : k ≤ 3 := thm5_5pow_le_3_of_dvd_125 k (thm5_card_dvd_125_from_dispatch _ h)
  intro heq
  -- 5^k = 625 forces k = 4 (since 5 is prime and 5^4 = 625).
  have h_625 : (5 : ℕ) ^ 4 = 625 := by decide
  -- Use injectivity of pow for base 5 ≥ 2.
  have h_5_ne_one : (5 : ℕ) ≠ 1 := by decide
  rw [← h_625] at heq
  have h_inj : k = 4 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ (5 : ℕ)) heq
  omega

/-- **Theorem 5 (5-group order bound).** [deferred-heavy]

The arithmetic content (dispatch → `|X| ∣ 125` → `k ≤ 3` → exclude 625)
is captured by `thm5_card_dvd_125_from_dispatch`,
`thm5_card_le_125_from_dispatch`, `thm5_5pow_le_3_of_dvd_125`, and
`thm5_5group_not_625_from_dispatch`. What remains for the unconditional
form is the geometric/structural side: the three-case fix-shape
dispatch via Section 8 (Prop 3 / Lem 22 / Prop 4 / Prop 5). -/
theorem thm5_5group_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
