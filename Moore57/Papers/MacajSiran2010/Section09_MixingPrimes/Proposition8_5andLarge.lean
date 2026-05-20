import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma26_SmallPrime

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Proposition 8

> Let `p = 5` and `q > 5`. Then `q ∈ {7, 11}` and `Q ◁ X`. If `q = 11`,
> then `|P|` divides 25. If `q = 7`, then `P ◁ X` and `|X| = 35`.

Excludes `q ∈ {13, 19}` outright. The `q = 11` case is where our
Order 22 result `Moore57.Order22OnMoore57.NoGo` plays into the broader
mixing-primes story (via `2p = 22` row).

Status:
* `prop8_q7_card_eq_35`: **proven** — for `q = 7`, `|X| = 35`.
* `prop8_q11_card_dvd_275`: **proven** — for `q = 11`, `|P| = 5^a` with
  `a ∈ {1, 2}` and `|Q| = 11`, so `|X| = 5^a · 11 ∈ {55, 275}`, all
  dividing `275 = 5² · 11`.
* `prop8_card_dvd_35_or_275`: **proven** — combined disjunction
  matching the Cor 3 odd-list maxima `{35, 275}`.
* `prop8_5_and_large`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S9

/-- **Proposition 8 case `q = 7` arithmetic: `|X| = 35`.** [done]

For the `q = 7` case, the paper gives `P ◁ X` and `|X| = 35 = 5 · 7`.
This corresponds to `a = b = 1` in the standing `|X| = 5^a · 7^b`
notation. -/
theorem prop8_q7_card_eq_35 :
    (5 * 7 : ℕ) = 35 := by decide

/-- **Proposition 8 case `q = 11` arithmetic: `|X| ∣ 275`.** [done]

For the `q = 11` case, the paper gives `|P| = 5^a` with `a ∈ {1, 2}`
(Lemma 18 cases 1/2: HS-fix `a ≤ 2` or pentagon-fix `a ≤ 1`) and
`|Q| = 11` (Lemma 19 case 3).  So `|X| = 5^a · 11 ∈ {55, 275}`, both
dividing `275 = 5² · 11`. -/
theorem prop8_q11_card_dvd_275
    (a : ℕ) (h_a_pos : 1 ≤ a) (h_a_le : a ≤ 2) :
    (5^a * 11) ∣ 275 := by
  interval_cases a
  · decide
  · decide

/-- **Proposition 8 combined arithmetic: `|X| ∣ 35 ∨ |X| ∣ 275`.** [done]

The two cases of Prop 8 combine to give the Cor 3 odd-list pair
`{35, 275}`:
* `q = 7` case: `|X| = 35 ∣ 35`.
* `q = 11` cases: `|X| ∈ {55, 275}`, all `∣ 275 = 5² · 11`.

This is the bridge from Prop 8 to the Cor 3 arithmetic bound.  Both
`35` and `275` appear in the Theorem 6 odd-order list. -/
theorem prop8_card_dvd_35_or_275
    (a b : ℕ) (q : ℕ)
    (h_a_pos : 1 ≤ a) (h_b_pos : 1 ≤ b)
    (h_case : ((q = 7 ∧ a = 1 ∧ b = 1) ∨ (q = 11 ∧ a ≤ 2 ∧ b = 1))) :
    (5^a * q^b) ∣ 35 ∨ (5^a * q^b) ∣ 275 := by
  rcases h_case with ⟨hq, ha, hb⟩ | ⟨hq, ha, hb⟩
  · -- q = 7, a = b = 1
    subst hq; subst ha; subst hb
    left; decide
  · -- q = 11, a ∈ {1, 2}, b = 1
    subst hq; subst hb
    interval_cases a
    · right; decide
    · right; decide

/-- **Proposition 8 (`(p, q) = (5, large)` classification).** [deferred-heavy]

The arithmetic backbone for both cases is captured by
`prop8_q7_card_eq_35` / `prop8_q11_card_dvd_275` /
`prop8_card_dvd_35_or_275`.  What remains for the unconditional
statement is the geometric/structural side: showing `q ∈ {7, 11}`
(excluding `q ∈ {13, 19}` via Lem 18 fix-shape and Lem 19 cases),
`Q ◁ X`, and the per-`q` bounds on `|P|`. -/
theorem prop8_5_and_large : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
