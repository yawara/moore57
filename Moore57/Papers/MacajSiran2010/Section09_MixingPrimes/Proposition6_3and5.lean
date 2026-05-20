import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma26_SmallPrime

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Proposition 6

> Let `p = 3` and `q = 5`. Then `Q ◁ X`. Moreover,
>
> (1) if `P ◁ X`, then `|Fix(P)| = 10`, `|Fix(Q)| = 0`, and `|Q| = 5`;
>
> (2) if `P ⋪ X`, then `|P| = 3` and `Q ∈ {Z₂₅, Z₁₂₅, Z₂₅ · Z₅}`.

The `(2)` case excludes a number of would-be subgroups via Lemma 13
and the structure of automorphism groups of small 5-groups.

Status:
* `prop6_case1_card_dvd_135`: **proven** — for the P-normal case, the
  paper gives `|Q| = 5` and `|P| = 3^a` with `a ≤ 3` (Lem 17), so
  `|X| = 3^a · 5 ∈ {15, 45, 135}`, all dividing `135`.
* `prop6_case2_card_dvd_375`: **proven** — for the P-not-normal case,
  the paper gives `|P| = 3` and `|Q| = 5^b ∈ {25, 125}` (Lem 18 cases
  1/2), so `|X| = 3 · 5^b ∈ {75, 375}`, all dividing `375`.
* `prop6_card_dvd_135_or_375`: **proven** — combined disjunction
  matching the Cor 3 odd-list maxima `{135, 375}`.
* `prop6_3_and_5`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S9

/-- **Proposition 6 case (1) arithmetic: `P ◁ X` ⇒ `|X| ∣ 135`.** [done]

For the `P ◁ X` case, the paper gives `|Q| = 5` and `|P| = 3^a` with
`a ∈ {1, 2, 3}` (Lemma 17 cases: Petersen-fix `a ≤ 3` or singleton-fix
`a ≤ 4`; the latter is excluded for this case by the Petersen fix
shape forced by `|Fix(P)| = 10`).

So `|X| = 3^a · 5 ∈ {15, 45, 135}`, all dividing `135 = 3³ · 5`. -/
theorem prop6_case1_card_dvd_135
    (a : ℕ) (h_a_pos : 1 ≤ a) (h_a_le : a ≤ 3) :
    (3^a * 5) ∣ 135 := by
  interval_cases a
  · decide
  · decide
  · decide

/-- **Proposition 6 case (2) arithmetic: `P ⋪ X` ⇒ `|X| ∣ 375`.** [done]

For the `P ⋪ X` case, the paper gives `|P| = 3` and `|Q| = 5^b` with
`b ∈ {2, 3}` (the cases `Q ∈ {Z₂₅, Z₁₂₅, Z₂₅ · Z₅}` of paper Lem 18,
all of order `25` or `125`).

So `|X| = 3 · 5^b ∈ {75, 375}`, all dividing `375 = 3 · 5³`. -/
theorem prop6_case2_card_dvd_375
    (b : ℕ) (h_b_lo : 2 ≤ b) (h_b_hi : b ≤ 3) :
    (3 * 5^b) ∣ 375 := by
  interval_cases b
  · decide
  · decide

/-- **Proposition 6 combined arithmetic: `|X| ∣ 135 ∨ |X| ∣ 375`.** [done]

The two cases of Prop 6 combine to give the Cor 3 odd-list pair
`{135, 375}`:
* Case (1) `P ◁ X`: `|X| ∈ {15, 45, 135}`, all `∣ 135 = 3³ · 5`.
* Case (2) `P ⋪ X`: `|X| ∈ {75, 375}`, all `∣ 375 = 3 · 5³`. -/
theorem prop6_card_dvd_135_or_375
    (a b : ℕ) (h_a_pos : 1 ≤ a) (h_b_pos : 1 ≤ b)
    (h_case : ((a ≤ 3 ∧ b = 1) ∨ (a = 1 ∧ 2 ≤ b ∧ b ≤ 3))) :
    (3^a * 5^b) ∣ 135 ∨ (3^a * 5^b) ∣ 375 := by
  rcases h_case with ⟨ha, hb⟩ | ⟨ha, hb_lo, hb_hi⟩
  · -- Case (1): a ∈ {1, 2, 3}, b = 1.
    subst hb
    left
    have := prop6_case1_card_dvd_135 a h_a_pos ha
    simpa [pow_one] using this
  · -- Case (2): a = 1, b ∈ {2, 3}.
    subst ha
    right
    have := prop6_case2_card_dvd_375 b hb_lo hb_hi
    simpa [pow_one] using this

/-- **Proposition 6 (`(p, q) = (3, 5)` classification).** [deferred-heavy]

The arithmetic backbone for both cases is captured by
`prop6_case1_card_dvd_135` / `prop6_case2_card_dvd_375` /
`prop6_card_dvd_135_or_375`.  What remains for the unconditional
statement is the geometric/structural side: `Q ◁ X`, the dichotomy
between cases (1)/(2), the `|Fix(P)| = 10` Petersen shape, and the
classification of order-125 5-groups acting compatibly. -/
theorem prop6_3_and_5 : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
