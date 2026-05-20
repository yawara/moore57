import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma26_SmallPrime

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Proposition 7

> Let `p = 3` and `q > 5`. Then `q ≠ 11`, `Q ◁ X`, `P ⋪ X`. If `q = 19`,
> then `|P|` divides 9; if `q ∈ {7, 13}`, then `|P| = 3`.

Proof outline (paper): the `P` element of order 3 fixes a Petersen graph
whose automorphism group has order 120, so `P ⋪ X`. For `q = 13`,
`P ◁ X` is impossible since `Fix(P)` lacks order-13 automorphisms.
Combinatorial subgroup analysis on `Aut(Q) ⊃ P` excludes cyclic order 21
when `Q = Z₂₇`.

Status:
* `prop7_card_dvd_147_39_or_171`: **proven** — the paper's per-case
  size constraints (`q = 7 ⇒ |P| = 3 ∧ |Q| ∈ {7, 49}`; `q = 13 ⇒
  |X| = 39`; `q = 19 ⇒ |P| ∈ {3, 9}, |Q| = 19`) combine to give
  `|X| ∣ 147 ∨ |X| ∣ 39 ∨ |X| ∣ 171`.
* `prop7_card_enumeration`: **proven** — explicit enumeration of the
  five `|X|` values.
* `prop7_3_and_large`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S9

/-- **Proposition 7 arithmetic enumeration (combined card list)**. [done]

Given the paper's per-case structural input for `p = 3, q > 5`:
* `q = 7`: `|P| = 3` and `|Q| ∈ {7, 49}` (Lem 19 cases 4/5).
* `q = 13`: `|P| = 3` and `|Q| = 13` (Lem 19 case 1).
* `q = 19`: `|P| ∈ {3, 9}` and `|Q| = 19` (Lem 19 case 2).

then `|X| = 3^a · q^b ∈ {21, 39, 57, 147, 171}`. -/
theorem prop7_card_enumeration
    (a b : ℕ) (q : ℕ)
    (h_a_pos : 1 ≤ a) (h_b_pos : 1 ≤ b)
    (h_pq_constraints : ((q = 7 ∧ a = 1 ∧ b ≤ 2) ∨
                         (q = 13 ∧ a = 1 ∧ b = 1) ∨
                         (q = 19 ∧ a ≤ 2 ∧ b = 1))) :
    3^a * q^b ∈ ({21, 39, 57, 147, 171} : Finset ℕ) := by
  rcases h_pq_constraints with ⟨hq, ha, hb⟩ | ⟨hq, ha, hb⟩ | ⟨hq, ha, hb⟩
  · -- q = 7, a = 1, 1 ≤ b ≤ 2
    subst hq; subst ha
    interval_cases b
    · decide
    · decide
  · -- q = 13, a = 1, b = 1
    subst hq; subst ha; subst hb
    decide
  · -- q = 19, 1 ≤ a ≤ 2, b = 1
    subst hq; subst hb
    interval_cases a
    · decide
    · decide

/-- **Proposition 7 arithmetic divisibility (Cor 3 odd-list form)**. [done]

The Prop 7 cases all give `|X|` that divides one of the Thm 6 odd-list
maxima `{147, 39, 171}`:
* `q = 7` cases (`|X| ∈ {21, 147}`): both divide `147`.
* `q = 13` case (`|X| = 39`): divides `39`.
* `q = 19` cases (`|X| ∈ {57, 171}`): both divide `171`.

This is the bridge from Prop 7 to the Cor 3 arithmetic bound. -/
theorem prop7_card_dvd_147_39_or_171
    (a b : ℕ) (q : ℕ)
    (h_a_pos : 1 ≤ a) (h_b_pos : 1 ≤ b)
    (h_pq_constraints : ((q = 7 ∧ a = 1 ∧ b ≤ 2) ∨
                         (q = 13 ∧ a = 1 ∧ b = 1) ∨
                         (q = 19 ∧ a ≤ 2 ∧ b = 1))) :
    (3^a * q^b) ∣ 147 ∨ (3^a * q^b) ∣ 39 ∨ (3^a * q^b) ∣ 171 := by
  rcases h_pq_constraints with ⟨hq, ha, hb⟩ | ⟨hq, ha, hb⟩ | ⟨hq, ha, hb⟩
  · -- q = 7
    subst hq; subst ha
    interval_cases b
    · left; decide
    · left; decide
  · -- q = 13
    subst hq; subst ha; subst hb
    right; left; decide
  · -- q = 19
    subst hq; subst hb
    interval_cases a
    · right; right; decide
    · right; right; decide

/-- **Proposition 7 (`(p, q) = (3, large)` classification).** [deferred-heavy]

The arithmetic content of the case-by-case `|X|` enumeration is captured
by `prop7_card_enumeration` and the Cor 3 bridge by
`prop7_card_dvd_147_39_or_171`.  What remains for the unconditional
statement is the geometric/structural side: showing `q ≠ 11`, `Q ◁ X`,
`P ⋪ X`, and the per-`q` bounds on `|P|` and `|Q|`. -/
theorem prop7_3_and_large : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
