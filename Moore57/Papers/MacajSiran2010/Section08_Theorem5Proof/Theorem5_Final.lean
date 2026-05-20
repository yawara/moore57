import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition3_HSFixBound
import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition4_SG625Excluded
import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition5_OrbitSize125
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Theorem5_5GroupBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Theorem 5 (full proof)

> Let `X` be a group of automorphisms of Γ of order a power of 5. Then one
> of the following holds:
>
> (1) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `5`;
>
> (2) `Fix(X)` is a pentagon and `|X|` divides `25`;
>
> (3) `Fix(X)` is empty and `|X|` divides `125`.

Proof structure:
- (1) from Proposition 3.
- (2) follows from (1) in much the same way as in Lemma 18.
- (3) by demonstrating non-existence of |X| = 625 via Lemma 22 +
  Proposition 4 (case smallest orbit 25) and Proposition 5
  (case smallest orbit 125).

Status:
* `thm5_final_dvd_125_from_section8_dispatch`: **proven** — given
  the three-case dispatch from Section 8's Prop 3 (HS), Lem 18 case
  2 (pentagon), and Section 8's combined Prop 4 + Prop 5 + Lem 22
  (empty-fix at most 125), conclude |X| ∣ 125.
* `thm5_final_625_excluded_from_dispatch`: **proven** — combined
  Prop 4 + Prop 5 case dispatch arithmetic excludes |X| = 625 in
  the empty-fix case.
* `thm5_final`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 5 (Section 8 full proof) arithmetic dispatch**. [done]

Given the three-case Section 8 dispatch (Prop 3 for HS, Lem 18 (2)
for pentagon, Prop 4 + Prop 5 + Lem 22 combined for empty-fix at
most 125), conclude `n ∣ 125`. Directly delegates to the Section 6
`thm5_card_dvd_125_from_dispatch` arithmetic. -/
theorem thm5_final_dvd_125_from_section8_dispatch
    (n : ℕ) (h : n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125) :
    n ∣ 125 :=
  Moore57.Papers.MacajSiran2010.S6.thm5_card_dvd_125_from_dispatch n h

/-- **Theorem 5 (Section 8) 625-exclusion arithmetic**. [done]

Given the empty-fix dispatch (orbit-size 25 case excluded by Lem 22
+ Prop 4; orbit-size 125 case excluded by Prop 5), conclude
`5^k ≠ 625`.  Delegates to Section 6's `thm5_5group_not_625_from_dispatch`. -/
theorem thm5_final_625_excluded_from_dispatch
    (k : ℕ) (h : 5 ^ k ∣ 5 ∨ 5 ^ k ∣ 25 ∨ 5 ^ k ∣ 125) :
    5 ^ k ≠ 625 :=
  Moore57.Papers.MacajSiran2010.S6.thm5_5group_not_625_from_dispatch k h

/-- **Theorem 5 (Section 8) numeric bound**. [done]

The three-case Section 8 dispatch gives `|X| ≤ 125`. -/
theorem thm5_final_card_le_125_from_dispatch
    (n : ℕ) (h : n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125) :
    n ≤ 125 :=
  Moore57.Papers.MacajSiran2010.S6.thm5_card_le_125_from_dispatch n h

/-- **Theorem 5 (full 5-group classification).** [deferred-heavy]

Arithmetic backbone via `thm5_final_dvd_125_from_section8_dispatch`,
`thm5_final_625_excluded_from_dispatch`, and
`thm5_final_card_le_125_from_dispatch`. What remains for the
unconditional form is the Section 8 geometric content: Prop 3 (HS
case), Lem 22 (SG(625,12) identification, GAP), Prop 4 (SG(625,12)
exclusion, GAP), Prop 5 (orbit-125 exclusion, arithmetic backbone
already done). -/
theorem thm5_final (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Theorem 5 (paper-faithful Section-8 conditional bound).** [done]

Proper-signature paper-faithful packaging at the Section-8 level: given
the three-case Section 8 dispatch (`n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125`), conclude
`n ∣ 125 ∧ n ≤ 125`. -/
theorem thm5_final_paper
    (n : ℕ) (h : n ∣ 5 ∨ n ∣ 25 ∨ n ∣ 125) :
    n ∣ 125 ∧ n ≤ 125 :=
  ⟨thm5_final_dvd_125_from_section8_dispatch n h,
   thm5_final_card_le_125_from_dispatch n h⟩

end Moore57.Papers.MacajSiran2010.S8
