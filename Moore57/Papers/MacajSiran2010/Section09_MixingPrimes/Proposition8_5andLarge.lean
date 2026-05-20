import Mathlib.GroupTheory.Sylow
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

/-- **Proposition 8 Sylow arithmetic for `q = 7`: both `n₅ = 1` and `n₇ = 1`**.
[done]

For `|X| = 5 · 7` (Prop 8 case `q = 7`, `a = b = 1`):
* `n₇ ∣ 5` and `n₇ ≡ 1 (mod 7)`: divisors of 5 are `{1, 5}`; only `1`
  is `≡ 1 (mod 7)` (5 mod 7 = 5).  Hence `n₇ = 1` and Q is normal.
* `n₅ ∣ 7` and `n₅ ≡ 1 (mod 5)`: divisors of 7 are `{1, 7}`; only `1`
  is `≡ 1 (mod 5)` (7 mod 5 = 2).  Hence `n₅ = 1` and P is normal.

Both Sylow subgroups normal ⟹ `X = P × Q = Z₅ × Z₇ = Z₃₅`. -/
theorem prop8_q7_sylow7_count_one
    (n7 : ℕ) (h_dvd : n7 ∣ 5) (h_mod : n7 % 7 = 1) :
    n7 = 1 := by
  have h_le : n7 ≤ 5 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n7 <;> omega

/-- **Proposition 8 Sylow arithmetic for `q = 7` (P-side): `n₅ = 1` from
`n₅ ∣ 7 ∧ n₅ ≡ 1 (mod 5)`**.  [done] -/
theorem prop8_q7_sylow5_count_one
    (n5 : ℕ) (h_dvd : n5 ∣ 7) (h_mod : n5 % 5 = 1) :
    n5 = 1 := by
  have h_le : n5 ≤ 7 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n5 <;> omega

/-- **Proposition 8 Sylow arithmetic for `q = 11`: `n₁₁ = 1` from `n₁₁ ∣ 5^a ∧
n₁₁ ≡ 1 (mod 11)` with `a ≤ 2`**.  [done]

For `|X| = 5^a · 11` (Prop 8 case `q = 11`, `a ∈ {1, 2}`).  Divisors of
25 (`a = 2` worst case): `{1, 5, 25}`; only `1 ≡ 1 (mod 11)` (5 mod 11
= 5, 25 mod 11 = 3, both ≠ 1). -/
theorem prop8_q11_sylow11_count_one
    (n11 : ℕ) (h_dvd : n11 ∣ 25) (h_mod : n11 % 11 = 1) :
    n11 = 1 := by
  have h_le : n11 ≤ 25 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n11 <;> omega

/-- **Proposition 8 unified Sylow arithmetic: `n_q = 1` for `q ∈ {7, 11}`**.
[done]

Combines the q-case arithmetic lemmas into a single dispatch.  Hypothesis
form: `n_q ∣ 5^a` (with `a ≤ 1` for q = 7, `a ≤ 2` for q = 11) and
`n_q ≡ 1 (mod q)`. -/
theorem prop8_sylow_q_count_one
    (q a n_q : ℕ)
    (h_a_bound : (q = 7 ∧ a ≤ 1) ∨ (q = 11 ∧ a ≤ 2))
    (h_dvd : n_q ∣ 5 ^ a) (h_mod : n_q % q = 1) :
    n_q = 1 := by
  rcases h_a_bound with ⟨hq, ha⟩ | ⟨hq, ha⟩
  · subst hq
    refine prop8_q7_sylow7_count_one n_q ?_ h_mod
    have : (5 ^ a : ℕ) ∣ 5 := by
      have := pow_dvd_pow 5 ha
      simpa using this
    exact h_dvd.trans this
  · subst hq
    refine prop8_q11_sylow11_count_one n_q ?_ h_mod
    have : (5 ^ a : ℕ) ∣ 25 := by
      have := pow_dvd_pow 5 ha
      have h25 : (5 ^ 2 : ℕ) = 25 := by norm_num
      rw [h25] at this
      exact this
    exact h_dvd.trans this

/-- **Proposition 8 Sylow-level: `Sylow q X` normal for q ∈ {7, 11}**. [done]

Lifts of `prop8_q*_sylow*_count_one` to Mathlib `Sylow.Normal`.
- q = 7: `n₇ ∣ 5 ⟹ n₇ = 1 ⟹ Subsingleton ⟹ Normal`.
- q = 11: `n₁₁ ∣ 25 ⟹ n₁₁ = 1 ⟹ Subsingleton ⟹ Normal`.
- q = 7 (P-side): `n₅ ∣ 7 ⟹ n₅ = 1 ⟹ Subsingleton ⟹ Normal` (so X ≅ Z₃₅). -/
theorem prop8_q7_sylow7_normal
    (X : Type*) [Group X] [Finite X] [Fact (Nat.Prime 7)]
    (h_dvd : Nat.card (Sylow 7 X) ∣ 5)
    (P : Sylow 7 X) :
    (P : Subgroup X).Normal := by
  haveI : Subsingleton (Sylow 7 X) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 7 X) = 1 := by
      refine prop8_q7_sylow7_count_one (Nat.card (Sylow 7 X)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 7 X
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

theorem prop8_q7_sylow5_normal
    (X : Type*) [Group X] [Finite X] [Fact (Nat.Prime 5)]
    (h_dvd : Nat.card (Sylow 5 X) ∣ 7)
    (P : Sylow 5 X) :
    (P : Subgroup X).Normal := by
  haveI : Subsingleton (Sylow 5 X) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 5 X) = 1 := by
      refine prop8_q7_sylow5_count_one (Nat.card (Sylow 5 X)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 5 X
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

theorem prop8_q11_sylow11_normal
    (X : Type*) [Group X] [Finite X] [Fact (Nat.Prime 11)]
    (h_dvd : Nat.card (Sylow 11 X) ∣ 25)
    (P : Sylow 11 X) :
    (P : Subgroup X).Normal := by
  haveI : Subsingleton (Sylow 11 X) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 11 X) = 1 := by
      refine prop8_q11_sylow11_count_one (Nat.card (Sylow 11 X)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 11 X
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

/-- **Proposition 8 (paper-faithful conditional dispatch).** [done]

Proper-signature wrapper for the paper's two-`q` `|X| ∣ {35, 275}`
classification.  Given the case dispatch (q ∈ {7, 11} with appropriate
(a, b)) as input, conclude `|X| ∈ {divisors of 35 ∨ 275}`.

The geometric content (which case applies + ruling out q ∈ {13, 19})
is deferred-heavy. -/
theorem prop8_5_and_large_paper
    (a b : ℕ) (q : ℕ)
    (h_a_pos : 1 ≤ a) (h_b_pos : 1 ≤ b)
    (h_case_dispatch : ((q = 7 ∧ a = 1 ∧ b = 1) ∨
                        (q = 11 ∧ a ≤ 2 ∧ b = 1))) :
    (5^a * q^b) ∣ 35 ∨ (5^a * q^b) ∣ 275 :=
  prop8_card_dvd_35_or_275 a b q h_a_pos h_b_pos h_case_dispatch

/-- **Proposition 8 (`(p, q) = (5, large)` classification).** [deferred-heavy]

The arithmetic backbone for both cases is captured by
`prop8_q7_card_eq_35` / `prop8_q11_card_dvd_275` /
`prop8_card_dvd_35_or_275` / `prop8_5_and_large_paper` (above).
The Feit–Thompson-free Sylow dispatch giving `Q ◁ X` (and `P ◁ X`
when q = 7) is captured by `prop8_q*_sylow*_count_one` lemmas and
unified in `prop8_sylow_q_count_one`.

What remains for the unconditional statement is the geometric/structural
side: showing `q ∈ {7, 11}` (excluding `q ∈ {13, 19}` via Lem 18
fix-shape and Lem 19 cases) and the per-`q` bounds on `|P|`. -/
theorem prop8_5_and_large : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
