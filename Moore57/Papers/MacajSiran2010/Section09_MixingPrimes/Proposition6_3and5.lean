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
* `prop6_sylow5_count_one_of_3pow_dvd_27`: **proven** — Sylow's third
  + arithmetic gives `n₅ = 1` (hence Sylow 5 normal) for any 3-group
  `|G| = 3^a · 5^b` with `a ≤ 3` (since 3^k mod 5 ≠ 1 for k ∈ {1,2,3}).
  This is the Feit–Thompson-free dispatch step.
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

/-- **Proposition 6 Sylow arithmetic core: `n₅ = 1` from Sylow's third for
`|X| = 3^a · 5^b` with `a ≤ 3`**.  [done]

This is the **Feit–Thompson-free** dispatch step for Prop 6.

Given a 3-power `3^a ∣ 27` (i.e., `a ≤ 3`) and a count `n₅ ∣ 3^a` with
`n₅ ≡ 1 (mod 5)` (the Sylow's-third-theorem conclusion for any group
of order `3^a · 5^b`), conclude `n₅ = 1`.

**Why** the paper's Feit–Thompson + Hall is not needed here: Sylow 5
subgroup IS the Hall {5}-subgroup, so we don't need solvability to
extract it.  The conclusion `n₅ = 1` directly gives "Sylow 5 is unique
and hence normal" via Mathlib `Sylow.normal_of_subsingleton`.

Arithmetic: `n₅ ∈ 3^k : k ∈ {0,1,2,3}` and `3^k mod 5 = 1, 3, 4, 2`
respectively; only `k = 0` (so `n₅ = 1`) satisfies the mod-5 condition. -/
theorem prop6_sylow5_count_one_of_3pow_dvd_27
    (n5 : ℕ) (h_dvd : n5 ∣ 27) (h_mod : n5 % 5 = 1) :
    n5 = 1 := by
  -- 27 = 3^3, so n5 is a power of 3 with exponent ≤ 3.
  have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27] at h_dvd
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp h_dvd with ⟨k, hk, hpow⟩
  rw [hpow] at h_mod
  -- 3^k mod 5 for k ∈ {0, 1, 2, 3}: 1, 3, 4, 2.  Only k = 0 gives 1.
  interval_cases k <;> simp_all

/-- **Proposition 6 Sylow arithmetic core (parametric `a ≤ 3`)**.  [done]

Same as `prop6_sylow5_count_one_of_3pow_dvd_27` but with the 3-power
exponent `a ≤ 3` as a parameter.  Covers the entire Prop 6 case
table where `a ∈ {1, 2, 3}` and `b ≥ 1`. -/
theorem prop6_sylow5_count_one_of_3pow_a_le_three
    (a n5 : ℕ) (h_a_le : a ≤ 3)
    (h_dvd : n5 ∣ 3 ^ a) (h_mod : n5 % 5 = 1) :
    n5 = 1 := by
  refine prop6_sylow5_count_one_of_3pow_dvd_27 n5 ?_ h_mod
  have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27]
  exact h_dvd.trans (pow_dvd_pow 3 h_a_le)

/-- **Proposition 6 Sylow-level conclusion: Sylow 5 is unique in `X`**.
[done]

For any finite group `X` with `Nat.card X = 3^a · 5^b` (`a ≤ 3`,
`b ≥ 1`), Sylow's third theorem combined with the arithmetic gives
that there is exactly one Sylow 5-subgroup, hence (by Mathlib
`Sylow.normal_of_subsingleton`) the Sylow 5-subgroup is normal.

This makes the paper's "`Q ◁ X`" conclusion of Prop 6 derivable from
**Sylow + arithmetic only** (no Feit–Thompson, no Philip Hall, no
Burnside).

The statement here is the arithmetic enabling the `Subsingleton (Sylow 5 X)`
deduction: combine `Nat.card (Sylow 5 X) ∣ 3^a` (Sylow's third part:
`card_dvd_index` with `|X|/|Sylow 5| = 3^a`) and
`Nat.card (Sylow 5 X) ≡ 1 [MOD 5]` (`card_sylow_modEq_one`). -/
theorem prop6_sylow5_count_one_of_card_3pow_a_5pow_b
    (n5 a : ℕ) (h_a_le : a ≤ 3)
    (h_dvd : n5 ∣ 3 ^ a) (h_mod : n5 ≡ 1 [MOD 5]) :
    n5 = 1 := by
  apply prop6_sylow5_count_one_of_3pow_a_le_three a n5 h_a_le h_dvd
  unfold Nat.ModEq at h_mod
  -- h_mod : n5 % 5 = 1 % 5 = 1
  simpa using h_mod

/-- **Proposition 6 (`(p, q) = (3, 5)` classification).** [deferred-heavy]

The arithmetic backbone for both cases is captured by
`prop6_case1_card_dvd_135` / `prop6_case2_card_dvd_375` /
`prop6_card_dvd_135_or_375`.  The Feit–Thompson-free Sylow dispatch
step is captured by `prop6_sylow5_count_one_of_*`.

What remains for the unconditional statement is the geometric/structural
side: the dichotomy between cases (1)/(2), the `|Fix(P)| = 10` Petersen
shape, and the classification of order-125 5-groups acting compatibly. -/
theorem prop6_3_and_5 : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
