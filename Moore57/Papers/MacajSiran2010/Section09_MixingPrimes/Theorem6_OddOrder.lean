import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition6_3and5
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition7_3andLarge
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition8_5andLarge

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Theorem 6

> Let Γ be a Moore graph of degree 57 on 3250 vertices and `G = Aut(Γ)`.
> If `|G|` is odd then `|G|` divides one of
> ```
> 19 · 3²,  13 · 3,  5² · 11,  7² · 3,  7 · 5,  5³ · 3,  3³ · 5.
> ```

Proof structure: by Feit–Thompson (`Mathlib.GroupTheory.Solvable`),
`G` is solvable; by Philip Hall, `G` has Hall subgroups of all
coprime orders. Combine Propositions 6, 7, 8 to enumerate at most
two-prime configurations. The only would-be three-prime config is
`Z₅ × Z₇ · Z₃`, excluded by Lemma 15.

Status:
* `thm6_dvd_one_of_seven_from_props`: **proven** — given the
  per-Prop case dispatch as hypothesis, the seven-way disjunction
  of Theorem 6 follows by `tauto`.
* `thm6_bound_375_from_props`: **proven** — combined with Cor 3
  arithmetic, the same per-Prop dispatch gives `|G| ≤ 375`.
* `thm6_odd_order`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 6 disjunction from Props 6/7/8 dispatch**. [done]

Given the per-case Proposition 6 / 7 / 8 arithmetic outputs as a
combined hypothesis, the seven-way Theorem 6 disjunction follows
by pure boolean disjunction rearrangement.

The hypothesis structure mirrors the paper's case analysis:
* `h_3and5`: Prop 6's `(p, q) = (3, 5)` output (`∣ 135 ∨ ∣ 375`).
* `h_3andLarge`: Prop 7's `(p, q) = (3, q>5)` output (`∣ 147 ∨ ∣ 39 ∨ ∣ 171`).
* `h_5andLarge`: Prop 8's `(p, q) = (5, q>5)` output (`∣ 35 ∨ ∣ 275`).

What this lemma does NOT cover (deferred-heavy):
* The dispatch itself: showing `|G|` falls into one of the three
  two-prime cases (Sylow + Feit–Thompson + Hall).
* The single-prime case: `|G| = p^k` with `p ∈ {3, 5, 7, 11, 13, 19}`
  bounded by Lems 16-19; the resulting divisors also appear in the
  seven-list. -/
theorem thm6_dvd_one_of_seven_from_props
    (n : ℕ)
    (h_dispatch :
       (n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)) :
    n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨
    n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135 := by
  tauto

/-- **Theorem 6 bound `|G| ≤ 375` from Props 6/7/8 dispatch**. [done]

Combines `thm6_dvd_one_of_seven_from_props` with
`Nat.le_of_dvd` per branch to derive `|G| ≤ 375` directly.

(`Corollary3_375Bound` imports this file, so the cleaner re-use of
`cor3_unified_arithmetic_bound` is not available here.) -/
theorem thm6_bound_375_from_props
    (n : ℕ)
    (h_dispatch :
       (n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)) :
    n ≤ 375 := by
  rcases h_dispatch with (h | h) | (h | h | h) | (h | h)
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 135) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 375) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 147) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 39) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 171) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 35) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 275) h; omega

/-- **Theorem 6 conditional from per-case Props 6/7/8 + 1-prime input**. [done]

Stronger conditional including the single-prime case dispatch. The
input is the disjunction `1-prime ∨ 2-prime`, matching the paper's
case split. Given either branch, conclude `|G|` divides one of the
seven Theorem 6 entries.

* 1-prime branch: from Lems 16/17/18/19 — each divisor `27, 125, 49,
  11, 13, 19` divides one of the seven entries (`135 = 27·5`,
  `375 = 5³·3`, `147 = 7²·3`, `275 = 5²·11`, `39 = 13·3`, `171 = 19·9`).
* 2-prime branch: from Props 6/7/8, delegate to
  `thm6_dvd_one_of_seven_from_props`. -/
theorem thm6_dvd_one_of_seven_from_props_and_one_prime
    (n : ℕ)
    (h_case_dispatch :
       (n ∣ 27 ∨ n ∣ 125 ∨ n ∣ 49 ∨ n ∣ 11 ∨ n ∣ 13 ∨ n ∣ 19) ∨
       ((n ∣ 135 ∨ n ∣ 375) ∨
        (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
        (n ∣ 35 ∨ n ∣ 275))) :
    n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨
    n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135 := by
  rcases h_case_dispatch with h_one | h_two
  · -- 1-prime case: each entry divides one of the seven.
    rcases h_one with h | h | h | h | h | h
    · right; right; right; right; right; right; exact dvd_trans h (by decide)
    · right; right; right; right; right; left; exact dvd_trans h (by decide)
    · right; right; right; left; exact dvd_trans h (by decide)
    · right; right; left; exact dvd_trans h (by decide)
    · right; left; exact dvd_trans h (by decide)
    · left; exact dvd_trans h (by decide)
  · -- 2-prime case: delegate to the Props 6/7/8 disjunction lemma.
    exact thm6_dvd_one_of_seven_from_props n h_two

/-- **Theorem 6 (paper-faithful conditional dispatch).** [done]

Proper-signature paper-faithful packaging: given the Props 6/7/8
dispatch (`n` divides one of three case-products) as input, conclude
`n ∈ divisors of {171, 39, 275, 147, 35, 375, 135}` and `n ≤ 375`.

The geometric content (Props 6/7/8 cases + Feit-Thompson solvability +
Philip Hall + Lem 15) is deferred-heavy. -/
theorem thm6_odd_order_paper
    (n : ℕ)
    (h_dispatch :
       (n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)) :
    (n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨ n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135)
    ∧ n ≤ 375 :=
  ⟨thm6_dvd_one_of_seven_from_props n h_dispatch,
   thm6_bound_375_from_props n h_dispatch⟩

/-- **Theorem 6 (odd `|Aut(Γ)|` divides one of seven values).** [deferred-heavy]

Arithmetic conclusion is captured by
`thm6_dvd_one_of_seven_from_props` and
`thm6_dvd_one_of_seven_from_props_and_one_prime` and combined in
`thm6_odd_order_paper` (above).

What remains for the unconditional form is the paper's dispatch:
Feit–Thompson solvability + Philip Hall subgroups for the 2-prime case,
and Lemma 15 for the 3-prime case exclusion. -/
theorem thm6_odd_order (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
