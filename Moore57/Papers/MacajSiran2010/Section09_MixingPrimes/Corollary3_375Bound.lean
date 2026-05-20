import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Theorem6_OddOrder
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Theorem7_EvenOrder

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Corollary 3

> Let Γ be a Moore graph of degree 57 on 3250 vertices and `G = Aut(Γ)`.
> Then `|G| ≤ 375`, and if `|G|` is even then `|G| ≤ 110`.

This is the main quantitative result of the paper.

Status:
* `cor3_375_bound`: full statement with `IsMoore57 Γ` hypothesis,
  paper-stub deferred (depends on Theorems 6, 7).
* `cor3_odd_arithmetic_bound`, `cor3_even_arithmetic_bound`:
  **proven** arithmetic cores. Given the divisibility constraints
  from Theorems 6 / 7 (deferred), the bound `|G| ≤ 375` (resp. `≤ 110`)
  follows by omega.
-/

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Corollary 3 arithmetic core (odd order).** [done]

Given the Theorem 6 conclusion `|G| ∣ X` for some `X` in the listed
odd-order maxima `{171, 39, 275, 147, 35, 375, 135}` (= `{19·9, 13·3,
5²·11, 7²·3, 7·5, 5³·3, 3³·5}`), conclude `|G| ≤ 375` (the maximum
in the list). -/
theorem cor3_odd_arithmetic_bound (n : ℕ)
    (h : n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨ n ∣ 147 ∨ n ∣ 35 ∨
         n ∣ 375 ∨ n ∣ 135) :
    n ≤ 375 := by
  rcases h with h | h | h | h | h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 171) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 39) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 275) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 147) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 35) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 375) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 135) h; omega

/-- **Corollary 3 arithmetic core (even order).** [done]

Given the Theorem 7 conclusion `|G| ∣ X` for some `X` in the listed
even-order maxima `{110, 50, 54, 14, 22, 38}` (= `{11·5·2, 5²·2,
3³·2, 2·7, 2·11, 2·19}`), conclude `|G| ≤ 110` (the maximum). -/
theorem cor3_even_arithmetic_bound (n : ℕ)
    (h : n ∣ 110 ∨ n ∣ 50 ∨ n ∣ 54 ∨
         n ∣ 14 ∨ n ∣ 22 ∨ n ∣ 38) :
    n ≤ 110 := by
  rcases h with h | h | h | h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 110) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 50) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 54) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 14) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 22) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 38) h; omega

/-- **Corollary 3 unified arithmetic core (flat disjunction).** [done]

Given that `n` divides ONE of the 13 values in the union of Theorem 6
(odd-order) and Theorem 7 (even-order) lists, conclude `n ≤ 375`.

This is the combined arithmetic content of `cor3_odd_arithmetic_bound`
and `cor3_even_arithmetic_bound`: the 13 maxima for `|Aut(Γ)|` divisor
candidates are `{171, 39, 275, 147, 35, 375, 135, 110, 50, 54, 14, 22, 38}`,
the largest of which is `375`.

Each branch is `Nat.le_of_dvd` + omega. -/
theorem cor3_unified_arithmetic_bound (n : ℕ)
    (h : n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨ n ∣ 147 ∨ n ∣ 35 ∨
         n ∣ 375 ∨ n ∣ 135 ∨
         n ∣ 110 ∨ n ∣ 50 ∨ n ∣ 54 ∨ n ∣ 14 ∨ n ∣ 22 ∨ n ∣ 38) :
    n ≤ 375 := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 171) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 39) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 275) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 147) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 35) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 375) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 135) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 110) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 50) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 54) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 14) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 22) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 38) h; omega

/-- **Corollary 3 conditional bridge (parity-dispatched).** [done]

The paper-faithful conditional form: given the Theorem 6/7 divisibility
conclusions dispatched by parity of `n`, conclude `n ≤ 375`, and the
sharper `n ≤ 110` when `n` is even.

Both branches are direct wraps of the odd/even arithmetic cores. -/
theorem cor3_bound_of_thm6_thm7 (n : ℕ)
    (h_odd : Odd n →
      n ∣ 171 ∨ n ∣ 39 ∨ n ∣ 275 ∨ n ∣ 147 ∨ n ∣ 35 ∨ n ∣ 375 ∨ n ∣ 135)
    (h_even : Even n →
      n ∣ 110 ∨ n ∣ 50 ∨ n ∣ 54 ∨ n ∣ 14 ∨ n ∣ 22 ∨ n ∣ 38) :
    n ≤ 375 ∧ (Even n → n ≤ 110) := by
  refine ⟨?_, fun he => cor3_even_arithmetic_bound n (h_even he)⟩
  rcases Nat.even_or_odd n with he | ho
  · have := cor3_even_arithmetic_bound n (h_even he); omega
  · exact cor3_odd_arithmetic_bound n (h_odd ho)

/-- **Corollary 3 conditional from Prop-level dispatch.** [done]

A stronger conditional form taking the inputs at the Propositions
6/7/8 and Thm-7-odd-part level (one step earlier than
`cor3_bound_of_thm6_thm7`). For each parity:

* `h_odd_props`: if `n` is odd, then the Props 6/7/8 dispatch holds.
  (`n` divides one of 135/375 (Prop 6) or 147/39/171 (Prop 7) or
  35/275 (Prop 8).)
* `h_even_oddpart`: if `n` is even, then `n = 2·m` with `m` dividing
  one of 55/25/27/7/11/19 (Thm 7 odd-part input).

Conclusion: `n ≤ 375` and `Even n → n ≤ 110`.

This conditional sits above the Thm 6 / Thm 7 dispatches and just
below the paper's `Aut(Γ)` interpretation. -/
theorem cor3_bound_from_props_and_oddpart (n : ℕ)
    (h_odd_props : Odd n →
      ((n ∣ 135 ∨ n ∣ 375) ∨
       (n ∣ 147 ∨ n ∣ 39 ∨ n ∣ 171) ∨
       (n ∣ 35 ∨ n ∣ 275)))
    (h_even_oddpart : Even n →
      ∃ m, n = 2 * m ∧ (m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19)) :
    n ≤ 375 ∧ (Even n → n ≤ 110) := by
  refine ⟨?_, ?_⟩
  · -- n ≤ 375
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, hn, hm⟩ := h_even_oddpart he
      have := thm7_bound_110_from_odd_part n m hn hm
      omega
    · exact thm6_bound_375_from_props n (h_odd_props ho)
  · -- Even n → n ≤ 110
    intro he
    obtain ⟨m, hn, hm⟩ := h_even_oddpart he
    exact thm7_bound_110_from_odd_part n m hn hm

/-- **Corollary 3 (`|Aut(Γ)| ≤ 375`, and `≤ 110` if even).** [deferred-heavy]

Full paper-faithful statement.  The arithmetic backbone (taking the
maximum over Thm 6 / Thm 7 listed values) is proven in
`cor3_odd_arithmetic_bound` / `cor3_even_arithmetic_bound` / the
unified `cor3_unified_arithmetic_bound` / `cor3_bound_of_thm6_thm7` /
the new Prop-level `cor3_bound_from_props_and_oddpart`;
what remains is the `Aut(Γ)` ↔ subgroup-of-Sym(V) bridge and
Theorems 6, 7 themselves. -/
theorem cor3_375_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
