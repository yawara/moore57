import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Theorem2_MakhnevPaduchikh
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Theorem5_5GroupBound
import Moore57.Papers.MacajSiran2010.Section05_Tables.Lemma15_OrderPQ

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Theorem 7

> Let Γ be a Moore graph of degree 57 on 3250 vertices and `G = Aut(Γ)`.
> If `|G|` is even then `|G|` divides one of
> ```
> 11 · 5 · 2,  5² · 2,  3³ · 2,  2p   for p ∈ {7, 11, 19}.
> ```

Proof: by Theorem 2 (Makhnev–Paduchikh), `G = ⟨Y, t⟩ × X` with `t` an
involution. Order-3 elements of `Y` are excluded by Lemma 12. By
Theorem 5, `|X| ≠ 25` when `Fix(X)` is the Hoffman–Singleton graph.
Lemma 15 excludes `Z₅₅` and `Z₂₂` sharing a `Z₁₁`, and `Z₁₀` and `Z₃₅`
sharing a `Z₅`.

Status:
* `thm7_dvd_one_of_six_from_odd_part`: **proven** — given that the
  odd part of `|G|` (i.e. `m` with `|G| = 2·m`) divides one of
  `{55, 25, 27, 7, 11, 19}`, then `|G|` divides one of the six
  Theorem 7 entries `{110, 50, 54, 14, 22, 38}`.
* `thm7_bound_110_from_odd_part`: **proven** — same hypothesis
  gives `|G| ≤ 110`.
* `thm7_even_order`: original True-stub kept for backwards compat.
-/

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 7 disjunction from odd-part dispatch**. [done]

The paper's Thm 2 (Makhnev–Paduchikh) decomposition `G = ⟨Y, t⟩ × X`
isolates the involution `t`, leaving the odd part `m = |G| / 2`
constrained by the Thm 5 (5-group bound) + Lemma 15 + Lemma 12
considerations to divide one of `{55, 25, 27, 7, 11, 19}`.

Doubling gives `|G| = 2·m` dividing one of `{110, 50, 54, 14, 22, 38}`. -/
theorem thm7_dvd_one_of_six_from_odd_part
    (n m : ℕ) (h_n : n = 2 * m)
    (h_m : m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19) :
    n ∣ 110 ∨ n ∣ 50 ∨ n ∣ 54 ∨ n ∣ 14 ∨ n ∣ 22 ∨ n ∣ 38 := by
  subst h_n
  rcases h_m with h | h | h | h | h | h
  · left; exact mul_dvd_mul_left 2 h
  · right; left; exact mul_dvd_mul_left 2 h
  · right; right; left; exact mul_dvd_mul_left 2 h
  · right; right; right; left; exact mul_dvd_mul_left 2 h
  · right; right; right; right; left; exact mul_dvd_mul_left 2 h
  · right; right; right; right; right; exact mul_dvd_mul_left 2 h

/-- **Theorem 7 bound `|G| ≤ 110` from odd-part dispatch**. [done]

Combines `thm7_dvd_one_of_six_from_odd_part` with per-branch
`Nat.le_of_dvd` to derive `|G| ≤ 110` directly. The max of
`{110, 50, 54, 14, 22, 38}` is `110`. -/
theorem thm7_bound_110_from_odd_part
    (n m : ℕ) (h_n : n = 2 * m)
    (h_m : m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19) :
    n ≤ 110 := by
  have h6 := thm7_dvd_one_of_six_from_odd_part n m h_n h_m
  rcases h6 with h | h | h | h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 110) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 50) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 54) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 14) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 22) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 38) h; omega

/-- **Theorem 7 odd-part bound (paper-faithful)**. [done]

Combined arithmetic conclusion: if `m` is the odd part (i.e. odd
divisor of `|G|`) satisfying the Thm 5 + Lem 15 + Lem 12 constraints
`m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19`, then `m ≤ 55`. -/
theorem thm7_odd_part_le_55
    (m : ℕ)
    (h_m : m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19) :
    m ≤ 55 := by
  rcases h_m with h | h | h | h | h | h
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 55) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 25) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 27) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 7) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 11) h; omega
  · have := Nat.le_of_dvd (by norm_num : (0 : ℕ) < 19) h; omega

/-- **Theorem 7 (even `|Aut(Γ)|` divides one of six values).** [deferred-heavy]

Arithmetic conclusion is captured by
`thm7_dvd_one_of_six_from_odd_part` and `thm7_bound_110_from_odd_part`.
What remains for the unconditional form is the paper's dispatch:
Thm 2 (Makhnev–Paduchikh) gives `G = ⟨Y, t⟩ × X` with `t` involution;
Thm 5 + Lems 12/15 constrain the odd part `m = |G|/2`. -/
theorem thm7_even_order (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
