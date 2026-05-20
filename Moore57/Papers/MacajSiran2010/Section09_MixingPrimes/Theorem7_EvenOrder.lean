import Mathlib.GroupTheory.Sylow
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

/-! ### Sylow arithmetic for even-order dispatch (Feit–Thompson-free)

The Thm 7 even-order list is `{110, 50, 54, 14, 22, 38}`.  For each
order `|G|` in this list, Sylow's third theorem combined with mod
arithmetic forces the "large prime" Sylow subgroup to be normal,
giving the structural decomposition needed for the paper's
`G = ⟨Y, t⟩ × X` form **without** invoking Feit–Thompson or Philip
Hall.

All six even orders share the 3-prime case logic for 110 = 2·5·11
(via Sylow 11 normal ⟹ Hall {5, 11} subgroup of order 55 exists),
or are 2-prime with the Sylow of the odd prime normal.
-/

/-- **Theorem 7 Sylow arithmetic for `|G| = 110 = 2·5·11`: `n₁₁ = 1`**. [done]

For `|G| = 2·5·11 = 110`, Sylow's third gives `n₁₁ ∣ 10` (since
`|G|/|Sylow 11| = 10`) and `n₁₁ ≡ 1 (mod 11)`.  Divisors of 10:
`{1, 2, 5, 10}`; only `1 ≡ 1 (mod 11)` (the others are `2, 5, 10`
mod 11, all ≠ 1).  Hence `n₁₁ = 1` and Sylow 11 is normal.

This is the key 3-prime case dispatch:  combined with Sylow 5 (which
normalizes Sylow 11), we get a Hall `{5, 11}`-subgroup of order 55.
**No Philip Hall theorem is needed.** -/
theorem thm7_card_110_sylow11_count_one
    (n11 : ℕ) (h_dvd : n11 ∣ 10) (h_mod : n11 % 11 = 1) :
    n11 = 1 := by
  have h_le : n11 ≤ 10 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n11 <;> omega

/-- **Theorem 7 Sylow arithmetic for `|G| = 50 = 2·5²`: `n₅ = 1`**. [done] -/
theorem thm7_card_50_sylow5_count_one
    (n5 : ℕ) (h_dvd : n5 ∣ 2) (h_mod : n5 % 5 = 1) :
    n5 = 1 := by
  have h_le : n5 ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n5 <;> omega

/-- **Theorem 7 Sylow arithmetic for `|G| = 54 = 2·3³`: `n₃ = 1`**. [done] -/
theorem thm7_card_54_sylow3_count_one
    (n3 : ℕ) (h_dvd : n3 ∣ 2) (h_mod : n3 % 3 = 1) :
    n3 = 1 := by
  have h_le : n3 ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n3 <;> omega

/-- **Theorem 7 Sylow arithmetic for `|G| = 14 = 2·7`: `n₇ = 1`**. [done] -/
theorem thm7_card_14_sylow7_count_one
    (n7 : ℕ) (h_dvd : n7 ∣ 2) (h_mod : n7 % 7 = 1) :
    n7 = 1 := by
  have h_le : n7 ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n7 <;> omega

/-- **Theorem 7 Sylow arithmetic for `|G| = 22 = 2·11`: `n₁₁ = 1`**. [done] -/
theorem thm7_card_22_sylow11_count_one
    (n11 : ℕ) (h_dvd : n11 ∣ 2) (h_mod : n11 % 11 = 1) :
    n11 = 1 := by
  have h_le : n11 ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n11 <;> omega

/-- **Theorem 7 Sylow arithmetic for `|G| = 38 = 2·19`: `n₁₉ = 1`**. [done] -/
theorem thm7_card_38_sylow19_count_one
    (n19 : ℕ) (h_dvd : n19 ∣ 2) (h_mod : n19 % 19 = 1) :
    n19 = 1 := by
  have h_le : n19 ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
  interval_cases n19 <;> omega

/-- **Theorem 7 unified Sylow dispatch (`q` Sylow normal for each even
candidate order)**.  [done]

For each `(|G|, q)` pair in the even-order Thm 7 list with `q` the
"largest" prime, `n_q = 1` forced by Sylow + mod arithmetic.  This
provides the Feit–Thompson-free dispatch: each even-order candidate
has a unique (hence normal) Sylow q-subgroup.

| `|G|` | factorization | normalised prime |
|-------|---------------|------------------|
| 110   | 2·5·11        | q = 11           |
| 50    | 2·5²          | q = 5            |
| 54    | 2·3³          | q = 3            |
| 14    | 2·7           | q = 7            |
| 22    | 2·11          | q = 11           |
| 38    | 2·19          | q = 19           | -/
theorem thm7_sylow_q_count_one_dispatch
    (q n_q : ℕ)
    (h_dvd_mod :
      (q = 11 ∧ n_q ∣ 10 ∧ n_q % 11 = 1) ∨
      (q = 5  ∧ n_q ∣ 2  ∧ n_q % 5  = 1) ∨
      (q = 3  ∧ n_q ∣ 2  ∧ n_q % 3  = 1) ∨
      (q = 7  ∧ n_q ∣ 2  ∧ n_q % 7  = 1) ∨
      (q = 19 ∧ n_q ∣ 2  ∧ n_q % 19 = 1)) :
    n_q = 1 := by
  rcases h_dvd_mod with ⟨_, hd, hm⟩ | ⟨_, hd, hm⟩ | ⟨_, hd, hm⟩ |
                       ⟨_, hd, hm⟩ | ⟨_, hd, hm⟩
  · exact thm7_card_110_sylow11_count_one n_q hd hm
  · exact thm7_card_50_sylow5_count_one n_q hd hm
  · exact thm7_card_54_sylow3_count_one n_q hd hm
  · exact thm7_card_14_sylow7_count_one n_q hd hm
  · exact thm7_card_38_sylow19_count_one n_q hd hm

/-- **Theorem 7 Sylow-level: Sylow q is normal for each even-order candidate**.
[done]

Mathlib lifts of `thm7_card_*_sylow*_count_one`. For each candidate
even order, the Sylow subgroup of the "large prime" q is normal. -/
theorem thm7_card_110_sylow11_normal
    (G : Type*) [Group G] [Finite G] [Fact (Nat.Prime 11)]
    (h_dvd : Nat.card (Sylow 11 G) ∣ 10)
    (P : Sylow 11 G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 11 G) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 11 G) = 1 := by
      refine thm7_card_110_sylow11_count_one (Nat.card (Sylow 11 G)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 11 G
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

/-- **Theorem 7 Sylow-level: `Sylow 5 G` normal for `|G| = 50 = 2·5²`**.
[done] -/
theorem thm7_card_50_sylow5_normal
    (G : Type*) [Group G] [Finite G] [Fact (Nat.Prime 5)]
    (h_dvd : Nat.card (Sylow 5 G) ∣ 2)
    (P : Sylow 5 G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 5 G) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 5 G) = 1 := by
      refine thm7_card_50_sylow5_count_one (Nat.card (Sylow 5 G)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 5 G
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

/-- **Theorem 7 Sylow-level: `Sylow 3 G` normal for `|G| = 54 = 2·3³`**.
[done] -/
theorem thm7_card_54_sylow3_normal
    (G : Type*) [Group G] [Finite G] [Fact (Nat.Prime 3)]
    (h_dvd : Nat.card (Sylow 3 G) ∣ 2)
    (P : Sylow 3 G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 3 G) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 3 G) = 1 := by
      refine thm7_card_54_sylow3_count_one (Nat.card (Sylow 3 G)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 3 G
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

/-- **Theorem 7 Sylow-level: `Sylow 7 G` normal for `|G| = 14 = 2·7`**. [done] -/
theorem thm7_card_14_sylow7_normal
    (G : Type*) [Group G] [Finite G] [Fact (Nat.Prime 7)]
    (h_dvd : Nat.card (Sylow 7 G) ∣ 2)
    (P : Sylow 7 G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 7 G) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 7 G) = 1 := by
      refine thm7_card_14_sylow7_count_one (Nat.card (Sylow 7 G)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 7 G
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

/-- **Theorem 7 Sylow-level: `Sylow 11 G` normal for `|G| = 22 = 2·11`**.
[done] -/
theorem thm7_card_22_sylow11_normal
    (G : Type*) [Group G] [Finite G] [Fact (Nat.Prime 11)]
    (h_dvd : Nat.card (Sylow 11 G) ∣ 2)
    (P : Sylow 11 G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 11 G) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 11 G) = 1 := by
      refine thm7_card_22_sylow11_count_one (Nat.card (Sylow 11 G)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 11 G
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

/-- **Theorem 7 Sylow-level: `Sylow 19 G` normal for `|G| = 38 = 2·19`**.
[done] -/
theorem thm7_card_38_sylow19_normal
    (G : Type*) [Group G] [Finite G] [Fact (Nat.Prime 19)]
    (h_dvd : Nat.card (Sylow 19 G) ∣ 2)
    (P : Sylow 19 G) :
    (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 19 G) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    have h_count : Nat.card (Sylow 19 G) = 1 := by
      refine thm7_card_38_sylow19_count_one (Nat.card (Sylow 19 G)) h_dvd ?_
      have h_mod := card_sylow_modEq_one 19 G
      unfold Nat.ModEq at h_mod; simpa using h_mod
    exact h_count.le
  exact Sylow.normal_of_subsingleton P

/-- **Theorem 7 (paper-faithful conditional dispatch).** [done]

Proper-signature paper-faithful packaging: given the odd-part dispatch
(`m ∈ divisors of {55, 25, 27, 7, 11, 19}`) as input, conclude
`|G| ∈ divisors of {110, 50, 54, 14, 22, 38}` and `|G| ≤ 110`.

The geometric content (Thm 2 Makhnev-Paduchikh + Thm 5 + Lems 12/15)
is deferred-heavy. -/
theorem thm7_even_order_paper
    (n m : ℕ) (h_n : n = 2 * m)
    (h_m : m ∣ 55 ∨ m ∣ 25 ∨ m ∣ 27 ∨ m ∣ 7 ∨ m ∣ 11 ∨ m ∣ 19) :
    (n ∣ 110 ∨ n ∣ 50 ∨ n ∣ 54 ∨ n ∣ 14 ∨ n ∣ 22 ∨ n ∣ 38) ∧
    n ≤ 110 :=
  ⟨thm7_dvd_one_of_six_from_odd_part n m h_n h_m,
   thm7_bound_110_from_odd_part n m h_n h_m⟩

/-- **Theorem 7 (even `|Aut(Γ)|` divides one of six values).** [deferred-heavy]

Arithmetic conclusion is captured by
`thm7_dvd_one_of_six_from_odd_part` and `thm7_bound_110_from_odd_part`
and combined in `thm7_even_order_paper` (above).
The Feit–Thompson-free Sylow dispatch is captured by the
`thm7_card_*_sylow*_count_one` lemmas and unified in
`thm7_sylow_q_count_one_dispatch`.

What remains for the unconditional form is the paper's dispatch:
Thm 2 (Makhnev–Paduchikh) gives `G = ⟨Y, t⟩ × X` with `t` involution;
Thm 5 + Lems 12/15 constrain the odd part `m = |G|/2`. -/
theorem thm7_even_order (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
