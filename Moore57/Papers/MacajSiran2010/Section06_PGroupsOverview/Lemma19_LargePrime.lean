import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 19 [deferred-heavy]

> Let `p > 5` be a prime and let `X` be a group of automorphisms of Γ of
> order `p^k`. Then one of the following holds:
>
> (1) `Fix(X) = ∅` and `X ≅ Z₁₃`;
>
> (2) `Fix(X)` is a singleton and `X ≅ Z₁₉`;
>
> (3) `Fix(X)` is a pentagon and `X ≅ Z₁₁`;
>
> (4) `Fix(X)` is a star on `2 + 7l` vertices and `X ≅ Z₇`;
>
> (5) `Fix(X)` is an edge and `X ≅ Z₇ × Z₇`.

This bounds `p`-groups for `p > 5` very tightly.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 19 case (1) arithmetic core: 13-group with `|X| ∣ 3250` is `Z₁₃`.** [done]

For `p = 13` and `X` a 13-group with `Fix(X) = ∅` (semi-regular on
3250 vertices ⟹ `|X| ∣ 3250`), the only nontrivial possibility is
`|X| = 13` (since `13² = 169` does not divide `3250 = 2·5²·13`). -/
theorem lem19_case1_arithmetic_13group_dvd_3250
    (k : ℕ) (h_dvd : 13 ^ k ∣ 3250) :
    13 ^ k = 1 ∨ 13 ^ k = 13 := by
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    -- 13^2 ∣ 13^k ∣ 3250, but 13^2 = 169 does not divide 3250 = 2·5²·13.
    have h_div : 13 ^ 2 ∣ 3250 := dvd_trans (pow_dvd_pow 13 h2) h_dvd
    revert h_div
    decide
  interval_cases k
  · left; rfl
  · right; rfl

/-- **Lemma 19 case (2) arithmetic core: 19-group with `|X| ∣ 57` is `Z₁₉`.** [done]

For `p = 19` and `X` a 19-group with `|Fix(X)| = 1` (semi-regular on
`N(a) \ {a}` of size 57 ⟹ `|X| ∣ 57 = 3·19`), the only nontrivial
possibility is `|X| = 19` (since `19² = 361` does not divide `57`). -/
theorem lem19_case2_arithmetic_19group_dvd_57
    (k : ℕ) (h_dvd : 19 ^ k ∣ 57) :
    19 ^ k = 1 ∨ 19 ^ k = 19 := by
  have h_le : 19 ^ k ≤ 57 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    have h_ge : 19 ^ 2 ≤ 19 ^ k := Nat.pow_le_pow_right (by norm_num) h2
    omega
  interval_cases k
  · left; rfl
  · right; rfl

/-- **Lemma 19 case (3) arithmetic core: 11-group with `|X| ∣ 55` is `Z₁₁`.** [done]

For `p = 11` and `X` an 11-group with `Fix(X)` a pentagon (semi-regular
on `N(a) \ Fix(X)` of size 55 ⟹ `|X| ∣ 55 = 5·11`), the only nontrivial
possibility is `|X| = 11`. -/
theorem lem19_case3_arithmetic_11group_dvd_55
    (k : ℕ) (h_dvd : 11 ^ k ∣ 55) :
    11 ^ k = 1 ∨ 11 ^ k = 11 := by
  have h_le : 11 ^ k ≤ 55 := Nat.le_of_dvd (by norm_num) h_dvd
  have h_k_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := Nat.lt_of_not_le h
    have h_ge : 11 ^ 2 ≤ 11 ^ k := Nat.pow_le_pow_right (by norm_num) h2
    omega
  interval_cases k
  · left; rfl
  · right; rfl

/-- **Lemma 19 (large-prime `p`-group classification).** [deferred-heavy]

The full 5-case classification.  Arithmetic cores for cases (1), (2),
(3) are proven above; cases (4) and (5) (p=7 star / edge) follow a
similar pattern but with additional structural constraints (the edge
case requires the rank-2 elementary-abelian `Z₇ × Z₇`). -/
theorem lem19_large_prime_pgroup (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
