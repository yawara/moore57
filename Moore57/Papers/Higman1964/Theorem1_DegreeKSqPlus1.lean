import Moore57.Moore57Graph.Moore57Definition
import Moore57.Papers.Higman1964.Lemma05_BlockDesignCount
import Moore57.Papers.Higman1964.Lemma07_IntegralityCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Theorem 1 (§6, Degree `k² + 1`)

> If `G` is a transitive group of rank 3 and degree `n = k² + 1`, where
> `k` is the length of a `G_a`-orbit, then `n ∈ {5, 10, 50, 3250}` —
> equivalently `k ∈ {2, 3, 7, 57}`.

## Proof outline (Higman §6)

* `G` is primitive (Lemma 4) and has `λ = 0`, `μ = 1` (corner of Lemma 5).
* `|G|` is even since one of `k`, `k² + 1` is even.
* Lemma 7 gives two cases:
  - **Case I.** `k = l, μ = λ + 1 = k/2`. From `n = k² + 1` and
    `n = 1 + k + l = 1 + 2k`, get `k² = 2k`, i.e. `k = 2`, `n = 5`.
  - **Case II.** `d = (λ − μ)² + 4(k − μ) = 1 + 4(k − 1) = 4k − 3` is a
    square, `e := √d`, and `e ∣ 2k + (λ − μ)(k + l) = 2k − (k + k(k−1)) = −k(k−2)`.
    Hence `e ∣ k(k − 2)`. From `gcd(4k − 3, k) ∣ 3` and
    `gcd(4k − 3, k − 2) ∣ 5` we get `e² = 4k − 3 ∣ 15² = 225`.
    The square divisors of `225 = 3² · 5²` are `{1, 9, 25, 225}`, giving
    `k ∈ {1, 3, 7, 57}` (and `k = 1` is degenerate).

## What we formalise

The **arithmetic core** — that "`4k − 3 ∈ {1, 9, 25, 225}` ⇒ `k ∈ {1, 3, 7, 57}`"
— is purely number-theoretic and provable here. The setup (rank-3 →
λ = 0, μ = 1 → integrality of `√(4k − 3)` → divisibility of 225) requires
the full rank-3 permutation-representation infrastructure of Lemmas 1–7
and remains as the [deferred-heavy] in `theorem1_n_kSq_plus_one`.

For Moore57: Case II with `k = 57` gives `e = 15`, `e² = 225`, exactly
the `4k − 3 = 225 / k = 57` fork.
-/

namespace Moore57.Papers.Higman1964

/-- **Arithmetic core of Theorem 1** (`4k − 3` is a square divisor of `225`).

If `e² = 4k − 3` (i.e. `4k = e² + 3`) and `e² ∣ 225`, then
`k ∈ {1, 3, 7, 57}`.

This is the pure number-theoretic step of Higman §6: given that
`4k − 3 ∈ {square divisors of 225}`, the candidate values for `k` are
exactly the four listed.

Combined with `k ≥ 1` (the meaningful range), this gives the conclusion
of Higman's Case II. -/
theorem theorem1_arithmetic_core {k e : ℕ}
    (he : 4 * k = e * e + 3) (hdvd : e * e ∣ 225) :
    k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  -- From `e² ∣ 225`, get `e² ≤ 225`, hence `e ≤ 15`.
  have hesq_le : e * e ≤ 225 := Nat.le_of_dvd (by norm_num) hdvd
  have he_le : e ≤ 15 := by
    by_contra h
    have h16 : 16 ≤ e := by omega
    have : 16 * 16 ≤ e * e := Nat.mul_le_mul h16 h16
    omega
  -- Case on `e ∈ {0, …, 15}`. `omega` handles all cases: it knows
  -- `4k = e² + 3` (forcing `k` uniquely or yielding no nat solution) and
  -- recognises `Nat`-divisibility, so `e² ∣ 225` is enough to exclude the
  -- non-divisor values `e ∈ {2, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14}`.
  interval_cases e <;> omega

/-- **Theorem 1 (Higman §6, full statement).** [deferred-heavy]

A transitive rank-3 permutation group of degree `n = k² + 1` (where `k`
is the length of a `G_a`-orbit) has `n ∈ {5, 10, 50, 3250}`, equivalently
`k ∈ {2, 3, 7, 57}`.

The arithmetic core (Case II) is proven in `theorem1_arithmetic_core`;
Case I (`k = l = 2`, `n = 5`) and the full setup (rank-3 hypothesis,
Lemmas 1–7, primitivity, even-order, integrality of `√(4k − 3)`) are
external and remain skeletal until the permutation-group / incidence-
matrix infrastructure is built. -/
theorem theorem1_n_kSq_plus_one : True := by trivial

/-- **Theorem 1, Moore57 instance.**

The Moore57 vertex count `n = 3250 = 57² + 1` is one of the four degrees
in Higman's classification. -/
theorem theorem1_moore57_degree :
    (3250 : ℕ) = 57 ^ 2 + 1 := by norm_num

/-- **Theorem 1, Moore57 valence instance.**

`k = 57` is one of the four valences `{2, 3, 7, 57}` allowed by
Theorem 1. -/
theorem theorem1_moore57_valence :
    (57 : ℕ) = 2 ∨ (57 : ℕ) = 3 ∨ (57 : ℕ) = 7 ∨ (57 : ℕ) = 57 := by
  right; right; right; rfl

end Moore57.Papers.Higman1964
