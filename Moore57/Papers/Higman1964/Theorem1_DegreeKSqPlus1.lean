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

/-- **Theorem 1 Case I arithmetic core** (`k = l, n = k² + 1`, rank-3
forces `k² = 2k`).

In Case I of Higman §6, `λ + 1 = μ = k/2`, so the rank-3 identity
`μ·l = k·(k − λ − 1)` collapses to `l = k`.  Combined with `n = k² + 1`
and `n = 1 + k + l = 1 + 2k`, we get `k² + 1 = 1 + 2k`, i.e.
`k² = 2k`, hence `k ∈ {0, 2}`.  The non-degenerate solution `k = 2`
gives `n = 5`.

This arithmetic core packages the pure ℕ identity:
`k * k + 1 = 1 + 2 * k ⟹ k = 0 ∨ k = 2`. -/
theorem theorem1_case1_arithmetic_core {k : ℕ}
    (h : k * k + 1 = 1 + 2 * k) :
    k = 0 ∨ k = 2 := by
  have h_eq : k * k = 2 * k := by omega
  -- Bound k: if k ≥ 3, then k*k ≥ 3*k > 2*k, contradiction.
  have hk_le : k ≤ 2 := by
    by_contra h_lt
    have hk_ge_3 : 3 ≤ k := Nat.lt_of_not_le h_lt
    have h_ge : 3 * k ≤ k * k := Nat.mul_le_mul_right k hk_ge_3
    -- Substitute h_eq into h_ge to get linear: 3*k ≤ 2*k.
    rw [h_eq] at h_ge
    omega
  interval_cases k
  · left; rfl
  · simp at h
  · right; rfl

/-- **Theorem 1 full arithmetic conclusion** (combining Case I and Case II).

Given that one of the following holds:
* Case I: `n = k² + 1 = 1 + 2k` (so `k = 0` or `k = 2`); or
* Case II: `4k = e² + 3` and `e² ∣ 225` (so `k ∈ {1, 3, 7, 57}`),

then `k ∈ {0, 1, 2, 3, 7, 57}`.  Combined with the non-degeneracy
condition `k ≥ 2` (a transitive rank-3 group has subdegrees ≥ 2), this
yields the four valences `k ∈ {2, 3, 7, 57}` of Higman's classification.

Convenience packaging for downstream Moore57 instantiations (`k = 57`). -/
theorem theorem1_combined_arithmetic_core {k : ℕ}
    (h : (k * k + 1 = 1 + 2 * k) ∨
         (∃ e : ℕ, 4 * k = e * e + 3 ∧ e * e ∣ 225)) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by
  rcases h with h1 | ⟨e, he, hdvd⟩
  · rcases theorem1_case1_arithmetic_core h1 with h | h
    · left; exact h
    · right; right; left; exact h
  · rcases theorem1_arithmetic_core he hdvd with h | h | h | h
    · right; left; exact h
    · right; right; right; left; exact h
    · right; right; right; right; left; exact h
    · right; right; right; right; right; exact h

/-! ### Thm 1 bridge: `e ∣ k(k-2) ∧ e² = 4k - 3 ⟹ e ∣ 15` (D3.6 backbone)

The arithmetic bridge between Lemma 7's Moore-parameter integrality
constraint `e ∣ k(k − 2)` (proven in `Lemma07.lem7_moore_e_dvd_k_times_k_minus_2`)
and the Theorem 1 arithmetic core's hypothesis `e² ∣ 225`.

Key calculation: from `e² = 4k − 3`,
`16 · k(k − 2) = (4k)² − 8 · (4k) = (e² + 3)² − 8(e² + 3) = e⁴ − 2e² − 15`,
so `e ∣ k(k − 2)` (any `ℤ`-multiple of `e`) implies `e ∣ e⁴ − 2e² − 15`,
hence `e ∣ 15` (since `e ∣ e⁴` and `e ∣ 2e²`).

Then `e ∣ 15 ⟹ e² ∣ 225` by `mul_dvd_mul`. -/

/-- **Thm 1 bridge: from `e ∣ k(k−2)` and `e² = 4k − 3`, deduce `e ∣ 15`**.
[done]

Proof: multiply `e ∣ k(k − 2)` by 16 to get `e ∣ 16k(k − 2)`.  Substitute
`4k = e² + 3` to rewrite the RHS as `e⁴ − 2e² − 15`.  Then `e ∣ e⁴` and
`e ∣ 2e²`, so `e ∣ (e⁴ − 2e² − 15) − (e⁴ − 2e²) = −15`, hence `e ∣ 15`. -/
theorem theorem1_e_dvd_fifteen
    {e k : ℤ} (h_dvd : e ∣ k * (k - 2)) (h_sq : e ^ 2 = 4 * k - 3) :
    e ∣ 15 := by
  -- e ∣ 16 * (k * (k - 2)).
  have h_16 : e ∣ 16 * (k * (k - 2)) := h_dvd.mul_left 16
  -- Substitute 4 * k = e^2 + 3 (from h_sq) to rewrite RHS algebraically.
  have h_4k : 4 * k = e ^ 2 + 3 := by linarith
  have h_eq : 16 * (k * (k - 2)) = e ^ 4 - 2 * e ^ 2 - 15 := by
    have h_calc : 16 * (k * (k - 2)) = (4 * k) ^ 2 - 8 * (4 * k) := by ring
    rw [h_calc, h_4k]; ring
  rw [h_eq] at h_16
  -- e ∣ e^4 - 2 * e^2 (since e ∣ e^4 and e ∣ 2 * e^2).
  have h_e_sq : e ∣ e ^ 4 - 2 * e ^ 2 := by
    refine ⟨e ^ 3 - 2 * e, ?_⟩; ring
  -- Subtract to get e ∣ -15.
  have h_neg15 : e ∣ (-15 : ℤ) := by
    have h_diff : (-15 : ℤ) = (e ^ 4 - 2 * e ^ 2 - 15) - (e ^ 4 - 2 * e ^ 2) := by
      ring
    rw [h_diff]
    exact h_16.sub h_e_sq
  exact (dvd_neg.mp h_neg15)

/-- **Thm 1 bridge: `e ∣ 15 ⟹ e² ∣ 225`** (ℤ form). [done]

Trivial multiplicative consequence: `e ∣ 15` ⟹ `e * e ∣ 15 * 15 = 225`. -/
theorem theorem1_e_sq_dvd_225_of_e_dvd_fifteen
    {e : ℤ} (h : e ∣ 15) : e * e ∣ 225 := by
  have h1 : e * e ∣ 15 * 15 := mul_dvd_mul h h
  norm_num at h1; exact h1

/-- **Thm 1 bridge (combined): `e ∣ k(k−2) ∧ e² = 4k − 3 ⟹ e² ∣ 225`**.
[done]

Composition of `theorem1_e_dvd_fifteen` and
`theorem1_e_sq_dvd_225_of_e_dvd_fifteen`. -/
theorem theorem1_e_sq_dvd_225_of_dvd_and_sq
    {e k : ℤ} (h_dvd : e ∣ k * (k - 2)) (h_sq : e ^ 2 = 4 * k - 3) :
    e * e ∣ 225 :=
  theorem1_e_sq_dvd_225_of_e_dvd_fifteen
    (theorem1_e_dvd_fifteen h_dvd h_sq)

/-- **Thm 1 bridge (ℤ → ℕ): if `k ≥ 1` and `e ≥ 1` in ℕ satisfy
`e * e ∣ 225` and `4 * k = e * e + 3`, then `k ∈ {1, 3, 7, 57}`**.
[done]

This is the ℕ wrap of `theorem1_arithmetic_core` taking direct
`e * e ∣ 225` form (rather than splitting into the e-divisor cases). -/
theorem theorem1_k_in_set_of_e_sq_dvd_225 {k e : ℕ}
    (he : 4 * k = e * e + 3) (hdvd : e * e ∣ 225) :
    k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 57 :=
  theorem1_arithmetic_core he hdvd

/-! ### Thm 1 full chain (conditional) -/

/-- **Theorem 1 full (Case II, conditional)**: under Moore SRG parameters
(`λ = 0`, `μ = 1`, `n = k² + 1`) with Case II hypotheses
(`e² = 4k − 3` perfect square, integer multiplicity condition
`2 e f₂ = k(k(e + 1) − 2)`), we have `k ∈ {1, 3, 7, 57}` (ℕ form,
assuming `e : ℕ` and the perfect-square equation in ℕ).

The conditional inputs are:
* `e * e = 4 * k - 3` (perfect square discriminant in ℕ — Case II
  Lem 7 hypothesis).
* `e * f₂ * 2 = k * (k * (e + 1) - 2)` (integer multiplicity, ℕ form
  — Lem 7 multiplicity constraint specialised to Moore parameters).

The Moore57 instance (`k = 57, e = 15`) is `theorem1_moore57_degree`
+ `theorem1_moore57_valence`. -/
theorem theorem1_case_two_full_conditional {k e : ℕ} {f₂ : ℤ}
    (he_sq : 4 * k = e * e + 3)
    (h_mult_Z : 2 * ((e : ℤ) * f₂) =
                (k : ℤ) * ((k : ℤ) * ((e : ℤ) + 1) - 2))
    (h_k_ge_2 : 2 ≤ k) :
    k = 3 ∨ k = 7 ∨ k = 57 := by
  -- Lift to ℤ and use the bridge.
  have h_dvd_kk2 : (e : ℤ) ∣ (k : ℤ) * ((k : ℤ) - 2) := by
    refine ⟨(2 : ℤ) * f₂ - (k : ℤ) ^ 2, ?_⟩
    linarith
  have h_sq_Z : (e : ℤ) ^ 2 = 4 * (k : ℤ) - 3 := by
    have := congrArg (Nat.cast (R := ℤ)) he_sq
    push_cast at this; linarith
  have h_e_sq_dvd : (e : ℤ) * (e : ℤ) ∣ 225 :=
    theorem1_e_sq_dvd_225_of_dvd_and_sq h_dvd_kk2 h_sq_Z
  have h_e_sq_dvd_N : e * e ∣ 225 := by
    have h_e_sq_Z : ((e * e : ℕ) : ℤ) = (e : ℤ) * (e : ℤ) := by push_cast; ring
    have : ((e * e : ℕ) : ℤ) ∣ (225 : ℤ) := h_e_sq_Z ▸ h_e_sq_dvd
    exact_mod_cast this
  rcases theorem1_arithmetic_core he_sq h_e_sq_dvd_N with h | h | h | h
  · omega
  · left; exact h
  · right; left; exact h
  · right; right; exact h

/-- **Theorem 1 (Higman §6, full statement).** [deferred-heavy]

A transitive rank-3 permutation group of degree `n = k² + 1` (where `k`
is the length of a `G_a`-orbit) has `n ∈ {5, 10, 50, 3250}`, equivalently
`k ∈ {2, 3, 7, 57}`.

The full arithmetic chain (Case I + Case II + bridge to multiplicities)
is formalised:
* Case I core: `theorem1_case1_arithmetic_core` (`k = 0 ∨ k = 2`).
* Case II arithmetic core: `theorem1_arithmetic_core` (`k ∈ {1, 3, 7, 57}`).
* Multiplicity / discriminant bridge: `theorem1_e_dvd_fifteen` +
  `theorem1_e_sq_dvd_225_of_dvd_and_sq`.
* Case II full conditional (Moore parameters): `theorem1_case_two_full_conditional`.

The full "k = 0/1 excluded by non-degeneracy" packaging and Case I/II
disjunction at the rank-3 level remain external (require the
permutation-group / incidence-matrix infrastructure). -/
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
