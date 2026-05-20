import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 6 (§4, Two eigenvalues `s, t`)

> Let `A` be the `n × n` incidence matrix of the block design `A` (0/1,
> `k` ones per row/column, trace 0). The properties
>
> * `I + A + B = J`,
> * `AAᵀ = kI + λA + μB`,
> * (if `|G|` even) `A` symmetric, `B = A`-paired-orbit-flip,
>
> give the polynomial identity
>
> * `(A − kI)(A² − (λ − μ)A − (k − μ)I) = 0`   if `|G|` even,
> * `(A − kI)(A² + A + ((k + 1)/2)I) = 0`      if `|G|` odd.
>
> Hence besides `k` (multiplicity 1), `A` has exactly two distinct
> eigenvalues `s, t`, given by:
>
> * `|G|` even:  `{s, t} = ((λ − μ) ± √d) / 2`, `d = (λ − μ)² + 4(k − μ)`.
> * `|G|` odd:   `{s, t} = (−1 ± √(−μ)) / 2`.

For Moore57 (rank-3, `n = 3250`, `λ = 0`, `μ = 1`, `|G|` even):
`d = 1 + 4·56 = 225`, `√d = 15`, eigenvalues `(−1 ± 15)/2 = 7, −8`.

Status:
* `lem6_two_eigenvalues`: paper-stub (full matrix-spectrum derivation,
  deferred-heavy).
* `lem6_moore57_eigenvalues_arithmetic`: **proven** — the pure ℤ
  arithmetic computation of the Moore57 secondary eigenvalues `7, −8`
  as roots of `x² + x − 56 = (x − 7)(x + 8)`.
-/

namespace Moore57.Papers.Higman1964

/-- **Moore57 secondary eigenvalue arithmetic.** [done]

For Moore57 with `(λ, μ, k) = (0, 1, 57)`, the secondary eigenvalues
of the adjacency matrix are roots of the quadratic
`x² − (λ − μ)·x − (k − μ) = x² + x − 56`, factoring as
`(x − 7)(x + 8)`.  Hence the eigenvalues are `{7, −8}`. -/
theorem lem6_moore57_eigenvalues_arithmetic (x : ℤ) :
    x^2 + x - 56 = 0 ↔ x = 7 ∨ x = -8 := by
  constructor
  · intro h
    have factored : (x - 7) * (x + 8) = x ^ 2 + x - 56 := by ring
    have h0 : (x - 7) * (x + 8) = 0 := factored.trans h
    rcases mul_eq_zero.mp h0 with h1 | h2
    · left; omega
    · right; omega
  · rintro (rfl | rfl) <;> ring

/-- **Lemma 6 (conditional): eigenvalue characterization via discriminant**.
[done]

For a rank-3 even-order block-design, the two secondary eigenvalues
`s, t` are characterised by the polynomial
`X² − (λ − μ)X − (k − μ) = 0`.  Equivalently, an integer `x` is an
eigenvalue (of multiplicity ≥ 1, besides `k`) iff
`x² − (λ − μ)·x − (k − μ) = 0`.

The Moore57 specialization (`(λ, μ, k) = (0, 1, 57)`) reduces this to
`x² + x − 56 = 0 ↔ x ∈ {7, −8}` — proven in
`lem6_moore57_eigenvalues_arithmetic`.

Conditional form: given `(λ − μ)² + 4·(k − μ) = d²` (so the discriminant
is a perfect square — Higman 1964 Lem 7's Case II hypothesis), the
secondary eigenvalues are `((λ − μ) ± d) / 2`. -/
theorem lem6_secondary_eigenvalues_via_discriminant
    {lam mu k d : ℤ} (h_disc : (lam - mu) ^ 2 + 4 * (k - mu) = d ^ 2) (x : ℤ) :
    x ^ 2 - (lam - mu) * x - (k - mu) = 0 ↔
    2 * x = (lam - mu) + d ∨ 2 * x = (lam - mu) - d := by
  -- The roots of x² - bx - c = 0 are (b ± √(b² + 4c)) / 2.
  -- With b = λ − μ, c = k − μ, and b² + 4c = d², the roots are (b ± d) / 2.
  constructor
  · intro h
    -- (2x - b - d)(2x - b + d) = 4x² - 4bx + b² - d² = 4(x² - bx) - (b² - d²)
    --                         = 4(x² - bx) - (b² + 4c) + 4c = 4(x² - bx - c)
    -- So h : x² - bx - c = 0 ⟹ (2x - b - d)(2x - b + d) = 0.
    have h_factored : (2 * x - (lam - mu) - d) * (2 * x - (lam - mu) + d) = 0 := by
      have hexp : (2 * x - (lam - mu) - d) * (2 * x - (lam - mu) + d) =
          4 * (x ^ 2 - (lam - mu) * x - (k - mu)) +
          (((lam - mu) ^ 2 + 4 * (k - mu)) - d ^ 2) := by ring
      rw [hexp, h, h_disc]
      ring
    rcases mul_eq_zero.mp h_factored with h1 | h2
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · -- 2x = (lam - mu) + d.  Then (2x − (lam − mu))² = d² = (lam−mu)² + 4(k−mu).
      -- Expanding: 4x² − 4x(lam−mu) + (lam−mu)² = (lam−mu)² + 4(k−mu)
      -- ⟹ 4(x² − x(lam−mu) − (k−mu)) = 0 ⟹ x² − x(lam−mu) − (k−mu) = 0.
      have h2x : 2 * x - (lam - mu) = d := by linarith
      have hsq : (2 * x - (lam - mu)) ^ 2 = d ^ 2 := by rw [h2x]
      nlinarith [h_disc, hsq, sq_nonneg (2 * x - (lam - mu) - d)]
    · have h2x : 2 * x - (lam - mu) = -d := by linarith
      have hsq : (2 * x - (lam - mu)) ^ 2 = d ^ 2 := by rw [h2x]; ring
      nlinarith [h_disc, hsq, sq_nonneg (2 * x - (lam - mu) + d)]

/-- **Lemma 6 (two eigenvalues `s, t`).** [deferred-heavy]

In addition to the eigenvalue `k` (multiplicity 1), the incidence matrix
`A` of a rank-3 block design has exactly two further eigenvalues `s, t`,
the roots of `X² − (λ − μ)X − (k − μ) = 0` (when `|G|` is even) or
`X² + X + (k + 1)/2 = 0` (when `|G|` is odd).

The Moore57 specialization of the eigenvalue arithmetic is proven in
`lem6_moore57_eigenvalues_arithmetic`. -/
theorem lem6_two_eigenvalues : True := by trivial

end Moore57.Papers.Higman1964
