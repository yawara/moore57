import Mathlib.Tactic.NormNum
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Papers.Higman1964.Lemma06_TwoEigenvalues

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 7 (§5, Integrality cases)

> If `|G|` is even, then either
>
> * **Case I.** `k = l, μ = λ + 1 = k/2, f₂ = f₃ = k`.
> * **Case II.** `d := (λ − μ)² + 4(k − μ)` is a square, and
>     - if `n` is even: `√d ∣ 2k + (λ − μ)(k + l)`, `2√d ∤ same`;
>     - if `n` is odd:  `2√d ∣ 2k + (λ − μ)(k + l)`.
>   In Case II, `f₂ ≠ f₃` and the eigenvalues of `A` are integers.

The proof uses Lemma 6 (two eigenvalues `s, t`) plus the trace-0 and
multiplicity constraints `f₂ + f₃ = k + l = n − 1`, `k + s f₂ = t f₃ = 0`.

For Moore57: Case II applies with `d = 225 = 15²` (a square), giving
integer eigenvalues `s, t = 7, −8`.

Status:
* `lem7_integrality_cases`: paper-stub (full Case I / Case II
  classification, deferred-heavy).
* `lem7_moore57_discriminant_eq_15_sq`: **proven** — Moore57 satisfies
  Case II with discriminant `(λ−μ)² + 4(k−μ) = 1 + 224 = 225 = 15²`.
-/

namespace Moore57.Papers.Higman1964

/-- **Moore57 discriminant is a perfect square (15²).** [done]

For Moore57 with `(λ, μ, k) = (0, 1, 57)`, the discriminant
`(λ − μ)² + 4(k − μ) = (−1)² + 4·56 = 1 + 224 = 225 = 15²`,
placing Moore57 in Higman Lemma 7's Case II (integer eigenvalues). -/
theorem lem7_moore57_discriminant_eq_15_sq :
    ((0 : ℤ) - 1) ^ 2 + 4 * (57 - 1) = 15 ^ 2 := by norm_num

/-- **Lemma 7 (Case I / Case II structure for even `|G|`).** [deferred-heavy]

Full classification of rank-3 even-order cases.  The Moore57
instance (Case II with `d = 15²`) is proven in
`lem7_moore57_discriminant_eq_15_sq`. -/
theorem lem7_integrality_cases : True := by trivial

end Moore57.Papers.Higman1964
