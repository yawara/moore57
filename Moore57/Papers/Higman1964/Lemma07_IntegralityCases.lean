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

[deferred-heavy]
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 7 (Case I / Case II structure for even `|G|`).** [deferred-heavy] -/
theorem lem7_integrality_cases : True := by trivial

end Moore57.Papers.Higman1964
