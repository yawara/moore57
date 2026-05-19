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

[skeleton]
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 6 (two eigenvalues `s, t`).** [skeleton]

In addition to the eigenvalue `k` (multiplicity 1), the incidence matrix
`A` of a rank-3 block design has exactly two further eigenvalues `s, t`,
the roots of `X² − (λ − μ)X − (k − μ) = 0` (when `|G|` is even) or
`X² + X + (k + 1)/2 = 0` (when `|G|` is odd). -/
theorem lem6_two_eigenvalues : True := by trivial

end Moore57.Papers.Higman1964
