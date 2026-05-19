import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Higman 1964, Lemma 2 (§2, Intersection numbers)

> Assume `G` is a transitive rank-3 group on `Ω`. For `a ∈ Ω`, write
> the three `G_a`-orbits as `{a}, Δ(a), Γ(a)` with `k = |Δ(a)|`,
> `l = |Γ(a)|`, `n = 1 + k + l`. Then the intersection numbers
>
> | `b ∈ Δ(a)`            | `b ∈ Γ(a)`            |
> |-----------------------|-----------------------|
> | `|Δ(a) ∩ Δ(b)| = λ`  | `|Δ(a) ∩ Δ(b)| = μ`  |
> | `|Γ(a) ∩ Γ(b)| = μ₁` | `|Γ(a) ∩ Γ(b)| = λ₁` |
>
> are independent of the particular `a, b` (depending only on whether
> `b ∈ Δ(a)` or `b ∈ Γ(a)`), and satisfy
>
> * `λ₁ = l − k + μ − 1`,
> * `μ₁ = l − k + λ + 1`.

These are the standard rank-3 association-scheme parameters. The
formalisation needs `MulAction G Ω` set up and the rank-3 hypothesis.
[deferred-heavy]
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 2 (intersection numbers `λ, μ`).** [deferred-heavy] -/
theorem lem2_intersection_numbers : True := by trivial

end Moore57.Papers.Higman1964
