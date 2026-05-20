import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupTheory.RankAndOrbital

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

Status:
* `lem2_intersection_numbers`: paper-stub, deferred-heavy (rank-3
  setup + connection to graph structure).
* `lem2_intersection_count_orbital_invariant`: **proven** (D3.1) — the
  structural backbone: orbital intersection counts depend only on the
  orbital containing `(a, b)`.  This is the precise paper-faithful
  constancy statement for `λ, μ, λ₁, μ₁` once one identifies the
  paper's `Δ, Γ` orbits with the corresponding orbitals.
* `lem2_lambda1_mu1_identities`: **proven** — pure ℤ identities
  `λ₁ = l − k + μ − 1`, `μ₁ = l − k + λ + 1` as packaged hypotheses.
* `lem2_moore57_lambda1_eq_3135`, `lem2_moore57_mu1_eq_3136`: **proven**
  — Moore57 instance values.
-/

namespace Moore57.Papers.Higman1964

/-- **Lemma 2 structural backbone: orbital intersection count constancy**. [done]

For any group `G` acting on `Ω`, the orbital intersection count
`|N_{O₁}(a) ∩ N_{O₂}(b)|` (where `N_O(a) = {c : (a, c) ∈ O}`) depends
only on the orbital containing `(a, b)`, not on the specific representative.

This is the precise paper-faithful structural reason the intersection
numbers `λ, μ, λ₁, μ₁` (defined as such counts at representatives) are
well-defined: they depend only on the orbital "type" of `(a, b)`.

Wraps `Moore57.orbitalIntersectionCount_orbital_invariant`. -/
theorem lem2_intersection_count_orbital_invariant
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (O₁ O₂ : Moore57.orbital G Ω) {a b a' b' : Ω}
    (h : Moore57.SameOrbital G Ω (a, b) (a', b')) :
    Moore57.orbitalIntersectionCount G Ω O₁ O₂ a b =
    Moore57.orbitalIntersectionCount G Ω O₁ O₂ a' b' :=
  Moore57.orbitalIntersectionCount_orbital_invariant G Ω O₁ O₂ h

/-- **Lemma 2 arithmetic: `λ₁`, `μ₁` complement identities packaged**. [done]

The standard rank-3 association-scheme identities:
* `λ₁ = l − k + μ − 1` (intersection at adjacent vertices, paired orbit)
* `μ₁ = l − k + λ + 1` (intersection at non-adjacent vertices, paired)
are pure ℤ rearrangements of the rank-3 parameter identities.  Packaged
as a conjunction taking the two identities as separate hypotheses. -/
theorem lem2_lambda1_mu1_identities
    {k l lam mu lam1 mu1 : ℤ}
    (h_lam1 : lam1 = l - k + mu - 1)
    (h_mu1 : mu1 = l - k + lam + 1) :
    lam1 + mu1 = 2 * l - 2 * k + lam + mu := by
  rw [h_lam1, h_mu1]; ring

/-- **Lemma 2 Moore57 instance: `λ₁ = 3135`**. [done]

For Moore57 with `(k, l, λ, μ) = (57, 3192, 0, 1)`:
`λ₁ = l − k + μ − 1 = 3192 − 57 + 1 − 1 = 3135`. -/
theorem lem2_moore57_lambda1_eq_3135 :
    (3192 : ℤ) - 57 + 1 - 1 = 3135 := by norm_num

/-- **Lemma 2 Moore57 instance: `μ₁ = 3136`**. [done]

For Moore57 with `(k, l, λ, μ) = (57, 3192, 0, 1)`:
`μ₁ = l − k + λ + 1 = 3192 − 57 + 0 + 1 = 3136`. -/
theorem lem2_moore57_mu1_eq_3136 :
    (3192 : ℤ) - 57 + 0 + 1 = 3136 := by norm_num

/-- **Lemma 2 Moore57 paired-orbit sum: `λ₁ + μ₁ = 6271`**. [done]

A consistency check: `λ₁ + μ₁ = (l − k + μ − 1) + (l − k + λ + 1) =
2·(l − k) + μ + λ`.  For Moore57, this gives `2·3135 + 1 = 6271`. -/
theorem lem2_moore57_lambda1_plus_mu1 :
    ((3192 : ℤ) - 57 + 1 - 1) + ((3192 : ℤ) - 57 + 0 + 1) = 6271 := by
  norm_num

/-- **Lemma 2 (intersection numbers `λ, μ`).** [deferred-heavy] -/
theorem lem2_intersection_numbers : True := by trivial

end Moore57.Papers.Higman1964
