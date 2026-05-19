import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 19 [skeleton]

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

/-- **Lemma 19 (large-prime `p`-group classification).** [skeleton] -/
theorem lem19_large_prime_pgroup (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
