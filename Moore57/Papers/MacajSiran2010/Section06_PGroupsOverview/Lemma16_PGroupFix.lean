import Moore57.Papers.MacajSiran2010.Section02_StateOfTheArt.Lemma4_OddPrimeFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 16 [skeleton]

> Let `X` be a group of automorphisms of Γ such that `X` is a `p`-group for
> some odd prime `p`. Then one of the following holds:
>
> (1) `Fix(X)` is empty and `p ∈ {5, 13}`;
>
> (2) `Fix(X)` is a singleton and `p ∈ {3, 19}`;
>
> (3) `Fix(X)` is a star with `|Fix(X)| = 2 + 7l` and `p = 7`;
>
> (4) `Fix(X)` is a pentagon and `p ∈ {5, 11}`;
>
> (5) `Fix(X)` is the Petersen graph and `p = 3`;
>
> (6) `Fix(X)` is the Hoffman–Singleton graph and `p = 5`.

This extends Lemma 4 from prime-order to `p`-group order.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 16 (odd-prime `p`-group fix shape).** [skeleton] -/
theorem lem16_pgroup_fix_shape (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
