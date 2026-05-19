import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 18 [deferred-heavy]

> Let `X` be a group of automorphisms of Γ such that `|X|` is a 5-group.
> Then one of the following holds:
>
> (1) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `25`;
>
> (2) `Fix(X)` is a pentagon and `|X|` divides `125`;
>
> (3) `Fix(X)` is empty and `|X|` divides `5⁶`.

This is the only lemma in §6 whose full proof the authors include
(orbit counting around `Fix(a)` for `a ∈ Fix(X)`).
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 18 (5-group fix shape and order bound).** [deferred-heavy] -/
theorem lem18_5group_fix (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
