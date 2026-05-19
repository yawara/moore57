import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma16_PGroupFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 17 [skeleton]

> Let `X` be an automorphism group of Γ of order `3^k`. Then one of the
> following holds:
>
> (1) `Fix(X)` is the Petersen graph and `|X|` divides `27`;
>
> (2) `Fix(X)` is a singleton and `|X|` divides `81`.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 17 (3-group fix is Petersen or singleton).** [skeleton] -/
theorem lem17_3group_fix (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
