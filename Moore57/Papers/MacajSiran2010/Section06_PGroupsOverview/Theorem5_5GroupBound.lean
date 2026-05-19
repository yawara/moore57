import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma18_5Group

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Theorem 5 [skeleton]

> Let `X` be a group of automorphisms of Γ of order a power of 5. Then one
> of the following holds:
>
> (1) `Fix(X)` is the Hoffman–Singleton graph and `|X|` divides `5`;
>
> (2) `Fix(X)` is a pentagon and `|X|` divides `25`;
>
> (3) `Fix(X)` is empty and `|X|` divides `125`.

Statement only; the full proof is in `Section08_Theorem5Proof/`.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 5 (5-group order bound).** [skeleton] -/
theorem thm5_5group_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
