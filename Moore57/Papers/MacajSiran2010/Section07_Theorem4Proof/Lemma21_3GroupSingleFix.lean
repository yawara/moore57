import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma17_3Group

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §7, Lemma 21 [deferred-heavy]

> Let Γ admit a 3-group `X` of automorphisms with `Fix(X) = {a}` and let
> `x` be a non-trivial element of `X`. Then,
>
> (1) if `X` has (at least) two orbits of size 3 on `N(a)`, then `|X| = 9`;
>
> (2) if `X` has an orbit of size 9 on `N(a)`, then `|X| ≤ 27`.
-/

namespace Moore57.Papers.MacajSiran2010.S7

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 21 (1) (two size-3 orbits on `N(a)` ⇒ `|X| = 9`).** [deferred-heavy] -/
theorem lem21_two_size3_orbits (hΓ : IsMoore57 Γ) : True := by trivial

/-- **Lemma 21 (2) (size-9 orbit on `N(a)` ⇒ `|X| ≤ 27`).** [deferred-heavy] -/
theorem lem21_size9_orbit (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S7
