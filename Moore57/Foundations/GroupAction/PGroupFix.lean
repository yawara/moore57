import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Action.End
import Moore57.Foundations.GroupAction.FixedPoints

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# p-group fixed-point counts

For a finite subgroup `X` of `Equiv.Perm V` (with `V` finite) that is a
`p`-group, the X-action on `V` has the standard mod-`p` constraint on the
fixed-point count:

```
|V| ≡ |Fix(X)| (mod p)
```

This is `IsPGroup.card_modEq_card_fixedPoints` instantiated to the
tautological `Equiv.Perm V`-action.  We package both `Nat.card` and
`Fintype.card` forms.
-/

namespace Moore57

open MulAction

variable {V : Type*} [Fintype V]
  {p : ℕ} [Fact (Nat.Prime p)]

/-- **p-group fixed-point count mod p (Nat.card form).** For a p-group
`X ≤ Equiv.Perm V` acting on a finite `V`, `|V| ≡ |Fix(X)| (mod p)`. -/
theorem natCard_modEq_natCard_fixedPoints_of_isPGroup
    (X : Subgroup (Equiv.Perm V)) [Finite X]
    (hX : IsPGroup p X) :
    Nat.card V ≡ Nat.card (MulAction.fixedPoints X V) [MOD p] :=
  hX.card_modEq_card_fixedPoints V

/-- **p-group fixed-point count mod p (Fintype.card form).** -/
theorem card_modEq_card_fixedPoints_of_isPGroup
    [DecidableEq V]
    (X : Subgroup (Equiv.Perm V)) [Finite X]
    (hX : IsPGroup p X)
    [Fintype (MulAction.fixedPoints X V)] :
    Fintype.card V ≡ Fintype.card (MulAction.fixedPoints X V) [MOD p] := by
  have h := hX.card_modEq_card_fixedPoints V
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h

end Moore57
