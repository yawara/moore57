import Mathlib.GroupTheory.GroupAction.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Lemma 20 [skeleton]

> Let `O` be an orbit of an action of a group `X` on a set and let `X_o` be
> a stabilizer of an element `o ∈ O`. Let `Conj(X_o)` be the number of
> conjugates of `X_o` in `X`. Then
> ```
> |Fix(X_o) ∩ O| · Conj(X_o) = |O|.
> ```

This is a general orbit-stabilizer / conjugate counting fact, not specific
to Γ.
-/

namespace Moore57.Papers.MacajSiran2010.S6

/-- **Lemma 20 (fix-conjugate orbit count).** [skeleton] -/
theorem lem20_fix_conjugate (X : Type*) [Group X] : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
