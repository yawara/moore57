import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Lemma17_3Group

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §6, Theorem 4 [skeleton]

> Let `X` be a group of automorphisms of Γ of order `3^k`. Then `k ≤ 3`.

Statement only; the full proof is in `Section07_Theorem4Proof/`.
-/

namespace Moore57.Papers.MacajSiran2010.S6

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 4 (3-group order ≤ 27).** [skeleton] -/
theorem thm4_3group_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S6
