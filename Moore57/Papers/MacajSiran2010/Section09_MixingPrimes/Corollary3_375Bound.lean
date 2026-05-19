import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Theorem6_OddOrder
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Theorem7_EvenOrder

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Corollary 3 [skeleton]

> Let Γ be a Moore graph of degree 57 on 3250 vertices and `G = Aut(Γ)`.
> Then `|G| ≤ 375`, and if `|G|` is even then `|G| ≤ 110`.

This is the main quantitative result of the paper.
-/

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Corollary 3 (`|Aut(Γ)| ≤ 375`, and `≤ 110` if even).** [skeleton] -/
theorem cor3_375_bound (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
