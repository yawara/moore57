import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma26_SmallPrime

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Proposition 8 [deferred-heavy]

> Let `p = 5` and `q > 5`. Then `q ∈ {7, 11}` and `Q ◁ X`. If `q = 11`,
> then `|P|` divides 25. If `q = 7`, then `P ◁ X` and `|X| = 35`.

Excludes `q ∈ {13, 19}` outright. The `q = 11` case is where our
Order 22 result `Moore57.Order22OnMoore57.NoGo` plays into the broader
mixing-primes story (via `2p = 22` row).
-/

namespace Moore57.Papers.MacajSiran2010.S9

/-- **Proposition 8 (`(p, q) = (5, large)` classification).** [deferred-heavy] -/
theorem prop8_5_and_large : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
