import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Lemma22_SmallGroup625_12

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Proposition 4 [GAP]

> The group `SmallGroup(625, 12)` cannot act as an automorphism group of a
> Moore (57, 2)-graph Γ with the smallest orbit of size 25.

Combined with Lemma 22, this gives "no `|X| = 625` action with smallest
orbit size 25". Coupled with Proposition 5, this gives the full
"no `|X| = 625`" result needed for Theorem 5.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Proposition 4 (`SmallGroup(625, 12)` cannot act with smallest orbit 25).**
[GAP, skeleton] -/
theorem prop4_sg625_excluded (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
