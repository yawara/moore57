import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition3_HSFixBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Lemma 22 [GAP]

> If `X` is a group of automorphisms of Γ of order 625 and with the
> smallest orbit size 25, then `X ≅ SmallGroup(625, 12)` of the GAP library.

Lean strategy: hand-construct `SmallGroup(625, 12)` and verify uniqueness
criterion via `native_decide`. Performance with 625-element group may be
borderline.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 22 (`|X| = 625, smallest orbit 25` ⇒ `X = SmallGroup(625, 12)`).**
[GAP, skeleton] -/
theorem lem22_smallGroup_625_12 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
