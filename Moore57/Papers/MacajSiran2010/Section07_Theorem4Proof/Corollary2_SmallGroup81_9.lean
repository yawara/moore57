import Moore57.Papers.MacajSiran2010.Section07_Theorem4Proof.Lemma21_3GroupSingleFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §7, Corollary 2 [GAP]

> If `|X| = 81`, then `X ≅ SmallGroup(81, 9)` of the GAP library.

This identifies a hypothetical 3-group of order 81 acting on Γ with the
specific GAP small group. The original proof inspects subgroup lattices
of all groups of order 81 in GAP and identifies the unique candidate.

Lean strategy: hand-construct `SmallGroup(81, 9)` (`(ℤ/9 × ℤ/3) ⋊ ℤ/3`)
and verify its uniqueness criterion via `native_decide`.
-/

namespace Moore57.Papers.MacajSiran2010.S7

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Corollary 2 (`|X| = 81` ⇒ `X = SmallGroup(81, 9)`).** [GAP, skeleton] -/
theorem cor2_smallGroup_81_9 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S7
