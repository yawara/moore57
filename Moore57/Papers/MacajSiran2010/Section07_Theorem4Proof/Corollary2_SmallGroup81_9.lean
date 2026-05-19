import Moore57.Papers.MacajSiran2010.Section07_Theorem4Proof.Lemma21_3GroupSingleFix
import Moore57.Foundations.GroupTheory.SmallGroup819

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §7, Corollary 2 [GAP]

> If `|X| = 81`, then `X ≅ SmallGroup(81, 9)` of the GAP library.

This identifies a hypothetical 3-group of order 81 acting on Γ with the
specific GAP small group. The original proof inspects subgroup lattices
of all groups of order 81 in GAP and identifies the unique candidate.

## Lean infrastructure

An explicit Lean construction of `SmallGroup(81, 9)` is provided in
`Moore57.Foundations.GroupTheory.SG819` — a split extension
`(Z₉ × Z₃) ⋊ Z₃` with Eisenstein-type action `ψ(a, b) = (a + 3b, -a + b)`
satisfying `1 + ψ + ψ² = 0`.  The GAP-quoted invariants of
`SmallGroup(81, 9)` are checked by `native_decide`:

* `SG819.card_eq : Fintype.card SG819 = 81`
* `SG819.card_orderEq_three : 62 elements of order 3` (matches GAP)
* `SG819.card_orderEq_nine  : 18 elements of order 9` (matches GAP)
* `SG819.card_center        : |Z(SG819)| = 3`

The remaining content of Corollary 2 (the classification step: among the
15 groups of order 81, this is the unique one satisfying the hypothesis
from Lemma 20) is still pending — it requires either a 15-group
enumeration or a high-level structure theorem.
-/

namespace Moore57.Papers.MacajSiran2010.S7

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Corollary 2 (`|X| = 81` ⇒ `X = SmallGroup(81, 9)`).** [GAP, skeleton]

The candidate group is constructed at
`Moore57.Foundations.GroupTheory.SG819`. The classification step
(uniqueness among order-81 groups) is still pending. -/
theorem cor2_smallGroup_81_9 (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S7
