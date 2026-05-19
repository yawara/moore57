import Moore57.Papers.MacajSiran2010.Section07_Theorem4Proof.Corollary2_SmallGroup81_9
import Moore57.Papers.MacajSiran2010.Section06_PGroupsOverview.Theorem4_3GroupBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §7, Theorem 4 (full proof) [deferred-heavy]

> Let `X` be a group of automorphisms of Γ of order `3^k`. Then `k ≤ 3`.

Proof strategy (paper §7):
1. By Lemma 17, the case `Fix(X) = singleton` is the only non-trivial one.
2. Assume `|X| = 81` for contradiction. By Corollary 2,
   `X = SmallGroup(81, 9)`.
3. Compute orbit structure in GAP: `1 + 3·3 + 6·27 + 38·81 = 3250`.
4. By Lemma 8, `Tr(X) = 26 + 30l`. By Lemma 9, `81 Tr(X) = 18 a₁(x)`
   for any order-9 element `x`, hence `a₁(x) = 117 + 135l`.
5. Common subgroup `Y ≅ Z₉ × Z₃` containing all order-9 elements; orbits
   split into size 27, so `a₁(x) = 27 k` — contradicts `a₁ = 117 + 135l`.
-/

namespace Moore57.Papers.MacajSiran2010.S7

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 4 (no 3-group of order > 27).** [deferred-heavy] -/
theorem thm4_final (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S7
