import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma26_SmallPrime

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Proposition 7 [deferred-heavy]

> Let `p = 3` and `q > 5`. Then `q ≠ 11`, `Q ◁ X`, `P ⋪ X`. If `q = 19`,
> then `|P|` divides 9; if `q ∈ {7, 13}`, then `|P| = 3`.

Proof outline (paper): the `P` element of order 3 fixes a Petersen graph
whose automorphism group has order 120, so `P ⋪ X`. For `q = 13`,
`P ◁ X` is impossible since `Fix(P)` lacks order-13 automorphisms.
Combinatorial subgroup analysis on `Aut(Q) ⊃ P` excludes cyclic order 21
when `Q = Z₂₇`.
-/

namespace Moore57.Papers.MacajSiran2010.S9

/-- **Proposition 7 (`(p, q) = (3, large)` classification).** [deferred-heavy] -/
theorem prop7_3_and_large : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
