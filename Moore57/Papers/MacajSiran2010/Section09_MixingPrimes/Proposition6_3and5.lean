import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Lemma26_SmallPrime

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Proposition 6 [skeleton]

> Let `p = 3` and `q = 5`. Then `Q ◁ X`. Moreover,
>
> (1) if `P ◁ X`, then `|Fix(P)| = 10`, `|Fix(Q)| = 0`, and `|Q| = 5`;
>
> (2) if `P ⋪ X`, then `|P| = 3` and `Q ∈ {Z₂₅, Z₃₅, Z₂₅ · Z₅}`.

The `(2)` case excludes a number of would-be subgroups via Lemma 13
and the structure of automorphism groups of small 5-groups.
-/

namespace Moore57.Papers.MacajSiran2010.S9

/-- **Proposition 6 (`(p, q) = (3, 5)` classification).** [skeleton] -/
theorem prop6_3_and_5 : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
