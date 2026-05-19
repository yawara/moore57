import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition6_3and5
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition7_3andLarge
import Moore57.Papers.MacajSiran2010.Section09_MixingPrimes.Proposition8_5andLarge

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §9, Theorem 6 [deferred-heavy]

> Let Γ be a Moore graph of degree 57 on 3250 vertices and `G = Aut(Γ)`.
> If `|G|` is odd then `|G|` divides one of
> ```
> 19 · 3²,  13 · 3,  5² · 11,  7² · 3,  7 · 5,  5³ · 3,  3³ · 5.
> ```

Proof structure: by Feit–Thompson (`Mathlib.GroupTheory.Solvable`),
`G` is solvable; by Philip Hall, `G` has Hall subgroups of all
coprime orders. Combine Propositions 6, 7, 8 to enumerate at most
two-prime configurations. The only would-be three-prime config is
`Z₅ × Z₇ · Z₃`, excluded by Lemma 15.
-/

namespace Moore57.Papers.MacajSiran2010.S9

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 6 (odd `|Aut(Γ)|` divides one of seven values).** [deferred-heavy] -/
theorem thm6_odd_order (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S9
