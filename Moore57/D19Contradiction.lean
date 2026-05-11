import Moore57.Moore57Graph.Moore57Definition
import Moore57.D19OnMoore57.Counting.AbstractCounting
import Moore57.D19OnMoore57.AbstractHypotheses
import Moore57.D19OnMoore57.Action.D19Action
import Moore57.Foundations.GroupTheory.Dihedral19LinearCharacter

/-!
# Moore57 / D₁₉ contradiction: re-export shim (deprecated)

This file used to be a 1377-line monolith containing:

* `IsMoore57` and Moore graph basic facts → now in
  `Moore57.Moore57Graph.Moore57Definition`.
* `counting_contradiction`, `TraceRepresentationData`,
  `Dq_card_le_two_of_moore`, `internalDiffSet` etc. → now in
  `Moore57.D19OnMoore57.Counting.AbstractCounting`.
* `D19ConcreteHypotheses`, `no_D19_concrete_hypotheses` etc. → now in
  `Moore57.D19OnMoore57.AbstractHypotheses`.
* `D19ActsOnMoore57` structure, `rotation`, `a1`, `smulEquiv`, basic
  action lemmas → now in `Moore57.D19OnMoore57.Action.D19Action`.

This shim re-exports all four split files so existing importers keep working.
New code should import the specific module it needs.
-/
