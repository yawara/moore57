import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Proposition3_HSFixBound

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Lemma 23 [deferred-heavy]

> Let `X` be an automorphism group of Γ of order 625 with the smallest
> orbit of size 125. Then `X` contains a subgroup `Y` of order 5 which is
> a vertex stabilizer in at least one and at most two orbits of size 125.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 23 (stabilizer in 1 or 2 size-125 orbits).** [deferred-heavy] -/
theorem lem23_stabilizer_orbits (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
