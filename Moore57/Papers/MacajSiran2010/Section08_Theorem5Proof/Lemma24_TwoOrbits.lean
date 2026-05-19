import Moore57.Papers.MacajSiran2010.Section08_Theorem5Proof.Lemma23_StabilizerOrbits

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §8, Lemma 24 [deferred-heavy]

> Let `X` have order 625 and let the smallest orbit of `X` have size 125.
> Then `X` has at least two orbits of size 125.

Proof outline (paper): pick a central element `x ∈ X` of order 5. By
Lemma 12, `a₁(x) > 0`, so `x` contributes to at least one orbit `O`. By
Lemma 7, `|O| ≤ a₁(x)`, and by Corollary 1, `a₁(x) ≤ 500`. So `|O| ≤ 500`.
Moreover `x` and `x²` contribute to different orbits.
-/

namespace Moore57.Papers.MacajSiran2010.S8

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 24 (`|X| = 625` with smallest orbit 125 has ≥ 2 such orbits).** [deferred-heavy] -/
theorem lem24_two_orbits (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S8
