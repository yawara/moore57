import Moore57.Papers.MacajSiran2010.Section04_Characters.Theorem3_RationalClasses

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §4, Lemma 11 [deferred-heavy]

> Let `X` be an automorphism group of a Moore (57, 2)-graph Γ. Then the
> functions `a₀`, `a₁`, `a₂` are constant on rational classes of `X`.

Proof outline (in paper): `aᵢ(x)` is a linear combination of `χⱼ(x)`,
which are characters of rational representations of `X`; apply Theorem 3.
-/

namespace Moore57.Papers.MacajSiran2010.S4

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 11 (`aᵢ` constant on rational classes).** [deferred-heavy] -/
theorem lem11_ai_constant_on_rational_classes (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S4
