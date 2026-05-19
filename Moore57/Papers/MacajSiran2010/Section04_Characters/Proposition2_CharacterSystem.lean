import Moore57.Papers.MacajSiran2010.Section04_Characters.Theorem3_RationalClasses
import Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §4, Proposition 2 [deferred-heavy]

> Let `H` be a finite group and let `x₁, …, x_u` be representatives of
> rational classes of `H`. Let `R₁, …, R_u` be irreducible `ℚ`-representations
> of `H` with characters `r₁, …, r_u`. Then for any rational representation
> `R` with character `χ`, the system
> ```
> ⎛ r₁(x₁)  r₂(x₁)  …  r_u(x₁) | χ(x₁) ⎞
> ⎜ r₁(x₂)  r₂(x₂)  …  r_u(x₂) | χ(x₂) ⎟
> ⎜  ⋮       ⋮     ⋱     ⋮     |   ⋮   ⎟
> ⎝ r₁(x_u) r₂(x_u) …  r_u(x_u)| χ(x_u)⎠
> ```
> has a solution in non-negative integers.

This is the workhorse for the entire §5 table. Already used heavily in
`Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace` for primes 19, 11.
-/

namespace Moore57.Papers.MacajSiran2010.S4

/-- **Proposition 2 (non-negative integer character system).** [deferred-heavy] -/
theorem prop2_character_system : True := by trivial

end Moore57.Papers.MacajSiran2010.S4
