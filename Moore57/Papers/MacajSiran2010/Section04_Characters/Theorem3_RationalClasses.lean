import Moore57.Foundations.Representation.PermutationRepresentationCharacter

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §4, Theorem 3 (Curtis–Reiner) [external]

> Let `H` be a finite group. Then, any rational representation of `H` is
> constant on all rational classes of `H` and the number of irreducible
> rational representations of `H` is equal to the number of rational
> classes of `H`.

This is a classical theorem of Curtis–Reiner [4]. Two elements `x, y ∈ H`
are in the same **rational class** iff `⟨x⟩ ~ ⟨y⟩` as subgroups.
-/

namespace Moore57.Papers.MacajSiran2010.S4

/-- **Theorem 3 (rational characters constant on rational classes).** [external] -/
theorem thm3_rational_classes : True := by trivial

end Moore57.Papers.MacajSiran2010.S4
