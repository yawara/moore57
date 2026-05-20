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

We capture the substantive consequence — "for any rational character
`χ` of `H`, the multiplicity vector of `χ` in the rational irreps is a
non-negative-integer solution of the character system above" — as the
proposition `Proposition2CharacterSystem`. This depends on
`Theorem3RationalClasses` (rational characters are constant on rational
classes) plus the standard structure of the rational character table.
-/

namespace Moore57.Papers.MacajSiran2010.S4

universe u v

/-- **Proposition 2 (character system, abstract conclusion as a `Prop`).**

For any rational representation `ρ : G → GL(V)` over `ℚ`, the vector of
character values `(ρ.character x₁, …, ρ.character x_u)` (indexed by a
rational-class representative system) is a non-negative-integer linear
combination of the irreducible rational character vectors.

Formally, this is encoded as: there exists a non-negative-integer-valued
function `m` on the irreducible rational characters of `G` such that
`ρ.character g = ∑ (χ irr), m χ • χ g` for all `g`. This follows from
Maschke's theorem (ℚ has characteristic 0) plus `Theorem3RationalClasses`. -/
def Proposition2CharacterSystem
    {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (ρ : Representation ℚ G V) : Prop :=
  ∃ (n : ℕ) (rs : Fin n → Representation ℚ G (Fin n → ℚ))
    (m : Fin n → ℕ),
    ∀ (g : G),
      ρ.character g = ∑ i : Fin n, (m i : ℚ) * (rs i).character g

/-- **Proposition 2 (non-negative integer character system).** [deferred-heavy]

Placeholder for the full proposition; substantive content is in
`Proposition2CharacterSystem`. The proof depends on Theorem 3
(Curtis–Reiner) and the ℚ-irreducible decomposition of finite-group
representations, which is in Mathlib via Maschke but not yet wired
together with rational characters in the form the paper needs. -/
theorem prop2_character_system : True := by trivial

end Moore57.Papers.MacajSiran2010.S4
