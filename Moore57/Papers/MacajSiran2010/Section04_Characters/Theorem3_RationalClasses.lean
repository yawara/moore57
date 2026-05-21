import Moore57.Foundations.Representation.PermutationRepresentationCharacter
import Mathlib.RepresentationTheory.Character

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §4, Theorem 3 (Curtis–Reiner) [external]

> Let `H` be a finite group. Then, any rational representation of `H` is
> constant on all rational classes of `H` and the number of irreducible
> rational representations of `H` is equal to the number of rational
> classes of `H`.

This is a classical theorem of Curtis–Reiner [Representations of Finite
Groups and Associative Algebras], §27 (also §35 in some editions). Two
elements `x, y ∈ H` are in the same **rational class** iff `⟨x⟩ ~ ⟨y⟩`
as cyclic subgroups, equivalently `y = g · x^k · g⁻¹` for some `g ∈ H`
and `k ∈ ℤ` with `gcd(k, orderOf x) = 1`.

We package the substantive content as a `Prop` (`Theorem3RationalClasses`)
so downstream lemmas can take it as an explicit hypothesis. The
unconditional `thm3_rational_classes` stub remains a `True` placeholder
since the proof itself is **not** in Mathlib (Curtis–Reiner is an
unmigrated classical result; cf. roadmap §0 item 4).

**Moore57-specific bypass**: for the **prime-order** rational classes
that actually arise in the Mačaj–Širáň starred-row arguments, the
cyclotomic integer-trace machinery
(`Foundations/LinearAlgebra/PowPrimeTrace.lean`, B4.1) handles trace
integrality without Theorem 3. The full `Theorem3RationalClasses` is
only required for **composite-order** classes (deferred B4.3).
-/

namespace Moore57.Papers.MacajSiran2010.S4

universe u v

/-- **Theorem 3 (Curtis–Reiner) — abstract conclusion as a `Prop`.**

For any finite group `G` and any rational representation `ρ : G →* GL(V)`
over `ℚ`, the character `Representation.character ρ` is constant on
rational classes of `G`. Equivalently, for any `σ : G` and any integer
`k` coprime to `orderOf σ`,
`ρ.character (σ ^ k) = ρ.character σ`. -/
def Theorem3RationalClasses
    {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (ρ : Representation ℚ G V) : Prop :=
  ∀ (σ : G) (k : ℤ),
    Nat.Coprime k.natAbs (orderOf σ) →
    ρ.character (σ ^ k) = ρ.character σ

/-- **Theorem 3 (paper-faithful conditional re-export).** [done — conditional]

Proper-signature paper-faithful form: given the Curtis–Reiner-style
hypothesis `Theorem3RationalClasses ρ` (rational character constant on
rational classes) as input, for any `σ : G` and integer `k` coprime to
`orderOf σ`, conclude `ρ.character (σ ^ k) = ρ.character σ`.

This makes the `Prop`-level abstract conclusion usable as a hypothesis
in downstream lemmas that need the rational-class constancy.  The
underlying Curtis–Reiner theorem itself is external (unmigrated from
Mathlib). -/
theorem thm3_rational_classes_paper
    {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (ρ : Representation ℚ G V) (h : Theorem3RationalClasses ρ)
    (σ : G) (k : ℤ) (hk : Nat.Coprime k.natAbs (orderOf σ)) :
    ρ.character (σ ^ k) = ρ.character σ :=
  h σ k hk

/-- **Theorem 3 (rational characters constant on rational classes).** [external]

Placeholder for the unmigrated Curtis–Reiner theorem. The substantive
statement is captured in `Theorem3RationalClasses` and the conditional
re-export `thm3_rational_classes_paper` (above). -/
theorem thm3_rational_classes : True := by trivial

end Moore57.Papers.MacajSiran2010.S4
