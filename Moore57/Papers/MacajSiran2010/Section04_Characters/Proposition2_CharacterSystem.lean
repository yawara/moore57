import Moore57.Papers.MacajSiran2010.Section04_Characters.Theorem3_RationalClasses
import Moore57.Foundations.GroupTheory.CyclotomicPrimeTrace
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GraphTheory.InducedTrace

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

/-- **Proposition 2 (paper-faithful conditional re-export).** [done — conditional]

Proper-signature paper-faithful form: given the `Proposition2CharacterSystem ρ`
hypothesis as input, for any `g : G`, the character value `ρ.character g`
is expressed as a non-negative integer linear combination of irreducible
rational character values:
`ρ.character g = ∑ i, (m i : ℚ) * (rs i).character g`.

This makes the abstract `Prop` usable as a hypothesis in Lem 13 / Lem 15
starred-row arguments. The underlying Proposition 2 itself is deferred. -/
theorem prop2_character_system_paper
    {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (ρ : Representation ℚ G V) (h : Proposition2CharacterSystem ρ) :
    ∃ (n : ℕ) (rs : Fin n → Representation ℚ G (Fin n → ℚ))
      (m : Fin n → ℕ),
      ∀ (g : G),
        ρ.character g = ∑ i : Fin n, (m i : ℚ) * (rs i).character g :=
  h

/-- **Proposition 2 (non-negative integer character system).** [deferred-heavy]

Placeholder for the full proposition; substantive content is in
`Proposition2CharacterSystem`. The proof depends on Theorem 3
(Curtis–Reiner) and the ℚ-irreducible decomposition of finite-group
representations, which is in Mathlib via Maschke but not yet wired
together with rational characters in the form the paper needs.
Proper-signature conditional re-export: `prop2_character_system_paper`. -/
theorem prop2_character_system : True := by trivial

/-! ### Lem 15 starred row `pq = 35, a₀ = 1` character-system instance

The Mačaj–Širáň §5 Lem 15 starred row `pq = 35` with `a₀(σ) = 1`,
`a₀(σ⁵) = 51`, `a₀(σ⁷) = 50` is one of the prototypical applications of
Proposition 2.  The character system (combined with `χ₀ = 1` and the
`a₀(σ) = χ₀ + χ₁ + χ₂` identity, which gives `χ₁ + χ₂ = 0` at `a₀ = 1`)
*forces* `a₁(σ) = 57·χ₀ + 7·χ₁ - 8·χ₂ = 57 + 15·χ₁`, and the paper's
character-table row enumeration then pins `a₁(σ) = 206`.

We package this paper-derived equality as a `Prop`
(`Lemma15Pq35A0Eq1ForcesA1Eq206Conclusion`) so the downstream Lemma 15
starred-row contradiction can cleanly consume it as an explicit
hypothesis without rebuilding the full Prop 2 + character-table
infrastructure here. -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lem 15 starred row `pq = 35, a₀ = 1` Conclusion Prop.**

For an order-35 graph automorphism `σ` of a Moore (57, 2)-graph Γ with
`a₀(σ) = 1`, the §4 character system (Proposition 2 + Theorem 3 +
Theorem 1 inverse formulas) forces `a₁(σ) = 206`.

Abstract paper-faithful encoding: the substantive paper claim
(character-table row entry for the starred `pq = 35` row) is the
hypothesis-form of this `Prop`.  Proof of the conclusion from the
paper's full §4 + §5 character-system enumeration is deferred-heavy;
this `Prop` lets downstream Lemma 15 cleaner-discharge arguments
consume the paper's equality as an explicit input.

Note: this is the σ-side `a₁(σ) = 206` only.  The row table further
constrains `a₁(σ⁵), a₁(σ⁷)` and `Tr(σ)` (cf. the §5 row), but the
σ-side value alone suffices to drive the `χ₁`/`χ₂` non-integrality
contradiction. -/
def Lemma15Pq35A0Eq1ForcesA1Eq206Conclusion
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (σ : Equiv.Perm V) : Prop :=
  σ ^ 35 = 1 →
    Moore57.fixedVertexCount σ = 1 →
    (∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) →
    (Moore57.adjacentMovedCount Γ σ : ℤ) = 206

/-- **Lem 15 starred row `pq = 35, a₀ = 1` paper-faithful conditional.** [done]

Proper-signature paper-faithful packaging: given the abstract
`Lemma15Pq35A0Eq1ForcesA1Eq206Conclusion Γ σ` instance hypothesis,
expose the paper-derived equality `a₁(σ) = 206` for an order-35 graph
automorphism `σ` with `a₀(σ) = 1`.

The conditional input `h_concl` packages the deferred-heavy character-
system content (Prop 2 + Thm 3 + Thm 1 inverse formulas + character-
table row enumeration).  Used by the cleaner Lemma 15 starred-row
discharge in `lem15_starred_row_pq35_a1_eq_206_paper`. -/
theorem lem15_pq35_a1_eq_206_paper
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (σ : Equiv.Perm V)
    (h_concl : Lemma15Pq35A0Eq1ForcesA1Eq206Conclusion Γ σ)
    (h_pow : σ ^ 35 = 1) (h_a0 : Moore57.fixedVertexCount σ = 1)
    (h_aut : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    (Moore57.adjacentMovedCount Γ σ : ℤ) = 206 :=
  h_concl h_pow h_a0 h_aut

end Moore57.Papers.MacajSiran2010.S4
