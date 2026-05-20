import Moore57.Papers.MacajSiran2010.Section04_Characters.Theorem3_RationalClasses
import Moore57.Foundations.GroupAction.FixedPoints
import Moore57.Foundations.GroupAction.FixedPointConjugacy
import Moore57.Foundations.GraphTheory.InducedTrace
import Moore57.Moore57Graph.Moore57Definition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §4, Lemma 11

> Let `X` be an automorphism group of a Moore (57, 2)-graph Γ. Then the
> functions `a₀`, `a₁`, `a₂` are constant on rational classes of `X`.

Status:
* `lem11_a0_constant_on_rational_classes`: **proven directly** (no
  character theory required) — `Fix(σ^k) = Fix(σ)` for `k` coprime
  to `orderOf σ`, plus conjugation invariance.  See
  `Moore57.fixedVertexCount_pow_coprime` and
  `Moore57.fixedVertexCount_conj`.
* `lem11_a1_constant`, `lem11_a2_constant`: [deferred-heavy] — require
  Theorem 3 (rational characters constant on rational classes) plus
  the Moore57 character formulas `χⱼ = ∑ ℤ-coeff · aᵢ` (Lemma 3,
  Theorem 1) to express `a₁, a₂` as ℤ-linear combinations of rational
  characters.

Two elements `x, y` of `X` are in the same **rational class** iff
`⟨x⟩` and `⟨y⟩` are conjugate as cyclic subgroups, equivalently
`y = τ · x^k · τ⁻¹` for some `τ ∈ X` and `k` coprime to `orderOf x`. -/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S4

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 11 for `a₀` (`fixedVertexCount` constant on rational classes).** [done]

If `y = τ · σ^k · τ⁻¹` with `k` coprime to `orderOf σ`, then
`fixedVertexCount y = fixedVertexCount σ`.  Proof: conjugation
invariance followed by coprime-power invariance.

This is a *purely permutation-theoretic* result; no Moore57 / SRG
hypothesis is required.  The full Lemma 11 (covering `a₁, a₂`) needs
Theorem 3 plus the Moore57 character formulas and remains
deferred-heavy. -/
theorem lem11_a0_constant_on_rational_classes
    (σ τ : Equiv.Perm V) {k : ℕ}
    (hk : Nat.Coprime k (orderOf σ)) :
    fixedVertexCount (τ * σ ^ k * τ⁻¹) = fixedVertexCount σ := by
  rw [fixedVertexCount_conj, fixedVertexCount_pow_coprime σ hk]

/-- **Lemma 11 for `a₁`, conjugation part (no power)** [done]

If `τ` is a graph automorphism of `Γ` and `σ` any permutation, then
`adjacentMovedCount Γ (τ · σ · τ⁻¹) = adjacentMovedCount Γ σ`.

Wraps `Moore57.adjacentMovedCount_conj`.  This is the conjugation-
invariance half of Lemma 11 for `a₁`; the coprime-power half
`a₁(σ^k) = a₁(σ)` requires character-theoretic input (Theorem 3) and
remains in `lem11_ai_constant_on_rational_classes`. -/
theorem lem11_a1_constant_under_graphAut_conjugation
    (σ τ : Equiv.Perm V)
    (hτ : ∀ a b : V, Γ.Adj a b ↔ Γ.Adj (τ a) (τ b)) :
    adjacentMovedCount Γ (τ * σ * τ⁻¹) = adjacentMovedCount Γ σ :=
  adjacentMovedCount_conj τ σ hτ

/-- **Lemma 11 for `a₁`, inverse symmetry** [done]

`a₁(σ⁻¹) = a₁(σ)` for any permutation `σ`.  This is the `k = -1`
(equivalently `k = orderOf σ - 1`) coprime-power instance; the only
coprime-power case that does NOT require character theory.

Wraps `Moore57.adjacentMovedCount_inv`. -/
theorem lem11_a1_constant_under_inv (σ : Equiv.Perm V) :
    adjacentMovedCount Γ σ⁻¹ = adjacentMovedCount Γ σ :=
  adjacentMovedCount_inv σ

/-- **Lemma 11 (`aᵢ` constant on rational classes).** [deferred-heavy]

The `a₀` part is fully proven as `lem11_a0_constant_on_rational_classes`
(direct, no character theory).  The `a₁, a₂` parts require Theorem 3
plus Lemma 3 / Theorem 1 character formulas. -/
theorem lem11_ai_constant_on_rational_classes (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S4
