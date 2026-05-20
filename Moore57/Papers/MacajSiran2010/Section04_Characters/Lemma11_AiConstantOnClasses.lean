import Moore57.Papers.MacajSiran2010.Section04_Characters.Theorem3_RationalClasses
import Moore57.Foundations.GroupAction.FixedPoints
import Moore57.Foundations.GroupAction.FixedPointConjugacy
import Moore57.Foundations.GraphTheory.InducedTrace
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Characters

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

/-! ### Character-theoretic conjugation invariance (Moore57)

The spectral characters `χ₀, χ₁, χ₂` (defined in
`Moore57.Moore57Graph.Characters`) are constant on conjugacy classes of
`Aut(Γ)`.  This is a direct trace-cyclic-property argument and does
*not* require Theorem 3 (Curtis–Reiner), which is only needed for the
*rational class* (= coprime-power) invariance of `χⱼ`.
-/

/-- **Lemma 11 character conj-invariance for `χ₀`.** [done] -/
theorem lem11_chi0_constant_under_conjugation
    (σ τ : Equiv.Perm V) :
    chi0 (V := V) (τ * σ * τ⁻¹) = chi0 (V := V) σ :=
  chi0_conj σ τ

/-- **Lemma 11 character conj-invariance for `χ₁`.** [done]
Requires the conjugator `τ` to be a graph automorphism of `Γ`. -/
theorem lem11_chi1_constant_under_graphAut_conjugation
    (σ τ : Equiv.Perm V)
    (hτ : ∀ v w, Γ.Adj v w ↔ Γ.Adj (τ v) (τ w)) :
    chi1 Γ (τ * σ * τ⁻¹) = chi1 Γ σ :=
  chi1_conj σ τ hτ

/-- **Lemma 11 character conj-invariance for `χ₂`.** [done] -/
theorem lem11_chi2_constant_under_graphAut_conjugation
    (σ τ : Equiv.Perm V)
    (hτ : ∀ v w, Γ.Adj v w ↔ Γ.Adj (τ v) (τ w)) :
    chi2 Γ (τ * σ * τ⁻¹) = chi2 Γ σ :=
  chi2_conj σ τ hτ

/-! ### `a₀, a₁` conjugation invariance via the character chain

The paper's *character-theoretic* derivation of `aᵢ` conjugation
invariance (alternative to the direct subset/bijection arguments).
This chain uses the Theorem 1 inverse formulas combined with
`chi_j_conj`, mirroring the paper's reasoning step.
-/

/-- **Lemma 11 `a₀` conj-invariance via character chain.** [done]

`a₀(τστ⁻¹) = χ₀(τστ⁻¹) + χ₁(τστ⁻¹) + χ₂(τστ⁻¹)` (Theorem 1 row 0)
`= χ₀(σ) + χ₁(σ) + χ₂(σ)` (chi conj invariance)
`= a₀(σ)`. -/
theorem lem11_a0_via_characters
    (σ τ : Equiv.Perm V)
    (hτ : ∀ v w, Γ.Adj v w ↔ Γ.Adj (τ v) (τ w)) :
    (fixedVertexCount (τ * σ * τ⁻¹) : ℚ) = (fixedVertexCount σ : ℚ) := by
  have h_dest := chi_sum_eq_fixedVertexCount (V := V) (Γ := Γ) (τ * σ * τ⁻¹)
  have h_src := chi_sum_eq_fixedVertexCount (V := V) (Γ := Γ) σ
  rw [chi0_conj σ τ, chi1_conj σ τ hτ, chi2_conj σ τ hτ] at h_dest
  linarith [h_dest, h_src]

/-- **Lemma 11 `a₁` conj-invariance via character chain.** [done]

`a₁(τστ⁻¹) = 57·χ₀ + 7·χ₁ − 8·χ₂` evaluated at `τστ⁻¹`
`= 57·χ₀(σ) + 7·χ₁(σ) − 8·χ₂(σ)` (chi conj invariance)
`= a₁(σ)`. -/
theorem lem11_a1_via_characters
    (hΓ : IsMoore57 Γ) (σ τ : Equiv.Perm V)
    (hτ : ∀ v w, Γ.Adj v w ↔ Γ.Adj (τ v) (τ w)) :
    (adjacentMovedCount Γ (τ * σ * τ⁻¹) : ℚ) =
      (adjacentMovedCount Γ σ : ℚ) := by
  have h_dest := adjacentMovedCount_eq_chi_combination hΓ (τ * σ * τ⁻¹)
  have h_src := adjacentMovedCount_eq_chi_combination hΓ σ
  rw [chi0_conj σ τ, chi1_conj σ τ hτ, chi2_conj σ τ hτ] at h_dest
  linarith [h_dest, h_src]

/-- **Lemma 11 (`aᵢ` constant on rational classes).** [deferred-heavy]

The `a₀` part is fully proven as `lem11_a0_constant_on_rational_classes`
(direct, no character theory).  The `a₁, a₂` parts require Theorem 3
plus Lemma 3 / Theorem 1 character formulas. -/
theorem lem11_ai_constant_on_rational_classes (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S4
