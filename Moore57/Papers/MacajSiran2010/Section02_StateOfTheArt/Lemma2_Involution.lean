import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155
import Moore57.Papers.CameronCh3.Section07_Automorphisms

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 2

> Let `x` be an involutory automorphism of Γ. Then `a₀(x) = 56` and
> `a₁(x) = 112`. Consequently, the order of `Aut(Γ)` is not divisible by 4.

* `lem2_involution_a0`  — wrapped from `aut_involution_fixedVertexCount_eq_56`
  (Cameron's Theorem 3.13 / Higman, fully proved in
  `Moore57.Moore57Graph.Aut.InvolutionFixIsK155`).
* `lem2_involution_a1` — `a₁(x) = 112`. [skeleton]
  The geometric formula `a₁ = 3250 − 58·a₀ + 2·|E(Fix)|` lives in
  `Moore57.Moore57Graph.InvolutionEdgeCountFormula`; combined with
  `|Fix| = 56` and `|E(Fix)| = 55` (K₁,₅₅ has 55 edges) gives 112.
* `lem2_four_not_dvd_aut` — `4 ∤ |Aut(Γ)|`. [skeleton]
-/

open Moore57

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Convert `σ ^ 2 = 1` to `Function.Involutive σ`. -/
private theorem _involutive_of_sq_eq_one {σ : Equiv.Perm V} (hσ : σ ^ 2 = 1) :
    Function.Involutive σ := fun x => by
  have h := congrArg (fun (f : Equiv.Perm V) => f x) hσ
  simpa [pow_two, Equiv.Perm.mul_apply] using h

/-- **Lemma 2 (involution `a₀ = 56`).**
The number of fixed points of any involutory automorphism `σ` (with `σ ≠ 1`)
of a Moore57 graph equals 56. -/
theorem lem2_involution_a0 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut (_involutive_of_sq_eq_one hσ) hne

/-- **Lemma 2 (involution `a₁ = 112`).**
For any involutory automorphism `σ ≠ 1`, `adjacentMovedCount Γ σ = 112`. -/
theorem lem2_involution_a1 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    adjacentMovedCount Γ σ = 112 := by
  have hinv : Function.Involutive σ := _involutive_of_sq_eq_one hσ
  have ha0 : fixedVertexCount σ = 56 :=
    aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne
  obtain ⟨c, hstar⟩ :=
    aut_involution_fixedInducedGraph_isStarWithCenter hΓ σ hAut hinv hne
  have hformula : (adjacentMovedCount Γ σ : ℤ) =
      3250 - 58 * (fixedVertexCount σ : ℤ) + 2 * ((fixedVertexCount σ : ℤ) - 1) :=
    aut_involution_starEdgeCountFormula hΓ σ hAut hinv hstar
  rw [ha0] at hformula
  -- 3250 - 58·56 + 2·(56-1) = 3250 - 3248 + 110 = 112
  have : (adjacentMovedCount Γ σ : ℤ) = 112 := by push_cast at hformula; linarith
  exact_mod_cast this

/-- **Lemma 2 (corollary: no order-4 automorphism).**

There is no element of `Aut(Γ)` with order 4.

Proof. If `σ ∈ Aut(Γ)` has `orderOf σ = 4`, then `σ ^ 2` is a non-trivial
involution-automorphism, so by
`CameronCh3.step5_moore57_involution_sign`, `sign (σ ^ 2) = −1`. But
`sign (σ ^ 2) = (sign σ) ^ 2 = 1` (since `sign σ ∈ {±1}` and both
square to 1). Contradiction. -/
theorem lem2_no_order_four_aut (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ_ord : orderOf σ = 4)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) : False := by
  have hσ4 : σ ^ 4 = 1 := by rw [← hσ_ord]; exact pow_orderOf_eq_one σ
  have hsq2 : (σ ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hσ4
  have hsq_ne : σ ^ 2 ≠ 1 := fun h => by
    have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hσ_ord] at hdvd
    omega
  have hsq_aut : ∀ a b, Γ.Adj a b ↔ Γ.Adj ((σ ^ 2) a) ((σ ^ 2) b) := by
    intro a b
    rw [show (σ ^ 2 : Equiv.Perm V) = σ * σ from by rw [pow_two],
        Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [hAut a b, hAut (σ a) (σ b)]
  have hsign_sq : Equiv.Perm.sign (σ ^ 2) = -1 :=
    Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ (σ ^ 2) hsq2 hsq_ne hsq_aut
  have hsign_eq : Equiv.Perm.sign (σ ^ 2) = (Equiv.Perm.sign σ) ^ 2 := by
    rw [map_pow]
  have hsign_sq_one : (Equiv.Perm.sign σ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      · rw [h]; decide
  rw [hsign_eq, hsign_sq_one] at hsign_sq
  exact absurd hsign_sq (by decide)

/-- **Lemma 2 (corollary: no Klein-4 in Aut(Γ)).**

For two distinct commuting non-trivial involution-automorphisms `σ, τ`,
False follows: `στ` is also a non-trivial involution-automorphism with
`sign (στ) = (sign σ)(sign τ) = (−1)(−1) = +1`, contradicting
`sign(στ) = −1` from `step5_moore57_involution_sign`. -/
theorem lem2_no_klein_four_in_aut (hΓ : IsMoore57 Γ) (σ τ : Equiv.Perm V)
    (hσ_sq : σ ^ 2 = 1) (hσ_ne : σ ≠ 1)
    (hAut_σ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b))
    (hτ_sq : τ ^ 2 = 1) (hτ_ne : τ ≠ 1)
    (hAut_τ : ∀ a b, Γ.Adj a b ↔ Γ.Adj (τ a) (τ b))
    (hcomm : σ * τ = τ * σ) (hne : σ ≠ τ) : False := by
  -- στ is a non-trivial involution-automorphism
  have hcom : Commute σ τ := hcomm
  have hστ_sq : (σ * τ) ^ 2 = 1 := by
    rw [hcom.mul_pow, hσ_sq, hτ_sq, mul_one]
  have hστ_ne : σ * τ ≠ 1 := by
    intro h
    have hσ_inv : σ⁻¹ = σ := by
      have hσσ : σ * σ = 1 := by rw [← pow_two]; exact hσ_sq
      exact inv_eq_of_mul_eq_one_right hσσ
    have hστ : σ⁻¹ = τ := mul_eq_one_iff_inv_eq.mp h
    rw [hσ_inv] at hστ
    exact hne hστ
  have hστ_aut : ∀ a b, Γ.Adj a b ↔ Γ.Adj ((σ * τ) a) ((σ * τ) b) := by
    intro a b
    simp only [Equiv.Perm.mul_apply]
    exact (hAut_τ a b).trans (hAut_σ (τ a) (τ b))
  -- Apply step5 to all three
  have hsign_σ := Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ σ hσ_sq hσ_ne hAut_σ
  have hsign_τ := Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ τ hτ_sq hτ_ne hAut_τ
  have hsign_στ := Moore57.Papers.CameronCh3.step5_moore57_involution_sign hΓ (σ * τ) hστ_sq hστ_ne hστ_aut
  -- But sign(στ) = sign σ · sign τ = (−1)(−1) = 1
  rw [map_mul, hsign_σ, hsign_τ] at hsign_στ
  exact absurd hsign_στ (by decide)

/-- **Lemma 2 (3): `4 ∤ |Aut(Γ)|`.** [skeleton — needs Sylow]

For any subgroup `G ≤ Aut(Γ)`, `4 ∤ Fintype.card G`. Follows from
`lem2_no_order_four_aut` + `lem2_no_klein_four_in_aut` via the
classification of order-4 groups: every group of order 4 is either
cyclic (`ℤ/4`) or Klein-4 (`ℤ/2 × ℤ/2`), and both are excluded by the
two preceding lemmas. The 2-Sylow argument: if `4 ∣ |G|`, then `G` has
a subgroup of order 4 (Sylow), which is one of the two excluded
groups.

The Sylow / order-4-group-classification step requires further Mathlib
group-theory infrastructure and is left as a skeleton. -/
theorem lem2_four_not_dvd_aut (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S2
