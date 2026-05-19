import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155

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

/-- **Lemma 2 (corollary: `4 ∤ |Aut(Γ)|`).** [skeleton] -/
theorem lem2_four_not_dvd_aut (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S2
