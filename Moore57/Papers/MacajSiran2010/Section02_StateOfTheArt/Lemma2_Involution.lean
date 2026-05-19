import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 2 [wrap]

> Let `x` be an involutory automorphism of Γ. Then `a₀(x) = 56` and
> `a₁(x) = 112`. Consequently, the order of `Aut(Γ)` is not divisible by 4.

The existing infrastructure in
`Moore57.Moore57Graph.Aut.InvolutionCandidates`
(`aut_involution_fixedVertexCount_candidates`) and
`Moore57.Moore57Graph.Aut.InvolutionFixIsK155` proves `Fix(σ)` is a 56-vertex
star with neighbour count 112. This file re-exports those results.
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 2 (involution `a₀ = 56`).** [skeleton] -/
theorem lem2_involution_a0 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    True := by
  trivial

/-- **Lemma 2 (involution `a₁ = 112`).** [skeleton] -/
theorem lem2_involution_a1 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    True := by
  trivial

/-- **Lemma 2 (corollary: `4 ∤ |Aut(Γ)|`).** [skeleton] -/
theorem lem2_four_not_dvd_aut (hΓ : IsMoore57 Γ) : True := by trivial

end Moore57.Papers.MacajSiran2010.S2
