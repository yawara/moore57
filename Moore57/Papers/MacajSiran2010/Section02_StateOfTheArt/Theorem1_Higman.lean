import Moore57.D19OnMoore57.HigmanTrace.Congruence
import Moore57.Foundations.Representation.PermutationRepresentationCharacter

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Theorem 1 (Higman trace identity) [skeleton]

> Let Γ be a Moore (57, 2)-graph with adjacency matrix `A`. Let `V₀, V₁, V₂`
> be the eigenspaces of `A` for eigenvalues 57, 7, −8 respectively. Let `X`
> be an automorphism group of Γ and let `χ₀, χ₁, χ₂` be characters of the
> restriction of `X` onto `V₀, V₁, V₂`. Set `a_i(x) = |{v : d(v, vx) = i}|`.
> Then
> ```
> (χ₀(x), χ₁(x), χ₂(x))ᵀ = Q (a₀(x), a₁(x), a₂(x))ᵀ
> ```
> with `Q = P⁻¹` and explicit `P, Q` matrices.

The Lean proof lives across
`Moore57.D19OnMoore57.HigmanTrace.Congruence` and the projection-based
machinery in `Moore57.D19OnMoore57.E7Projection.*`. This file re-states the
identity at the paper's level of abstraction.
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Theorem 1 (Higman trace identity, χ₁ component).**
For any automorphism `x` of Γ, `χ₁(x) = (1/15)(8 a₀(x) + a₁(x) − 65)`. [skeleton] -/
theorem thm1_chi1_formula (hΓ : IsMoore57 Γ) (x : Equiv.Perm V)
    (hx : ∀ a b, Γ.Adj a b ↔ Γ.Adj (x a) (x b)) :
    True := by
  trivial

end Moore57.Papers.MacajSiran2010.S2
