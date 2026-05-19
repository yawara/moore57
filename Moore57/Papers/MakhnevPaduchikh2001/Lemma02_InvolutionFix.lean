import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 2

> Let Γ be a Moore graph of valence `k ≥ 3` and `t` an involution of
> `Aut(Γ)`. Then `Fix(t)` is a star centered at some vertex `a`.

This is the bedrock fact used downstream by Mačaj–Širáň as "involution
fixes a 56-vertex star". The Moore57 codebase formalizes a more specific
result: for Moore57 with `t ≠ 1`, `Fix(t)` is the star `K_{1, 55}` with
56 vertices.
-/

open Moore57

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Convert `σ ^ 2 = 1` to `Function.Involutive σ`. -/
private theorem _involutive_of_sq_eq_one {σ : Equiv.Perm V} (hσ : σ ^ 2 = 1) :
    Function.Involutive σ := fun x => by
  have h := congrArg (fun (f : Equiv.Perm V) => f x) hσ
  simpa [pow_two, Equiv.Perm.mul_apply] using h

/-- **Lemma 2 (involution fixes a star).**
For a Moore57 graph Γ and a non-trivial involution `σ ∈ Aut(Γ)`, the σ-fixed
induced subgraph is a star with some center `c`.
Wraps `aut_involution_fixedInducedGraph_isStarWithCenter`. -/
theorem lem2_involution_fix_star (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    ∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c :=
  aut_involution_fixedInducedGraph_isStarWithCenter hΓ σ hAut
    (_involutive_of_sq_eq_one hσ) hne

end Moore57.Papers.MakhnevPaduchikh2001
