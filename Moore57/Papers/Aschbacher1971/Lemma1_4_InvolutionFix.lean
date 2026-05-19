import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.4

> Let `𝒢` satisfy (*) and assume `𝒢` is regular with valence `k`. Let
> `x` be an involution in `Aut 𝒢`. Then
>
> (1) if `x` has a cycle `(A, Ax)` with `A I Ax`, then `|F(x)| = k − 1`;
>
> (2) if `F(x)` is a star of order `f`, then `f = k ± 1`.

For Moore57 (`k = 57`), part (1) gives `|F(x)| = 56`, wrapped from
`aut_involution_fixedVertexCount_eq_56` (Cameron/Higman, via Moore57's
adjacency-moved + K_{1,55} structure).

For part (2) on Moore57: the involution fix is the K_{1,55} star, and we
prove `f = 56 = k − 1` (the "−" branch). The general "f = k + 1 or
f = k − 1" disjunction is left as a [deferred-heavy].
-/

open Moore57

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Convert `σ ^ 2 = 1` to `Function.Involutive σ`. -/
private theorem _involutive_of_sq_eq_one {σ : Equiv.Perm V} (hσ : σ ^ 2 = 1) :
    Function.Involutive σ := fun x => by
  have h := congrArg (fun (f : Equiv.Perm V) => f x) hσ
  simpa [pow_two, Equiv.Perm.mul_apply] using h

/-- **Lemma 1.4 (1), `k = 57` instance.**
For an involution `σ ∈ Aut(Γ)` with `σ ≠ 1`, the existence of a moved
adjacent pair `A ~ σA` forces `|Fix(σ)| = k − 1 = 56`. -/
theorem lem1_4_part1_k57 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut
    (_involutive_of_sq_eq_one hσ) hne

/-- **Lemma 1.4 (2), `k = 57` instance — the "minus" branch is realised.**

For a non-trivial involution `σ ∈ Aut(Γ)`, `Fix(σ)` is a star (by part 1
combined with Moore57's structural lemma) and `|Fix(σ)| = 56 = k − 1`.

So the Moore57 instance of Aschbacher's Lemma 1.4 (2) sits in the `f = k − 1`
branch of the dichotomy. -/
theorem lem1_4_part2_k57 (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    (∃ c : fixedVertexSet σ, IsStarWithCenter (autFixedInducedGraph Γ σ) c) ∧
      fixedVertexCount σ = 56 := by
  have hinv := _involutive_of_sq_eq_one hσ
  refine ⟨?_, ?_⟩
  · exact aut_involution_fixedInducedGraph_isStarWithCenter hΓ σ hAut hinv hne
  · exact aut_involution_fixedVertexCount_eq_56 hΓ σ hAut hinv hne

/-- **Lemma 1.4 (2) (general star-fix dichotomy `f = k ± 1`).** [deferred-heavy] -/
theorem lem1_4_part2 : True := by trivial

end Moore57.Papers.Aschbacher1971
