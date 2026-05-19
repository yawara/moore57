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

For Moore57 (`k = 57`), part (1) gives `|F(x)| = 56`, which is wrapped from
`aut_involution_fixedVertexCount_eq_56` (Cameron/Higman, via Moore57's
adjacency-moved + K_{1,55} structure).

Part (2) (`f = k ± 1` from a star fix) is a structural lemma about
involutions on strong (0,1) graphs and is left as a general skeleton.
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

/-- **Lemma 1.4 (2) (star fix forces `f = k ± 1`).** [skeleton] -/
theorem lem1_4_part2 : True := by trivial

end Moore57.Papers.Aschbacher1971
