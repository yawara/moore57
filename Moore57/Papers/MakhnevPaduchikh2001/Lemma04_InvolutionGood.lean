import Moore57.Papers.MakhnevPaduchikh2001.Lemma02_InvolutionFix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Makhnev–Paduchikh 2001, Lemma 4

> Every involution of `G = Aut(Γ)` is "good" — for a Moore graph of valence
> `k`, an involution `t` is good iff `|Fix(t)| = k − 1`.
>
> In our case (`k = 57`), this asserts `|Fix(t)| = 56`. The paper's
> consequence "every involution is an odd permutation" follows, and from
> that the group decomposition `G = O(G)⟨t⟩` used downstream.

We wrap the `|Fix(t)| = 56` claim from
`Moore57.Moore57Graph.Aut.InvolutionFixIsK155`; the odd-permutation /
`G = O(G)⟨t⟩` consequences remain skeletons.
-/

open Moore57

namespace Moore57.Papers.MakhnevPaduchikh2001

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Convert `σ ^ 2 = 1` to `Function.Involutive σ`. -/
private theorem _involutive_of_sq_eq_one' {σ : Equiv.Perm V} (hσ : σ ^ 2 = 1) :
    Function.Involutive σ := fun x => by
  have h := congrArg (fun (f : Equiv.Perm V) => f x) hσ
  simpa [pow_two, Equiv.Perm.mul_apply] using h

/-- **Lemma 4 (involution is "good": `|Fix(t)| = 56`).**
Every non-trivial involution of a Moore57 graph fixes exactly 56 vertices —
this is the `k = 57` instance of the paper's "good" definition `|Fix(t)| = k − 1`. -/
theorem lem4_involution_good (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (hAut : ∀ a b, Γ.Adj a b ↔ Γ.Adj (σ a) (σ b)) :
    fixedVertexCount σ = 56 :=
  aut_involution_fixedVertexCount_eq_56 hΓ σ hAut
    (_involutive_of_sq_eq_one' hσ) hne

end Moore57.Papers.MakhnevPaduchikh2001
