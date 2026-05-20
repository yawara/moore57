import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.InvolutionFixIsK155
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

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

/-! ### Lem 1.4 (2) algebraic core (D4.0)

The Higman/Aschbacher dichotomy `f ∈ {k − 1, k + 1}` reduces to the
quadratic identity `(f − k)² = 1`, equivalent to
`(f − k − 1)(f − k + 1) = 0`.  Both directions are pure ℤ algebra.

The quadratic identity comes from a trace computation:
* `tr τ = f` (counting fixed points; `τ` is an involution).
* `tr (A τ) = ±` something on each eigenspace (with `±1` for the
  trivial k-eigenspace, χ values on s, t-eigenspaces).
* `tr (A² τ) = …` second moment giving the SRG constraint.

Combining these and using the SRG identity `A² = k I + λ A + μ (J − I − A)`
yields the quadratic `(f − k)² = 1`.

The algebraic core packages just the final arithmetic step. -/

/-- **Aschbacher 1.4 (2) algebraic core (factored form)**: from the
quadratic identity `(f − k − 1)(f − k + 1) = 0`, conclude
`f = k − 1 ∨ f = k + 1`.  [done] -/
theorem asc1_4_arithmetic_core (f k : ℤ)
    (h_quad : (f - k - 1) * (f - k + 1) = 0) :
    f = k - 1 ∨ f = k + 1 := by
  rcases mul_eq_zero.mp h_quad with h | h
  · right; linarith
  · left; linarith

/-- **Aschbacher 1.4 (2) algebraic core (square form)**: from
`(f − k)² = 1`, conclude `f = k − 1 ∨ f = k + 1`.  [done]

Equivalent to `asc1_4_arithmetic_core` via the identity
`(f − k − 1)(f − k + 1) = (f − k)² − 1`. -/
theorem asc1_4_arithmetic_core_sq (f k : ℤ)
    (h_sq : (f - k) ^ 2 = 1) :
    f = k - 1 ∨ f = k + 1 := by
  apply asc1_4_arithmetic_core
  have h_eq : (f - k - 1) * (f - k + 1) = (f - k) ^ 2 - 1 := by ring
  rw [h_eq, h_sq]; ring

/-- **Aschbacher 1.4 (2) iff form**: the dichotomy
`f = k − 1 ∨ f = k + 1` is equivalent to the quadratic
`(f − k − 1)(f − k + 1) = 0`. [done] -/
theorem asc1_4_arithmetic_core_iff (f k : ℤ) :
    (f - k - 1) * (f - k + 1) = 0 ↔ (f = k - 1 ∨ f = k + 1) := by
  constructor
  · exact asc1_4_arithmetic_core f k
  · rintro (h | h) <;> · rw [h]; ring

/-- **Aschbacher 1.4 (2) Moore57 instance via the algebraic core**: for
`f = 56, k = 57`, the quadratic identity `(56 − 57)² = 1` gives the
dichotomy branch `f = k − 1` (the "minus" branch realised by Moore57).
[done] -/
theorem asc1_4_moore57_arithmetic_instance :
    (56 : ℤ) = 57 - 1 ∨ (56 : ℤ) = 57 + 1 := by
  apply asc1_4_arithmetic_core_sq 56 57
  norm_num

/-- **Lemma 1.4 (2) (general star-fix dichotomy `f = k ± 1`).** [deferred-heavy]

The algebraic core `(f − k)² = 1 ⟹ f = k ± 1` is fully formalised in
`asc1_4_arithmetic_core_sq` / `asc1_4_arithmetic_core`.

The full Lemma 1.4 (2) statement requires the spectral derivation of
the quadratic `(f − k)² = 1` from involution trace identities on the
Moore graph adjacency matrix; that remains [deferred-heavy].  Moore57
instance is `lem1_4_part2_k57` (with the explicit `f = 56 = k − 1`
branch). -/
theorem lem1_4_part2 : True := by trivial

end Moore57.Papers.Aschbacher1971
