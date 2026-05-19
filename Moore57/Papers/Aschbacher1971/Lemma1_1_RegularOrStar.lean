import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GraphTheory.StrongZeroOne

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.1

> Let `𝒢` be a triangle-free, irreflexive 1-system with `d(A, B) ≤ 2` for
> all `A, B ∈ ℰ`. Then `𝒢` is either regular or a star.

In our formalisation, condition (*) is captured by `IsStrongZeroOne`:

* triangle-free  ⇔  `of_adj`:  adjacent vertices share 0 common neighbours.
* 1-system + `d ≤ 2`  ⇔  `of_not_adj`: distinct non-adjacent vertices
  share exactly 1 common neighbour.

(Irreflexivity is automatic for `SimpleGraph`.)

The dichotomy then follows directly from the existing
`IsStrongZeroOne.exists_isStarWithCenter_of_not_regular`.
-/

open Moore57

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Lemma 1.1 (regular-or-star dichotomy).**
A finite simple graph satisfying the strong (λ = 0, μ = 1) common-neighbour
condition is either regular or a star with some centre. -/
theorem lem1_1_regular_or_star (hG : IsStrongZeroOne G) :
    (∃ k : ℕ, G.IsRegularOfDegree k) ∨ (∃ c : V, IsStarWithCenter G c) := by
  by_cases hreg : ∃ k : ℕ, ∀ v : V, G.degree v = k
  · exact Or.inl hreg
  · exact Or.inr (hG.exists_isStarWithCenter_of_not_regular hreg)

/-- **Lemma 1.1, Moore57 instance.**
Moore57 satisfies the strong (0, 1) condition (`IsSRGWith 3250 57 0 1` ⊆
`IsStrongZeroOne`), so the dichotomy applies. In this concrete case the
regular branch is realised (Moore57 is 57-regular by definition). -/
theorem lem1_1_moore57 {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) :
    (∃ k : ℕ, Γ.IsRegularOfDegree k) ∨ (∃ c : V, IsStarWithCenter Γ c) :=
  Or.inl ⟨57, hΓ.regular⟩

end Moore57.Papers.Aschbacher1971
