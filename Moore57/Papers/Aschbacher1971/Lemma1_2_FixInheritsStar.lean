import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.InducedSubgraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.2

> Let `𝒢` satisfy condition (*) (triangle-free, irreflexive 1-system,
> `d(A, B) ≤ 2`). Let `G ≤ Aut 𝒢`. Then `F(G)` (fixed subgraph) also
> satisfies (*).

In our Moore57 setting, condition (*) corresponds to the strong (λ = 0,
μ = 1) common-neighbour structure. For a single σ ∈ Aut(Γ), the σ-fixed
induced subgraph inherits the strong (0, 1) property — this is
`autFixedInducedGraph_isStrongZeroOne` in
`Moore57.Moore57Graph.Aut.InducedSubgraph`.

The general subgroup case follows by intersecting fixed sets.
-/

open Moore57

namespace Moore57.Papers.Aschbacher1971

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- **Lemma 1.2 (Fix inherits strong (0,1)), single-element case.**
For any σ ∈ Aut(Γ), the σ-fixed induced subgraph satisfies the strong
(λ = 0, μ = 1) common-neighbour condition. -/
theorem lem1_2_fix_isStrongZeroOne (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (hAut : ∀ v w, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    IsStrongZeroOne (autFixedInducedGraph Γ σ) :=
  autFixedInducedGraph_isStrongZeroOne hΓ σ hAut

end Moore57.Papers.Aschbacher1971
