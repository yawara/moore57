import Moore57.Moore57Graph.Moore57Definition
import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Aut.SubgroupInducedSubgraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Aschbacher 1971, Lemma 1.2

> Let `𝒢` satisfy condition (*) (triangle-free, irreflexive 1-system,
> `d(A, B) ≤ 2`). Let `G ≤ Aut 𝒢`. Then `F(G)` (fixed subgraph) also
> satisfies (*).

In our Moore57 setting, condition (*) corresponds to the strong (λ = 0,
μ = 1) common-neighbour structure.

Status:
* Single-element case (`σ ∈ Aut(Γ)`): `lem1_2_fix_isStrongZeroOne`,
  wrapped from `autFixedInducedGraph_isStrongZeroOne`.
* Subgroup case (`G ≤ Aut(Γ)`): `lem1_2_fix_subgroup_isStrongZeroOne`,
  wrapped from `subgroupFixedInducedGraph_isStrongZeroOne`
  (`MulAction.fixedPoints G V` Mathlib native).
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

/-- **Lemma 1.2 (Fix inherits strong (0,1)), subgroup case.** [done]

For any finite subgroup `G ≤ Equiv.Perm V` whose elements are all graph
automorphisms of a Moore57 graph `Γ`, the induced subgraph on
`MulAction.fixedPoints G V` satisfies the strong `(λ=0, μ=1)`
common-neighbour condition.

Wraps `subgroupFixedInducedGraph_isStrongZeroOne`. -/
theorem lem1_2_fix_subgroup_isStrongZeroOne
    (hΓ : IsMoore57 Γ) (G : Subgroup (Equiv.Perm V)) [Fintype G]
    (hG : ∀ σ ∈ G, ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    IsStrongZeroOne (subgroupFixedInducedGraph Γ G) :=
  subgroupFixedInducedGraph_isStrongZeroOne hΓ G hG

end Moore57.Papers.Aschbacher1971
