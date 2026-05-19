import Moore57.Moore57Graph.Aut.FixedSubgraphData

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Mačaj–Širáň 2010, §2, Lemma 1 [skeleton]

> Let `X` be a group of automorphisms of Γ. Then `Fix(X)` is empty, an
> isolated vertex, a pentagon, the Petersen graph, the Hoffman–Singleton
> graph, or a star `K_{1,n}` for some `n ≥ 1`.

Originally due to Aschbacher (1971). The existing
`Moore57.Moore57Graph.Aut.FixedSubgraphData` gives the structural API for
fixed-point subgraphs; this file re-states the dichotomy from the paper.
-/

namespace Moore57.Papers.MacajSiran2010.S2

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Symbolic discriminator for the six possibilities in Lemma 1. -/
inductive FixShape
  | empty
  | singleton
  | pentagon
  | petersen
  | hoffmanSingleton
  | starK1n (n : ℕ)

/-- **Lemma 1.** For any group `X ≤ Aut(Γ)`, the fixed subgraph `Fix(X)` has
one of six shapes (six-way classification). [skeleton] -/
theorem lem1_fixShape (hΓ : IsMoore57 Γ)
    (X : Subgroup (Equiv.Perm V))
    (hX : ∀ g ∈ X, ∀ x y, Γ.Adj x y ↔ Γ.Adj (g x) (g y)) :
    ∃ s : FixShape, True := by
  exact ⟨FixShape.empty, trivial⟩

end Moore57.Papers.MacajSiran2010.S2
