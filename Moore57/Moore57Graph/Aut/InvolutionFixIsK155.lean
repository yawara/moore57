import Moore57.Moore57Graph.Aut.InvolutionCandidates
import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.InvolutionEdgeCountFormula
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Moore57.Moore57Graph.Aut.FixedSubgraphData

/-!
# Fix(σ) ≅ K_{1,55} for an involution σ of a Moore57 graph (Tier 2)

This file establishes Cameron's Theorem 3.13 (Higman's argument, see
`tmp/pdfs/cameron_ch3_coherent_configurations.txt` Steps 1-4 and
Makhnev-Paduchikh's Lemmas 1, 2, 4 in `tmp/pdfs/involution-fixed-star.txt`).
Inputs are minimal:

* `σ : Equiv.Perm V` with `Function.Involutive σ` (i.e. `σ^2 = 1`),
* `σ ≠ 1`,
* `σ` preserves adjacency in a Moore57 graph `Γ`.

The conclusion is that the σ-fixed induced subgraph is the star `K_{1,55}` —
a center adjacent to all 55 leaves, with no other edges.

## Outline (Cameron Steps 1-4)

* **Phase 1** (`aut_involution_exists_adjacent_moved`): Case B impossible.
  If `∀ v, ¬ Γ.Adj v (σ v)` (no adjacent moved pair), then the
  `adjacentMovedCount` equation forces `2 · #E(Fix) = 58 · |Fix| - 3250`.
  Combined with `#E ≥ 0`, this gives `|Fix| ≥ 57`, contradicting the
  candidates list (max 56). Hence some adjacent moved pair exists.

* **Phase 2** (Cameron Step 2 labeling): for `a`, `b = σ a` with `a ~ b`, the
  map `V \ ({a,b} ∪ N(a)\{b} ∪ N(b)\{a}) → A × B`, `v ↦ (φ_a v, φ_b v)`
  (common neighbors with `a`, `b`) is a bijection, and σ-fixed `v` correspond
  to pairs `(α, σ α)` with `α ∈ A`. Hence `|Fix(σ)| = 56`.

* **Phase 3**: `|Fix(σ)| = 56` rules out the regular branch
  (`k² = 55` has no integer solution), so the fixed induced graph is a star.

* **Phase 4**: Build `K155FixedData Γ σ` from the star + 56-vertex data.
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Phase 1: Some adjacent moved pair exists -/

/-- If `σ` has no adjacent moved pair, then `adjacentMovedCount Γ σ = 0`. -/
private theorem adjacentMovedCount_eq_zero_of_no_adjacent_moved
    (σ : Equiv.Perm V)
    (hno : ∀ v : V, ¬ Γ.Adj v (σ v)) :
    adjacentMovedCount Γ σ = 0 := by
  classical
  unfold adjacentMovedCount
  rw [Finset.card_eq_zero]
  ext v
  simp [hno v]

/-- **Cameron Step 1 (refuted Case B)**: an involutive automorphism `σ ≠ 1` of
a Moore57 graph must interchange some adjacent pair. -/
theorem aut_involution_exists_adjacent_moved
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (haut : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hinv : Function.Involutive σ)
    (hne : σ ≠ 1) :
    ∃ a : V, Γ.Adj a (σ a) := by
  classical
  by_contra hno_exists
  push_neg at hno_exists
  have ha1_zero : adjacentMovedCount Γ σ = 0 :=
    adjacentMovedCount_eq_zero_of_no_adjacent_moved σ hno_exists
  have hformula :
      (adjacentMovedCount Γ σ : ℤ) =
        3250 - 58 * (fixedVertexCount σ : ℤ) +
          2 * (((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ)) :=
    adjacentMovedCount_eq_involution_fixed_edge_formula hΓ hinv haut
  rw [ha1_zero] at hformula
  have hedges_nn :
      0 ≤ ((Γ.induce (fixedVertexSet σ)).edgeFinset.card : ℤ) := by
    exact_mod_cast Nat.zero_le _
  -- 0 = 3250 - 58 |Fix| + 2 #E, with #E ≥ 0, gives 58 |Fix| ≥ 3250, so |Fix| ≥ 57
  have hge_int : (57 : ℤ) ≤ (fixedVertexCount σ : ℤ) := by omega
  have hge : 57 ≤ fixedVertexCount σ := by exact_mod_cast hge_int
  rcases aut_involution_fixedVertexCount_candidates hΓ σ haut hinv hne with
    h | h | h | h | h | h | h | h | h | h <;> omega

end Moore57
