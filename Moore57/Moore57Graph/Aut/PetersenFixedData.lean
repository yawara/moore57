import Moore57.Foundations.GraphTheory.PetersenGraph
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Moore57Definition

/-!
# Petersen fixed subgraph data (Tier C / §6 Lem 17 geometric input)

Data structure capturing "the σ-fixed-point subgraph of Γ is isomorphic to
the Petersen graph", matching the §6 Lemma 17 case (1) geometric premise.

This file mirrors `Moore57.Moore57Graph.Aut.FixedSubgraphData` (which defines
`C5FixedData` and `K155FixedData` for the 5-cycle and `K_{1,55}` cases of
Aschbacher's Lemma 1) for the Petersen case.

## Main definitions

* `PetersenFixedData Γ σ` — a `Fin 10` indexing of 10 distinct σ-fixed
  vertices spanning `Fix(σ)`, with induced adjacency matching the explicit
  `petersenGraph` (`Moore57.Foundations.GraphTheory.PetersenGraph`).

## Connection to §6 Lemma 17

The §6 Lemma 17 case (1) reads: "if `Fix(X)` is the Petersen graph, then
`|X| ∣ 27`."  The arithmetic step (3-group + `|X| ∣ 54 ⟹ |X| ∣ 27`) is
proven in `Section06_PGroupsOverview.Lemma17_3Group`.  The remaining
geometric step is the divisibility `orderOf σ ∣ 54`, which follows from
`PetersenFixedData` via the semi-regular action of σ on
`N(a) \ Fix(σ)` (size 57 − 3 = 54).

The bridge lemma `petersenFixedData_complement_size` records this
elementary count.
-/

namespace Moore57

variable {V : Type*}

/-- The σ-fixed subgraph of Γ is "Petersen-shaped":
a `Fin 10`-indexed list of 10 distinct fixed vertices spanning `Fix(σ)`,
with induced adjacency matching the explicit `petersenGraph`.

Fields:
* `v : Fin 10 → V` — the 10 fixed vertices, indexed by `Fin 10`.
* `v_injective` — all 10 vertices are distinct.
* `v_fixed` — σ fixes each of them.
* `span` — σ has no other fixed points.
* `induced_adj_iff` — the induced subgraph on `{v 0, …, v 9}` agrees with
  the explicit `petersenGraph` (via the index identification). -/
structure PetersenFixedData (Γ : SimpleGraph V) (σ : Equiv.Perm V) where
  /-- 10 fixed vertices, indexed by `Fin 10` (matching the
  `petersenGraph` indexing: outer pentagon = 0–4, inner pentagram = 5–9). -/
  v : Fin 10 → V
  /-- The 10 vertices are pairwise distinct. -/
  v_injective : Function.Injective v
  /-- σ fixes each of the 10 vertices. -/
  v_fixed : ∀ i : Fin 10, σ (v i) = v i
  /-- σ has no fixed points beyond `{v 0, …, v 9}`. -/
  span : ∀ x : V, σ x = x → ∃ i : Fin 10, x = v i
  /-- The induced subgraph on `{v 0, …, v 9}` matches the explicit Petersen
  graph (after identifying indices via `v`). -/
  induced_adj_iff : ∀ i j : Fin 10, Γ.Adj (v i) (v j) ↔ petersenGraph.Adj i j

namespace PetersenFixedData

variable {Γ : SimpleGraph V} {σ : Equiv.Perm V}

/-- The fixed-vertex finset has cardinality 10. -/
theorem card_fixed_vertices [DecidableEq V] (h : PetersenFixedData Γ σ) :
    (Finset.univ.image h.v).card = 10 := by
  rw [Finset.card_image_of_injective _ h.v_injective, Finset.card_univ,
      Fintype.card_fin]

/-- **Petersen induced regularity**: each `v i` has exactly 3 neighbours
among the other 9 indexed vertices, mirroring the `petersenGraph` degree. -/
theorem induced_degree_three [DecidableRel Γ.Adj] (h : PetersenFixedData Γ σ)
    (i : Fin 10) :
    ((Finset.univ : Finset (Fin 10)).filter (fun j => Γ.Adj (v h i) (v h j))).card
      = 3 := by
  have hcong :
      ((Finset.univ : Finset (Fin 10)).filter (fun j => Γ.Adj (v h i) (v h j)))
        = ((Finset.univ : Finset (Fin 10)).filter (fun j => petersenGraph.Adj i j)) := by
    apply Finset.filter_congr
    intro j _
    exact h.induced_adj_iff i j
  rw [hcong]
  -- Petersen graph is 3-regular: degree i = 3.
  have hdeg : petersenGraph.degree i = 3 := petersenGraph_regular i
  -- degree = (neighborFinset i).card = (univ.filter (Adj i)).card.
  unfold SimpleGraph.degree at hdeg
  rw [SimpleGraph.neighborFinset_def] at hdeg
  rw [← hdeg]
  congr 1
  ext j
  simp [SimpleGraph.mem_neighborSet]

/-- **Petersen bridge to `autFixedNeighborFinset`**: for σ with Petersen
fixed-point data, the σ-fixed neighbour count at any of the 10 fixed vertices
equals `3` (matching `petersenGraph`'s degree).

This is the key bridge between `PetersenFixedData` and the §6 Lem 17 case (1)
geometric input: `|N(a) ∩ Fix(σ)| = 3` for a ∈ Fix(σ), hence
`|N(a) \ Fix(σ)| = 57 − 3 = 54` and σ acts semi-regularly on this 54-set, so
`orderOf σ ∣ 54`. -/
theorem autFixedNeighborFinset_card_eq_three
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : PetersenFixedData Γ σ) (i : Fin 10) :
    (autFixedNeighborFinset Γ σ (h.v i)).card = 3 := by
  -- Rewrite autFixedNeighborFinset as the image of {j : Γ.Adj (v i) (v j)} under v.
  have heq :
      autFixedNeighborFinset Γ σ (h.v i)
        = ((Finset.univ : Finset (Fin 10)).filter
            (fun j => Γ.Adj (h.v i) (h.v j))).image h.v := by
    ext w
    simp only [mem_autFixedNeighborFinset, Finset.mem_image, Finset.mem_filter,
               Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hadj, hfix⟩
      obtain ⟨j, hj⟩ := h.span w hfix
      exact ⟨j, hj ▸ hadj, hj.symm⟩
    · rintro ⟨j, hadj, rfl⟩
      exact ⟨hadj, h.v_fixed j⟩
  rw [heq, Finset.card_image_of_injective _ h.v_injective]
  exact h.induced_degree_three i

/-- **Petersen complement neighbour count**: for σ with Petersen fixed-point
data on a Moore57 graph, the σ-moved neighbour count at any of the 10 fixed
vertices equals `54 = 57 − 3`.

Combines `autFixedNeighborFinset_card_eq_three` (`|N(a) ∩ Fix(σ)| = 3`) with
the Moore57 regular degree (`|N(a)| = 57`).  This is the §6 Lem 17 case (1)
semi-regular orbit input: σ acts on a 54-element set (without fixed points),
and the orbit-stabilizer argument gives `orderOf σ ∣ 54`. -/
theorem petersenFixedData_complement_neighbor_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : PetersenFixedData Γ σ) (i : Fin 10) :
    ((Γ.neighborFinset (h.v i)).filter (fun w => σ w ≠ w)).card = 54 := by
  have h57 : (Γ.neighborFinset (h.v i)).card = 57 := by
    have := hΓ.regular.degree_eq (h.v i)
    rwa [SimpleGraph.degree] at this
  have h3 : ((Γ.neighborFinset (h.v i)).filter (fun w => σ w = w)).card = 3 :=
    h.autFixedNeighborFinset_card_eq_three i
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset (h.v i))
    (p := fun w => σ w = w)
  change ((Γ.neighborFinset (h.v i)).filter (fun w => ¬ σ w = w)).card = 54
  omega

end PetersenFixedData

end Moore57
