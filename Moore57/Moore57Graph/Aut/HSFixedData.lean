import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Defs
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Moore57Definition

/-!
# Hoffman–Singleton fixed subgraph data (Tier C / §6 Lem 18 geometric input)

Data structure capturing "the σ-fixed-point subgraph of Γ is isomorphic to
the Hoffman–Singleton graph", matching the §6 Lemma 18 case (1) geometric
premise.

Unlike `PetersenFixedData`, we do not commit to an explicit construction of
the 50-vertex Hoffman–Singleton graph (which would require substantial work).
Instead we characterize the induced subgraph by its strongly regular
parameters `(50, 7, 0, 1)` — which by the Hoffman–Singleton classification
uniquely identify the graph up to isomorphism.

## Main definitions

* `HSFixedData Γ σ` — a `Fin 50` indexing of 50 distinct σ-fixed vertices
  spanning `Fix(σ)`, with induced adjacency satisfying the
  `(50, 7, 0, 1)`-SRG conditions.

## Connection to §6 Lemma 18

The §6 Lemma 18 case (1) reads: "if `Fix(X)` is the Hoffman–Singleton graph,
then `|X| ∣ 25`."  The arithmetic step (5-group + `|X| ∣ 50 ⟹ |X| ∣ 25`) is
proven in `Section06_PGroupsOverview.Lemma18_5Group`.  The remaining
geometric step is the divisibility `orderOf σ ∣ 50`, which follows from
`HSFixedData` via the semi-regular action of σ on
`N(a) \ Fix(σ)` (size 57 − 7 = 50).
-/

namespace Moore57

variable {V : Type*}

/-- The σ-fixed subgraph of Γ is "Hoffman–Singleton-shaped":
a `Fin 50`-indexed list of 50 distinct fixed vertices spanning `Fix(σ)`,
with induced adjacency satisfying the `(50, 7, 0, 1)`-strongly-regular
conditions.

Fields:
* `v : Fin 50 → V` — the 50 fixed vertices, indexed by `Fin 50`.
* `v_injective` — all 50 vertices are distinct.
* `v_fixed` — σ fixes each of them.
* `span` — σ has no other fixed points.
* `induced_regular` — each `v i` has exactly 7 neighbours among the other
  49 (induced degree 7).
* `induced_lambda` — adjacent `v i, v j` share `0` common neighbours
  (triangle-free, `ℓ = 0`).
* `induced_mu` — distinct non-adjacent `v i, v j` share exactly `1` common
  neighbour (`μ = 1`, the Moore-graph defining property).

By the Hoffman–Singleton classification (the unique `(50, 7, 0, 1)`-SRG up to
isomorphism), the induced subgraph is the Hoffman–Singleton graph. -/
structure HSFixedData (Γ : SimpleGraph V) (σ : Equiv.Perm V) where
  /-- 50 fixed vertices, indexed by `Fin 50`. -/
  v : Fin 50 → V
  /-- The 50 vertices are pairwise distinct. -/
  v_injective : Function.Injective v
  /-- σ fixes each of the 50 vertices. -/
  v_fixed : ∀ i : Fin 50, σ (v i) = v i
  /-- σ has no fixed points beyond `{v 0, …, v 49}`. -/
  span : ∀ x : V, σ x = x → ∃ i : Fin 50, x = v i
  /-- Each `v i` has exactly 7 neighbours among the other indexed vertices
  (induced regularity, `k = 7`). -/
  induced_regular : ∀ i : Fin 50,
    Set.ncard { j : Fin 50 | Γ.Adj (v i) (v j) } = 7
  /-- Adjacent `v i, v j` share `0` common indexed neighbours (`ℓ = 0`,
  the triangle-free / girth-5 condition). -/
  induced_lambda : ∀ i j : Fin 50, Γ.Adj (v i) (v j) →
    Set.ncard { k : Fin 50 | Γ.Adj (v i) (v k) ∧ Γ.Adj (v j) (v k) } = 0
  /-- Distinct non-adjacent `v i, v j` share exactly `1` common indexed
  neighbour (`μ = 1`, the Moore-graph defining property). -/
  induced_mu : ∀ i j : Fin 50, i ≠ j → ¬Γ.Adj (v i) (v j) →
    Set.ncard { k : Fin 50 | Γ.Adj (v i) (v k) ∧ Γ.Adj (v j) (v k) } = 1

namespace HSFixedData

variable {Γ : SimpleGraph V} {σ : Equiv.Perm V}

/-- The fixed-vertex finset has cardinality 50. -/
theorem card_fixed_vertices [DecidableEq V] (h : HSFixedData Γ σ) :
    (Finset.univ.image h.v).card = 50 := by
  rw [Finset.card_image_of_injective _ h.v_injective, Finset.card_univ,
      Fintype.card_fin]

/-- **HS induced regularity in Finset form**: each `v i` has exactly 7
neighbours among the other 49 indexed vertices.

This is the Finset-card form of the structure's `induced_regular` field
(which is stated using `Set.ncard`).  Used by the §6 Lem 18 bridge below. -/
theorem induced_degree_seven [DecidableRel Γ.Adj] (h : HSFixedData Γ σ)
    (i : Fin 50) :
    ((Finset.univ : Finset (Fin 50)).filter (fun j => Γ.Adj (h.v i) (h.v j))).card
      = 7 := by
  have hreg := h.induced_regular i
  rw [Set.ncard_eq_toFinset_card' _, Set.toFinset_setOf] at hreg
  exact hreg

/-- **HS bridge to `autFixedNeighborFinset`**: for σ with HS fixed-point
data, the σ-fixed neighbour count at any of the 50 fixed vertices equals
`7` (matching the Hoffman–Singleton induced degree).

This is the key bridge between `HSFixedData` and the §6 Lem 18 case (1)
geometric input: `|N(a) ∩ Fix(σ)| = 7` for a ∈ Fix(σ), hence
`|N(a) \ Fix(σ)| = 57 − 7 = 50` and σ acts semi-regularly on this 50-set, so
`orderOf σ ∣ 50`. -/
theorem autFixedNeighborFinset_card_eq_seven
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (h : HSFixedData Γ σ) (i : Fin 50) :
    (autFixedNeighborFinset Γ σ (h.v i)).card = 7 := by
  have heq :
      autFixedNeighborFinset Γ σ (h.v i)
        = ((Finset.univ : Finset (Fin 50)).filter
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
  exact h.induced_degree_seven i

/-- **HS complement neighbour count**: for σ with HS fixed-point data on a
Moore57 graph, the σ-moved neighbour count at any of the 50 fixed vertices
equals `50 = 57 − 7`.

Combines `autFixedNeighborFinset_card_eq_seven` (`|N(a) ∩ Fix(σ)| = 7`) with
the Moore57 regular degree (`|N(a)| = 57`).  This is the §6 Lem 18 case (1)
semi-regular orbit input: σ acts on a 50-element set (without fixed points),
and the orbit-stabilizer argument gives `orderOf σ ∣ 50`. -/
theorem hsFixedData_complement_neighbor_count
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : HSFixedData Γ σ) (i : Fin 50) :
    ((Γ.neighborFinset (h.v i)).filter (fun w => σ w ≠ w)).card = 50 := by
  have h57 : (Γ.neighborFinset (h.v i)).card = 57 := by
    have := hΓ.regular.degree_eq (h.v i)
    rwa [SimpleGraph.degree] at this
  have h7 : ((Γ.neighborFinset (h.v i)).filter (fun w => σ w = w)).card = 7 :=
    h.autFixedNeighborFinset_card_eq_seven i
  have hsum := Finset.card_filter_add_card_filter_not (s := Γ.neighborFinset (h.v i))
    (p := fun w => σ w = w)
  change ((Γ.neighborFinset (h.v i)).filter (fun w => ¬ σ w = w)).card = 50
  omega

end HSFixedData

end Moore57
