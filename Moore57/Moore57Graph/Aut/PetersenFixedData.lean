import Moore57.Foundations.GraphTheory.PetersenGraph
import Moore57.Foundations.GraphTheory.PetersenUniqueness
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Aut.SemiRegularComplement
import Moore57.Moore57Graph.Aut.InducedSubgraph
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupAction.FixedPoints

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

/-- **Petersen `fixedVertexCount = 10`**: the σ-fixed-vertex count
equals `10`. -/
theorem fixedVertexCount_eq_10
    [Fintype V] [DecidableEq V] (h : PetersenFixedData Γ σ) :
    fixedVertexCount σ = 10 := by
  unfold fixedVertexCount
  have heq :
      ((Finset.univ : Finset V).filter (fun w => σ w = w))
        = (Finset.univ : Finset (Fin 10)).image h.v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hfix
      obtain ⟨i, hi⟩ := h.span w hfix
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact h.v_fixed i
  rw [heq, Finset.card_image_of_injective _ h.v_injective, Finset.card_univ,
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

/-- **Induced triangle-free**: any three fixed vertices indexed by Petersen do
not form a triangle.

This is the §6 Lem 17 case (1) input encoding "the σ-fixed induced subgraph
is triangle-free" (since Petersen is `λ = 0`).  Derived directly from
`induced_adj_iff` and `petersenGraph_triangleFree`. -/
theorem induced_triangleFree (h : PetersenFixedData Γ σ) :
    ∀ i j k : Fin 10, Γ.Adj (h.v i) (h.v j) → Γ.Adj (h.v j) (h.v k) →
      Γ.Adj (h.v i) (h.v k) → False := by
  intro i j k hij hjk hik
  rw [h.induced_adj_iff] at hij hjk hik
  exact petersenGraph_triangleFree i j k hij hjk hik

/-- **Induced no 4-cycle**: four distinct fixed vertices (with `i ≠ k` and
`j ≠ l`) cannot form a 4-cycle.

Derived from `induced_adj_iff` and `petersenGraph_no_C4` (Petersen has girth
5). -/
theorem induced_no_C4 (h : PetersenFixedData Γ σ) :
    ∀ i j k l : Fin 10, i ≠ k → j ≠ l →
      Γ.Adj (h.v i) (h.v j) → Γ.Adj (h.v j) (h.v k) →
      Γ.Adj (h.v k) (h.v l) → Γ.Adj (h.v l) (h.v i) → False := by
  intro i j k l hik hjl hij hjk hkl hli
  rw [h.induced_adj_iff] at hij hjk hkl hli
  exact petersenGraph_no_C4 i j k l hik hjl hij hjk hkl hli

/-- **Induced ordered adjacency pair count**: among the 100 ordered pairs of
fixed-vertex indices, exactly 30 are Γ-adjacent (matching Petersen's
`2 · |E| = 30`).

This is the bridge to `petersenGraph_edgeFinset_card` at the `PetersenFixedData`
level: the σ-fixed induced subgraph has exactly 15 edges (since 30 ordered
pairs = 15 unordered edges via symmetry). -/
theorem induced_adj_pairs_card_eq_30 [DecidableRel Γ.Adj]
    (h : PetersenFixedData Γ σ) :
    ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
      (fun p => Γ.Adj (h.v p.1) (h.v p.2))).card = 30 := by
  have hcong :
      ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
        (fun p => Γ.Adj (h.v p.1) (h.v p.2)))
        = ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
            (fun p => petersenGraph.Adj p.1 p.2)) := by
    apply Finset.filter_congr
    intro p _
    exact h.induced_adj_iff p.1 p.2
  rw [hcong]
  decide

/-- **Petersen semi-regular orbit bridge**: for σ with `PetersenFixedData`
on a Moore57 graph and `σ` acting semi-regularly on `N(a) \ Fix(σ)`,
`orderOf σ ∣ 54`.

This is the [C3.4] semi-regular orbit argument specialised to the
Petersen case (Lem 17 case (1) input).  The semi-regular hypothesis is
phrased as: every non-trivial power of σ moves every element of
`N(a) \ Fix(σ)`.

Combined with `petersenFixedData_complement_neighbor_count` (= 54) and
the general `orderOf_dvd_card_movedNeighbour_of_semiRegular` bridge, the
conclusion is unconditional on the semi-regular assumption. -/
theorem petersen_orderOf_dvd_54_of_semiRegular
    [Fintype V] [DecidableEq V] [DecidableRel Γ.Adj]
    (hΓ : IsMoore57 Γ) (h : PetersenFixedData Γ σ) (i : Fin 10)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (hsemi : ∀ w ∈ autMovedNeighborFinset Γ σ (h.v i),
             ∀ k : ℕ, (σ^k) w = w → orderOf σ ∣ k) :
    orderOf σ ∣ 54 := by
  have hcard : (autMovedNeighborFinset Γ σ (h.v i)).card = 54 :=
    h.petersenFixedData_complement_neighbor_count hΓ i
  exact hcard ▸ orderOf_dvd_card_movedNeighbour_of_semiRegular
    σ smul_adj (h.v_fixed i) hsemi

end PetersenFixedData

/-! ## Conditional bridge from `IsSRGWith 10 3 0 1` to `PetersenFixedData`

The §6 Lem 17 case (1) shape dispatch (`OrderThreeShapeClassification.lean`,
`aut_order_three_SingletonOrPetersenSRG_unconditional`) produces
`IsSRGWith 10 3 0 1` on the σ-fixed induced subgraph, **not** an explicit
`PetersenFixedData`.  Promoting from the SRG signature to
`PetersenFixedData` requires a graph isomorphism to the explicit
`petersenGraph`, i.e., the Petersen uniqueness theorem.

The constructor `petersenFixedData_of_iso_to_petersen` below performs this
promotion **given an explicit graph isomorphism**.  The full conditional
dispatch consumes `PetersenUniqueness` (from
`Moore57.Foundations.GraphTheory.PetersenUniqueness`) to extract such an
isomorphism non-canonically.
-/

/-- **`PetersenFixedData` from an explicit iso to the explicit `petersenGraph`.**

Given:
* `Γ` a graph and `σ` a permutation,
* `smul_adj` (σ is a graph automorphism — actually unused here, but kept
  in the API surface for symmetry with §6 Lem 17 dispatch entry points),
* a graph isomorphism
  `φ : autFixedInducedGraph Γ σ ≃g petersenGraph`,

construct the `PetersenFixedData Γ σ` structure.  The 10 vertices are
extracted from `φ.symm` (i.e., the inverse iso sends `Fin 10` indices
back to vertices of `fixedVertexSet σ`, then projected to `V`).

This is the **non-canonical** part of the bridge: distinct isomorphisms
yield distinct `PetersenFixedData` records (differing by the
`Aut(petersenGraph) = S_5` choice). -/
noncomputable def petersenFixedData_of_iso_to_petersen
    [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {σ : Equiv.Perm V}
    (φ : autFixedInducedGraph Γ σ ≃g petersenGraph) :
    PetersenFixedData Γ σ where
  v i := (φ.symm i : V)
  v_injective := by
    intro i j hij
    -- `φ.symm i = φ.symm j` as elements of `V` ⟹ as `fixedVertexSet σ`
    -- (Subtype.ext) ⟹ as `Fin 10` (φ.symm injective).
    have hsub : φ.symm i = φ.symm j := Subtype.ext hij
    exact φ.symm.injective hsub
  v_fixed i := (φ.symm i).property
  span x hx := by
    -- Every σ-fixed `x : V` lies in `fixedVertexSet σ`, so `φ ⟨x, hx⟩ : Fin 10`
    -- pulls back to `x` via `φ.symm`.
    refine ⟨φ ⟨x, hx⟩, ?_⟩
    -- `(φ.symm (φ ⟨x, hx⟩) : V) = (⟨x, hx⟩ : fixedVertexSet σ).val = x`
    have hroundtrip : φ.symm (φ ⟨x, hx⟩) = (⟨x, hx⟩ : fixedVertexSet σ) :=
      φ.symm_apply_apply ⟨x, hx⟩
    -- Project to V.
    have : (φ.symm (φ ⟨x, hx⟩) : V) = x := by
      rw [hroundtrip]
    exact this.symm
  induced_adj_iff i j := by
    -- `Γ.Adj (φ.symm i) (φ.symm j)` ⇔ `(autFixedInducedGraph Γ σ).Adj (φ.symm i) (φ.symm j)`
    -- ⇔ (via φ.map_adj_iff) `petersenGraph.Adj i j`.
    have hsub :
        (autFixedInducedGraph Γ σ).Adj (φ.symm i) (φ.symm j)
          ↔ Γ.Adj (φ.symm i : V) (φ.symm j : V) :=
      autFixedInducedGraph_adj σ
    have hiso : petersenGraph.Adj i j ↔
        (autFixedInducedGraph Γ σ).Adj (φ.symm i) (φ.symm j) := by
      have := φ.symm.map_adj_iff (v := i) (w := j)
      simpa using this.symm
    rw [← hsub, ← hiso]

/-- **Conditional `PetersenFixedData` constructor via Petersen uniqueness.**

Given:
* `hΓ : IsMoore57 Γ`,
* `σ` an automorphism (`smul_adj`) with `IsSRGWith 10 3 0 1` on its
  σ-fixed induced subgraph,
* the Petersen uniqueness Prop (`PetersenUniqueness` —
  `Moore57.Foundations.GraphTheory.PetersenUniqueness`),

produce `PetersenFixedData Γ σ`.

The construction extracts a (non-canonical) iso from the uniqueness Prop
via `Classical.choice`, then delegates to
`petersenFixedData_of_iso_to_petersen`.

This is the **paper-conditional** part of the §6 Lem 17 case (1) bridge:
given Petersen uniqueness, the SRG-signature output of
`aut_order_three_SingletonOrPetersenSRG_unconditional` can be promoted to
the full `PetersenFixedData` structure consumed by the Lem 17 case (1)
arithmetic dispatch. -/
noncomputable def petersenFixedData_of_isSRGWith_given_uniqueness
    [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {σ : Equiv.Perm V}
    (h_unique : PetersenUniqueness)
    (h_srg : (autFixedInducedGraph Γ σ).IsSRGWith 10 3 0 1) :
    PetersenFixedData Γ σ :=
  letI : Fintype (fixedVertexSet σ) := fixedVertexSet.fintype σ
  letI : DecidableEq (fixedVertexSet σ) := Subtype.instDecidableEq
  let φ : autFixedInducedGraph Γ σ ≃g petersenGraph :=
    Classical.choice (h_unique (autFixedInducedGraph Γ σ) h_srg)
  petersenFixedData_of_iso_to_petersen φ

end Moore57
