import Moore57.Foundations.GraphTheory.PetersenAuxiliary

/-!
# Bose 1963 strangers-partition lemmas for `IsPetersenLike`

This file continues the structural development of `IsPetersenLike` graphs
(SRGs with parameters `(10, 3, 0, 1)`) toward Bose 1963's enumeration of
Petersen-like graphs.

The central object is the **strangers partition** of a vertex `v`:

* `v` itself (1 vertex);
* the open neighbourhood `N(v)` (3 vertices, an independent set);
* the *strangers* of `v` — `univ \ ({v} ∪ N(v))` — 6 vertices that are
  neither `v` nor neighbours of `v`.

The 6 strangers further partition into **three pairs**, indexed by the
three neighbours `z ∈ N(v)`.  For each `z`, the pair is `N(z) \ {v}` (the
two non-`v` neighbours of `z`).  By `λ = 0`, those vertices cannot be
adjacent to `v`, so they are strangers; by `μ = 1`, each stranger has a
unique common neighbour with `v` (which must lie in `N(v)`), so the
assignment of strangers to neighbours of `v` is a bijection from
strangers onto pairs over `N(v)`.

This is the 3-by-6 vertex incidence at the heart of Bose 1963: each
edge `(v, w)` of `G` gives rise to a `K_{3,3}`-minus-a-matching structure
between `N(v) \ {w}` and `N(w) \ {v}`, with each stranger of `v`
attached to exactly one `z ∈ N(v)`.

## Main definitions

* `strangers G v` — the finset `Finset.univ \ insert v (G.neighborFinset v)`.
* `partnersOf G v z` — for `z ∈ N(v)`, the finset `(G.neighborFinset z).erase v`.

## Main results

* `IsPetersenLike.strangers_card` — `(strangers G v).card = 6`.
* `IsPetersenLike.partnersOf_card` — `(partnersOf G v z).card = 2` for
  `z ∈ N(v)`.
* `IsPetersenLike.partnersOf_subset_strangers` — each partner is a
  stranger.
* `IsPetersenLike.partnersOf_pairwise_disjoint` — the partners of
  distinct neighbours of `v` are disjoint (μ = 1 uniqueness).
* `IsPetersenLike.strangers_eq_biUnion_partnersOf` — the 6 strangers
  decompose as the disjoint union of the three `partnersOf` pairs.
* `IsPetersenLike.unique_neighborOf_v_adjacent_to_stranger` — each
  stranger `u` of `v` has a unique `z ∈ N(v)` with `G.Adj z u`.

## References

Bose, R. C., "Strongly regular graphs, partial geometries and partially
balanced designs," Pacific J. Math. 13 (1963), 389-419.
-/

namespace Moore57

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-- **Strangers of a vertex.**

The finset of vertices that are neither `v` itself nor a neighbour
of `v`.  Has cardinality 6 in a Petersen-like graph. -/
def strangers (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (Finset.univ : Finset V) \ insert v (G.neighborFinset v)

/-- **Partners of a vertex `v` via a neighbour `z`.**

For `z ∈ N(v)`, the partners are `N(z) \ {v}`, i.e., the neighbours of
`z` other than `v`.  Since `G` has degree 3, this is a 2-element set.
In a Petersen-like graph, all elements lie in `strangers G v` (no
triangle through the edge `(v, z)`). -/
def partnersOf (G : SimpleGraph V) [DecidableRel G.Adj] (v z : V) : Finset V :=
  (G.neighborFinset z).erase v

/-- **Membership in `strangers`** — characterization. -/
theorem mem_strangers_iff {G : SimpleGraph V} [DecidableRel G.Adj] {v u : V} :
    u ∈ strangers G v ↔ u ≠ v ∧ ¬ G.Adj v u := by
  unfold strangers
  simp [Finset.mem_sdiff, Finset.mem_insert, SimpleGraph.mem_neighborFinset]

/-- **Membership in `partnersOf`** — characterization. -/
theorem mem_partnersOf_iff {G : SimpleGraph V} [DecidableRel G.Adj] {v z u : V} :
    u ∈ partnersOf G v z ↔ u ≠ v ∧ G.Adj z u := by
  unfold partnersOf
  rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]

/-- **`strangers G v` has cardinality 6** (Bose 1963 vertex partition). -/
theorem IsPetersenLike.strangers_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) : (strangers G v).card = 6 :=
  h.non_neighborhood_card v

/-- **`partnersOf G v z` has cardinality 2 when `z ∈ N(v)`.**

By `degree_eq_three`, `|N(z)| = 3`; erasing one element (`v`) gives 2.
-/
theorem IsPetersenLike.partnersOf_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v z : V} (hadj : G.Adj v z) :
    (partnersOf G v z).card = 2 := by
  have hv_mem : v ∈ G.neighborFinset z := by
    rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm
  have hcard := h.neighborFinset_card z
  unfold partnersOf
  rw [Finset.card_erase_of_mem hv_mem, hcard]

/-- **Partners of `z ∈ N(v)` are strangers of `v`.**

By `λ = 0` (no triangle through the edge `(v, z)`), every neighbour
of `z` other than `v` is not adjacent to `v`, hence a stranger. -/
theorem IsPetersenLike.partnersOf_subset_strangers
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v z : V} (hadj : G.Adj v z) :
    partnersOf G v z ⊆ strangers G v := by
  intro u hu
  rw [mem_partnersOf_iff] at hu
  obtain ⟨hne_uv, hzu⟩ := hu
  rw [mem_strangers_iff]
  refine ⟨hne_uv, ?_⟩
  intro hvu
  -- `z` is a common neighbour of `v` and `u`, contradicting `λ = 0`.
  exact h.no_triangle_through_edge hvu z ⟨hadj, hzu.symm⟩

/-- **Distinct neighbours of `v` give disjoint partner pairs** (`μ = 1`).

If `z₁, z₂ ∈ N(v)` are distinct and `u` is a common partner of both,
then both `z₁` and `z₂` are common neighbours of `v` and `u`, but
`μ = 1` (or `λ = 0` if `v = u`) forces uniqueness. -/
theorem IsPetersenLike.partnersOf_disjoint
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v z₁ z₂ : V}
    (hadj₁ : G.Adj v z₁) (hadj₂ : G.Adj v z₂) (hne : z₁ ≠ z₂) :
    Disjoint (partnersOf G v z₁) (partnersOf G v z₂) := by
  rw [Finset.disjoint_left]
  intro u hu₁ hu₂
  rw [mem_partnersOf_iff] at hu₁ hu₂
  obtain ⟨hne_uv, hz₁u⟩ := hu₁
  obtain ⟨_, hz₂u⟩ := hu₂
  -- We have G.Adj z₁ u and G.Adj z₂ u, with z₁ ≠ z₂.
  -- Also we know u ≠ v (so v ≠ u).
  -- We need to deduce a contradiction.
  -- If G.Adj v u: triangle v -- z₁ -- u -- v via λ = 0.
  by_cases hvu : G.Adj v u
  · exact h.triangleFree v z₁ u hadj₁ hz₁u hvu
  · -- v ≠ u (since u ≠ v) and ¬ G.Adj v u: then v, u share μ = 1 common neighbours.
    -- z₁ and z₂ are two distinct common neighbours of v and u: contradiction.
    have hne_vu : v ≠ u := fun h => hne_uv h.symm
    have hexists := h.exists_unique_commonNeighbor v u hne_vu hvu
    obtain ⟨z, _, hzunique⟩ := hexists
    have h1 := hzunique z₁ ⟨hadj₁, hz₁u.symm⟩
    have h2 := hzunique z₂ ⟨hadj₂, hz₂u.symm⟩
    exact hne (h1.trans h2.symm)

/-- **Every stranger of `v` has a (unique) common neighbour in `N(v)`.**

By `μ = 1`, each stranger `u` (so `u ≠ v` and `¬ G.Adj v u`) shares
exactly one neighbour with `v`, which by construction lies in `N(v)`. -/
theorem IsPetersenLike.exists_unique_neighbor_witness
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v u : V} (hu : u ∈ strangers G v) :
    ∃! z, z ∈ G.neighborFinset v ∧ G.Adj z u := by
  rw [mem_strangers_iff] at hu
  obtain ⟨hne_uv, hvu_nadj⟩ := hu
  have hne_vu : v ≠ u := fun h => hne_uv h.symm
  obtain ⟨z, ⟨hvz, huz⟩, hzunique⟩ :=
    h.exists_unique_commonNeighbor v u hne_vu hvu_nadj
  refine ⟨z, ⟨?_, huz.symm⟩, ?_⟩
  · rw [SimpleGraph.mem_neighborFinset]; exact hvz
  · intro z' ⟨hz'_mem, hz'u⟩
    rw [SimpleGraph.mem_neighborFinset] at hz'_mem
    exact hzunique z' ⟨hz'_mem, hz'u.symm⟩

/-- **The biUnion of `partnersOf` over `N(v)` covers all strangers.**

By the previous lemma, every stranger `u` is adjacent to some
`z ∈ N(v)`.  Hence `u ∈ partnersOf G v z`. -/
theorem IsPetersenLike.strangers_subset_biUnion_partnersOf
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    strangers G v ⊆ (G.neighborFinset v).biUnion (partnersOf G v) := by
  intro u hu
  have hu_copy := hu
  rw [mem_strangers_iff] at hu_copy
  obtain ⟨hne_uv, _⟩ := hu_copy
  obtain ⟨z, ⟨hz_mem, hzu⟩, _⟩ := h.exists_unique_neighbor_witness hu
  rw [Finset.mem_biUnion]
  refine ⟨z, hz_mem, ?_⟩
  rw [mem_partnersOf_iff]
  exact ⟨hne_uv, hzu⟩

/-- **The biUnion of `partnersOf` over `N(v)` lies inside `strangers`.**

Each `partnersOf G v z` for `z ∈ N(v)` lies inside `strangers G v` by
`partnersOf_subset_strangers`. -/
theorem IsPetersenLike.biUnion_partnersOf_subset_strangers
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    (G.neighborFinset v).biUnion (partnersOf G v) ⊆ strangers G v := by
  intro u hu
  rw [Finset.mem_biUnion] at hu
  obtain ⟨z, hz_mem, hu_part⟩ := hu
  rw [SimpleGraph.mem_neighborFinset] at hz_mem
  exact h.partnersOf_subset_strangers hz_mem hu_part

/-- **`strangers G v` equals the disjoint union of `partnersOf G v z`
for `z ∈ N(v)`.**

Combines the two inclusions: each stranger is partnered with exactly one
`z ∈ N(v)`, and each partner of `z` is a stranger.  This is the central
Bose 1963 incidence. -/
theorem IsPetersenLike.strangers_eq_biUnion_partnersOf
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    strangers G v = (G.neighborFinset v).biUnion (partnersOf G v) := by
  apply Finset.Subset.antisymm
  · exact h.strangers_subset_biUnion_partnersOf v
  · exact h.biUnion_partnersOf_subset_strangers v

/-- **Pairwise disjointness of `partnersOf` indexed by `N(v)`.**

The neighbours of `v` are pairwise distinct (as elements of a set), and
the partner sets are pairwise disjoint by `μ = 1`.  Packaged as a
`Set.PairwiseDisjoint` over the coercion of `G.neighborFinset v`. -/
theorem IsPetersenLike.partnersOf_pairwiseDisjoint
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    ((G.neighborFinset v : Set V)).PairwiseDisjoint (partnersOf G v) := by
  intro z₁ hz₁ z₂ hz₂ hne
  simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hz₁ hz₂
  exact h.partnersOf_disjoint hz₁ hz₂ hne

/-- **Stranger-partition cardinality identity** (Bose 1963 "3 × 2 = 6").

The strangers of `v` decompose as the disjoint union of three pairs
(one per neighbour of `v`), each of cardinality 2; total = 6 = `|strangers|`.
This is the algebraic core of Bose 1963's enumeration of the
Petersen-like incidence structure. -/
theorem IsPetersenLike.strangers_card_via_partnersOf
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    ∑ z ∈ G.neighborFinset v, (partnersOf G v z).card = 6 := by
  have hcard_biUnion :
      ((G.neighborFinset v).biUnion (partnersOf G v)).card =
        ∑ z ∈ G.neighborFinset v, (partnersOf G v z).card :=
    Finset.card_biUnion (h.partnersOf_pairwiseDisjoint v)
  rw [← hcard_biUnion, ← h.strangers_eq_biUnion_partnersOf]
  exact h.strangers_card v

/-- **Each stranger of `v` has a unique 2-path through some `z ∈ N(v)`.**

For a stranger `u`, there is exactly one neighbour `z` of `v` such that
`G.Adj z u`.  This is the constructive form of the Bose 1963 incidence:
each "non-edge" `(v, u)` is realised by a unique 2-path `v — z — u`. -/
theorem IsPetersenLike.stranger_unique_2path
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v u : V} (hu : u ∈ strangers G v) :
    ∃! z, z ∈ G.neighborFinset v ∧ G.Adj z u :=
  h.exists_unique_neighbor_witness hu

end Moore57
