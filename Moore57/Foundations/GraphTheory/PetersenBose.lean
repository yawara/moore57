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
set_option linter.unusedDecidableInType false

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

/-! ### Edge-relative refinements (5-cycle scaffolding)

For an edge `(v, w)`, the strangers of `v` admit a finer decomposition
indexed by `N(v) = {w, z₁, z₂}`:

* `partnersOf G v w` — the 2 partners-via-`w`, i.e. `N(w) \ {v}`.
  These are the 2 strangers of `v` that are *adjacent to* `w`.
* `partnersOf G v z₁`, `partnersOf G v z₂` — the 4 remaining strangers
  (2 per neighbour), each adjacent to one of `v`'s other two neighbours.

The pieces are disjoint by `μ = 1`, total 6, and the `w`-partners are the
strangers reachable from `v` through the chosen edge.  This is the
scaffolding the explicit `K_{3,3}`-minus-a-matching incidence between
`N(v) \ {w}` and `N(w) \ {v}` rests on, and feeds the 5-cycle existence
argument: starting from `v – w`, the only way back to `v` in 3 more steps
is through 2 strangers and one of the `z_i`. -/

/-- **Partners-of-`w` lie inside `N(w)`** (definitional unpack).

Since `partnersOf G v w = (G.neighborFinset w).erase v`, the inclusion
`partnersOf G v w ⊆ G.neighborFinset w` is `Finset.erase_subset`. -/
theorem IsPetersenLike.partnersOf_subset_neighborFinset
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (v z : V) :
    partnersOf G v z ⊆ G.neighborFinset z := by
  unfold partnersOf
  exact Finset.erase_subset _ _

/-- **Partners via `w` are exactly the strangers of `v` adjacent to `w`.**

For an edge `(v, w)`, an element `u ∈ partnersOf G v w` iff `u ≠ v` and
`G.Adj w u`.  In a Petersen-like graph, by `λ = 0`, such `u` is
automatically not adjacent to `v` (otherwise `v – w – u – v` triangle),
so `u ∈ strangers G v`.  This lemma packages that characterisation as a
biconditional. -/
theorem IsPetersenLike.mem_partnersOf_w_iff_stranger
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w u : V} (hadj : G.Adj v w) :
    u ∈ partnersOf G v w ↔ u ∈ strangers G v ∧ G.Adj w u := by
  rw [mem_partnersOf_iff, mem_strangers_iff]
  constructor
  · rintro ⟨hne, hwu⟩
    refine ⟨⟨hne, ?_⟩, hwu⟩
    intro hvu
    -- triangle v - w - u with v - u
    exact h.no_triangle_through_edge hadj u ⟨hvu, hwu⟩
  · rintro ⟨⟨hne, _⟩, hwu⟩
    exact ⟨hne, hwu⟩

/-- **Strangers of `v` adjacent to `w` are exactly `partnersOf G v w`.**

The set-theoretic form: `(strangers G v) ∩ (N(w)) = partnersOf G v w`
when `(v, w)` is an edge.  This is the "row" of the
`K_{3,3}`-minus-matching at `w` in the Bose 1963 incidence. -/
theorem IsPetersenLike.strangers_inter_neighborFinset_w
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    (strangers G v) ∩ (G.neighborFinset w) = partnersOf G v w := by
  ext u
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      h.mem_partnersOf_w_iff_stranger hadj]

/-- **Cardinality of `w`-partners for an edge `(v, w)`: exactly 2.**

Named restatement of `partnersOf_card` applied at `z = w` for an edge
`(v, w)`.  Provides a direct numerical form for downstream edge-relative
counting. -/
theorem IsPetersenLike.edge_partnersOf_w_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    (partnersOf G v w).card = 2 :=
  h.partnersOf_card hadj

/-- **Each stranger of `v` is in a unique `partnersOf G v z`** (the
partition's uniqueness of fibres).

For `u ∈ strangers G v`, there exists a unique `z ∈ N(v)` such that
`u ∈ partnersOf G v z`.  This packages the biUnion of `partnersOf` as a
**partition** (existence + uniqueness of the index).  The witness `z` is
the unique common neighbour of `v` and `u` from `μ = 1`. -/
theorem IsPetersenLike.exists_unique_partnersOf_index
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v u : V} (hu : u ∈ strangers G v) :
    ∃! z, z ∈ G.neighborFinset v ∧ u ∈ partnersOf G v z := by
  have hu_copy := hu
  rw [mem_strangers_iff] at hu_copy
  obtain ⟨hne_uv, _⟩ := hu_copy
  obtain ⟨z, ⟨hz_mem, hzu⟩, hunique⟩ := h.exists_unique_neighbor_witness hu
  refine ⟨z, ⟨hz_mem, ?_⟩, ?_⟩
  · rw [mem_partnersOf_iff]; exact ⟨hne_uv, hzu⟩
  · rintro z' ⟨hz'_mem, hz'_part⟩
    rw [mem_partnersOf_iff] at hz'_part
    exact hunique z' ⟨hz'_mem, hz'_part.2⟩

/-- **The `partnersOf` 2-path witness coincides with `z` for `u ∈ partnersOf G v z`.**

If `z ∈ N(v)` and `u ∈ partnersOf G v z`, then the unique `μ = 1`
witness of the 2-path `v – ? – u` is exactly `z`.  This pins down the
constructive form of `non_neighbor_2path_count` via the partition. -/
theorem IsPetersenLike.partnersOf_2path_witness_eq
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v z u : V}
    (hz_mem : z ∈ G.neighborFinset v) (hu_part : u ∈ partnersOf G v z) :
    ∀ z', z' ∈ G.neighborFinset v ∧ G.Adj z' u → z' = z := by
  rw [SimpleGraph.mem_neighborFinset] at hz_mem
  rw [mem_partnersOf_iff] at hu_part
  obtain ⟨hne_uv, hzu⟩ := hu_part
  have hu_stranger : u ∈ strangers G v := by
    rw [mem_strangers_iff]
    refine ⟨hne_uv, ?_⟩
    intro hvu
    exact h.no_triangle_through_edge hvu z ⟨hz_mem, hzu.symm⟩
  obtain ⟨z₀, ⟨hz₀_mem, hz₀u⟩, hunique⟩ :=
    h.exists_unique_neighbor_witness hu_stranger
  intro z' ⟨hz'_mem, hz'u⟩
  have hz_eq : z = z₀ := by
    apply hunique
    refine ⟨?_, hzu⟩
    rw [SimpleGraph.mem_neighborFinset]; exact hz_mem
  have hz'_eq : z' = z₀ := hunique z' ⟨hz'_mem, hz'u⟩
  rw [hz_eq, hz'_eq]

/-- **The `partnersOf` index function (assignment of strangers to N(v)).**

For each stranger `u` of `v`, this returns the unique `z ∈ N(v)` such that
`u ∈ partnersOf G v z`.  Defined via `Finset.choose` on the unique-existence
witness `exists_unique_partnersOf_index`. -/
noncomputable def IsPetersenLike.partnerIndex
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v u : V} (hu : u ∈ strangers G v) : V :=
  (h.exists_unique_partnersOf_index hu).choose

/-- **Defining property of `partnerIndex`** (membership in `N(v)`). -/
theorem IsPetersenLike.partnerIndex_mem
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v u : V} (hu : u ∈ strangers G v) :
    h.partnerIndex hu ∈ G.neighborFinset v :=
  (h.exists_unique_partnersOf_index hu).choose_spec.1.1

/-- **Defining property of `partnerIndex`** (the stranger is a partner). -/
theorem IsPetersenLike.partnerIndex_partners
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v u : V} (hu : u ∈ strangers G v) :
    u ∈ partnersOf G v (h.partnerIndex hu) :=
  (h.exists_unique_partnersOf_index hu).choose_spec.1.2

/-- **5-cycle existence through any edge** (Petersen girth-5).

For an edge `(v, w)` in a Petersen-like graph, there exists a 5-cycle
`v – w – u₁ – x – u₂ – v` containing both `v` and `w`.  Concretely:

* Pick `u₁ ∈ partnersOf G v w` (2 choices, both strangers of `v`).
* By `μ = 1`, `v` and `u₁` share a unique common neighbour `x ∈ N(v)`.
* The third edge `u₁ – x` then closes the 5-cycle via some `u₂` adjacent
  to both `x` and `v`.

Here we extract just the **existence of the second leg**: there exists
`u₁ ∈ strangers G v` adjacent to `w`, which is exactly a 3-path
`v – w – u₁` extending the edge.  Full 5-cycle existence requires
chaining two more steps; we leave that for downstream work. -/
theorem IsPetersenLike.exists_extending_3path
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    ∃ u, u ∈ strangers G v ∧ G.Adj w u ∧ u ≠ v := by
  have hcard : (partnersOf G v w).card = 2 := h.partnersOf_card hadj
  have hnonempty : (partnersOf G v w).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨u, hu⟩ := hnonempty
  have hu_stranger : u ∈ strangers G v := h.partnersOf_subset_strangers hadj hu
  rw [mem_partnersOf_iff] at hu
  refine ⟨u, hu_stranger, hu.2, hu.1⟩

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Edge endpoint `w` is a neighbour of `v`'s neighbour-finset element.**

A trivial bridge: for an edge `(v, w)`, `w ∈ G.neighborFinset v`. -/
theorem IsPetersenLike.edge_endpoint_mem_neighborFinset
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} (hadj : G.Adj v w) :
    w ∈ G.neighborFinset v := by
  rw [SimpleGraph.mem_neighborFinset]; exact hadj

/-- **Stranger `u ∈ partnersOf G v z` is adjacent to its partner index `z`.**

For `u ∈ partnersOf G v z` with `z ∈ N(v)`, by definition `G.Adj z u`.
This is the "non-`v` neighbour of `z`" property exposed in the
constructive form needed for the Bose 1963 incidence. -/
theorem IsPetersenLike.partner_adj_index
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v z u : V} (hu : u ∈ partnersOf G v z) : G.Adj z u :=
  (mem_partnersOf_iff.mp hu).2

/-- **Strangers split via `N(v) = {w} ∪ (N(v) \ {w})` for any edge endpoint `w`.**

For `w ∈ N(v)`, the strangers of `v` decompose as
`partnersOf G v w` (2 vertices, adjacent to `w`) and the biUnion of
`partnersOf G v z` over `z ∈ (G.neighborFinset v).erase w` (4 vertices,
the remaining 2 neighbours' partners).  This is the edge-relative form
of `strangers_eq_biUnion_partnersOf`. -/
theorem IsPetersenLike.strangers_eq_partnersOf_w_union_rest
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    strangers G v =
      partnersOf G v w ∪
        ((G.neighborFinset v).erase w).biUnion (partnersOf G v) := by
  rw [h.strangers_eq_biUnion_partnersOf v]
  have hw_mem : w ∈ G.neighborFinset v :=
    IsPetersenLike.edge_endpoint_mem_neighborFinset hadj
  -- `(G.neighborFinset v).biUnion f = f w ∪ ((neighborFinset v).erase w).biUnion f`.
  conv_lhs => rw [← Finset.insert_erase hw_mem]
  rw [Finset.biUnion_insert]

/-! ### Tier 1: 5-cycle existence through any edge -/

/-- **The "other neighbours" finset `N(v) \ {w}` has cardinality 2** for any
edge endpoint `w`. -/
theorem IsPetersenLike.neighborFinset_erase_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    ((G.neighborFinset v).erase w).card = 2 := by
  have hw_mem : w ∈ G.neighborFinset v :=
    IsPetersenLike.edge_endpoint_mem_neighborFinset hadj
  rw [Finset.card_erase_of_mem hw_mem, h.neighborFinset_card v]

/-- **`w ∉ partnersOf G v x` for `x ∈ N(v) \ {w}` and `(v, w)` an edge** (no
triangle through `(v, w)`).

If `w ∈ partnersOf G v x = N(x) \ {v}`, then `G.Adj x w`, combined with
`G.Adj v x` and `G.Adj v w`, gives a triangle `v - x - w` through the
edge `(v, w)`, contradicting `λ = 0`. -/
theorem IsPetersenLike.edge_w_notMem_partnersOf
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w x : V}
    (hadj_vw : G.Adj v w) (hadj_vx : G.Adj v x) (_hxw : x ≠ w) :
    w ∉ partnersOf G v x := by
  intro hw_mem
  rw [mem_partnersOf_iff] at hw_mem
  obtain ⟨_, hxw_adj⟩ := hw_mem
  exact h.no_triangle_through_edge hadj_vw x ⟨hadj_vx, hxw_adj.symm⟩

/-- **For an edge endpoint `x ∈ N(v) \ {w}`, `partnersOf G v x` lies inside
`strangers G v` and avoids `w`** (so any partner is also distinct from `w`).
-/
theorem IsPetersenLike.partnersOf_subset_strangers_erase_w
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w x : V}
    (hadj_vw : G.Adj v w) (hadj_vx : G.Adj v x) (hxw : x ≠ w) :
    partnersOf G v x ⊆ (strangers G v).erase w := by
  intro y hy
  rw [Finset.mem_erase]
  refine ⟨?_, h.partnersOf_subset_strangers hadj_vx hy⟩
  intro heq
  subst heq
  exact h.edge_w_notMem_partnersOf hadj_vw hadj_vx hxw hy

/-- **Existence of a non-`w` neighbour of `v`** (for an edge `(v, w)`).

Since `|N(v) \ {w}| = 2 > 0`, there exists `x ∈ N(v)` with `x ≠ w`. -/
theorem IsPetersenLike.exists_other_neighbor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    ∃ x, G.Adj v x ∧ x ≠ w := by
  have hcard : ((G.neighborFinset v).erase w).card = 2 :=
    h.neighborFinset_erase_card hadj
  have hnonempty : ((G.neighborFinset v).erase w).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨x, hx⟩ := hnonempty
  rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hx
  exact ⟨x, hx.2, hx.1⟩

/-- **Existence of a 3-path `v - x - y` extending edge `(v, w)` to a non-`w`
neighbour of `v`.**

For edge `(v, w)`, there exist `x, y` with `Adj v x ∧ Adj x y ∧ x ≠ w ∧
y ∈ strangers G v ∧ y ≠ w`.  The vertex `y` lies in `partnersOf G v x`
(so adjacent to `x`, distinct from `v`), and avoids `w` because `w` would
form a triangle through edge `(v, w)`. -/
theorem IsPetersenLike.exists_3path_avoiding_w
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    ∃ x y, G.Adj v x ∧ G.Adj x y ∧ x ≠ w ∧ x ≠ v ∧
           y ∈ strangers G v ∧ y ≠ w ∧ y ≠ v ∧ y ≠ x := by
  obtain ⟨x, hadj_vx, hxw⟩ := h.exists_other_neighbor hadj
  have hxv : x ≠ v := fun heq => by subst heq; exact (G.irrefl hadj_vx).elim
  -- `partnersOf G v x` has cardinality 2; pick any partner `y`.
  have hcard : (partnersOf G v x).card = 2 := h.partnersOf_card hadj_vx
  have hnonempty : (partnersOf G v x).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨y, hy⟩ := hnonempty
  have hy_stranger : y ∈ strangers G v := h.partnersOf_subset_strangers hadj_vx hy
  have hyw : y ≠ w := by
    intro heq
    subst heq
    exact h.edge_w_notMem_partnersOf hadj hadj_vx hxw hy
  rw [mem_partnersOf_iff] at hy
  obtain ⟨hyv, hxy⟩ := hy
  have hyx : y ≠ x := fun heq => by subst heq; exact (G.irrefl hxy).elim
  refine ⟨x, y, hadj_vx, hxy, hxw, hxv, hy_stranger, hyw, hyv, hyx⟩

/-- **No 4-cycle through an edge** (specialised form of `no_C4`).

For an edge `(v, w)` and a 3-path `v - x - y` with `x ≠ w` and `y ≠ v`,
the vertex `y` is **not** adjacent to `w`: otherwise `v - x - y - w - v`
would be a 4-cycle.  Requires `y ≠ x` (irreflexivity guarantees this if
`Adj x y`) and `v ≠ y` (since `y ∈ strangers G v`). -/
theorem IsPetersenLike.no_adj_y_w_of_3path
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w x y : V}
    (hadj_vw : G.Adj v w) (hadj_vx : G.Adj v x) (hadj_xy : G.Adj x y)
    (hxw : x ≠ w) (hyv : y ≠ v) :
    ¬ G.Adj y w := by
  intro hadj_yw
  -- 4-cycle `v - x - y - w - v` with `v ≠ y` and `x ≠ w`.
  -- The `no_C4` lemma signature: `a ≠ c → b ≠ d → ...` for `a - b - c - d - a`.
  -- Here `(a, b, c, d) = (v, x, y, w)`, so `a ≠ c` is `v ≠ y` and `b ≠ d` is `x ≠ w`.
  exact h.no_C4 v x y w (Ne.symm hyv) hxw hadj_vx hadj_xy hadj_yw hadj_vw.symm

/-- **5-cycle existence through any edge** (the main Tier 1 milestone).

For any edge `(v, w)` of a Petersen-like graph, there is a 5-cycle
`v - x - y - z - w - v` (formally: vertices `x, y, z` together with
adjacencies and the 13 pairwise-distinctness conditions).

**Construction.**
1. Pick `x ∈ N(v) \ {w}` (`|N(v) \ {w}| = 2`).
2. Pick `y ∈ partnersOf G v x` (so `Adj x y` and `y ∈ strangers G v`,
   in particular `y ≠ v ∧ ¬ Adj v y`).  Also `y ≠ w` (otherwise
   triangle).
3. By `no_C4`, `¬ Adj y w`.  By `μ = 1`, there is a unique `z` with
   `Adj y z ∧ Adj w z`.
4. Distinctness:
   * `z ≠ v` (else `Adj v y`, contradicting `y ∈ strangers G v`);
   * `z ≠ x` (else `Adj v x ∧ Adj w x ∧ Adj v w` triangle);
   * `z ≠ y, z ≠ w` (irreflexivity).
-/
theorem IsPetersenLike.exists_5cycle_through_edge
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hvw : G.Adj v w) :
    ∃ x y z, G.Adj v x ∧ G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧
             x ≠ v ∧ x ≠ w ∧ y ≠ v ∧ y ≠ w ∧ z ≠ v ∧ z ≠ w ∧
             x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  -- Step 1-2: extending 3-path `v - x - y` avoiding `w`.
  obtain ⟨x, y, hadj_vx, hadj_xy, hxw, hxv, hy_stranger, hyw, hyv, hyx⟩ :=
    h.exists_3path_avoiding_w hvw
  -- `y ∈ strangers G v`, so `¬ Adj v y`.
  rw [mem_strangers_iff] at hy_stranger
  obtain ⟨_, hvy_nadj⟩ := hy_stranger
  -- Step 3: `¬ Adj y w` by `no_C4`.
  have hyw_nadj : ¬ G.Adj y w := h.no_adj_y_w_of_3path hvw hadj_vx hadj_xy hxw hyv
  -- By `μ = 1`, unique `z` adjacent to both `y` and `w`.
  obtain ⟨z, ⟨hadj_yz, hadj_wz⟩, _⟩ :=
    h.exists_unique_commonNeighbor y w hyw hyw_nadj
  -- Step 4: distinctness.
  have hzy : z ≠ y := fun heq => by subst heq; exact (G.irrefl hadj_yz).elim
  have hzw : z ≠ w := fun heq => by subst heq; exact (G.irrefl hadj_wz).elim
  have hzv : z ≠ v := by
    intro heq
    subst heq
    -- `G.Adj y z = G.Adj y v` and `¬ G.Adj v y` gives contradiction.
    exact hvy_nadj hadj_yz.symm
  have hzx : z ≠ x := by
    intro heq
    -- `heq : z = x`.  Then `Adj w z = Adj w x`.  Triangle `v - x - w`.
    rw [heq] at hadj_wz
    exact h.triangleFree v x w hadj_vx hadj_wz.symm hvw
  refine ⟨x, y, z, hadj_vx, hadj_xy, hadj_yz, hadj_wz.symm,
          hxv, hxw, hyv, hyw, hzv, hzw, hyx.symm, hzx.symm, hzy.symm⟩

/-! ### Tier 2: K_{3,3}-minus-matching scaffolding

For an edge `(v, w)`, the "bipartite remainder" is the structure between
`N(v) \ {w}` (2 vertices) and `N(w) \ {v}` (2 vertices), together with
the 4 strangers attached to each side via the partner indices.  The full
K_{3,3}-minus-perfect-matching identification is the central Bose 1963
incidence; here we record the **basic structural facts** that pave the
way:

* `N(v) \ {w}` and `N(w) \ {v}` both have cardinality 2 (degree-3 graph);
* The two sides are disjoint (`λ = 0` on edge `(v, w)`);
* `partnersOf G v w = N(w) \ {v}` and `partnersOf G w v = N(v) \ {w}`
  (definitional restatement: both sides of the bipartite incidence are
  partner pairs in the strangers-partition sense from the *other*
  endpoint).

The full edge-by-edge K_{3,3}-minus-matching identification (which edges
are present/absent between the two sides) is deferred. -/

/-- **`N(w) \ {v}` has cardinality 2** for an edge `(v, w)`.

This is `partnersOf_card` applied to `partnersOf G w v` — the "other"
side of the bipartite incidence (looking at `w`'s non-`v` neighbours
instead of `v`'s non-`w` neighbours). -/
theorem IsPetersenLike.partnersOf_w_v_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    (partnersOf G w v).card = 2 :=
  h.partnersOf_card hadj.symm

/-- **`N(v) \ {w}` and `N(w) \ {v}` are disjoint** (`λ = 0` on edge `(v, w)`).

If `x` lies in both, then `x ∈ N(v) ∩ N(w)` is a common neighbour of
adjacent vertices `v, w`, contradicting `λ = 0`. -/
theorem IsPetersenLike.bipartite_sides_disjoint
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    Disjoint ((G.neighborFinset v).erase w) ((G.neighborFinset w).erase v) := by
  rw [Finset.disjoint_left]
  intro x hx_v hx_w
  rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hx_v hx_w
  exact h.no_triangle_through_edge hadj x ⟨hx_v.2, hx_w.2⟩

/-- **`partnersOf G v w = (G.neighborFinset w).erase v`** (definitional
restatement).

This is the "right side" of the K_{3,3} bipartite description: the
non-`v` neighbours of `w`.  Already definitional, but recorded as a
named lemma for downstream pattern matching. -/
theorem IsPetersenLike.partnersOf_eq_neighborFinset_erase
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (v z : V) :
    partnersOf G v z = (G.neighborFinset z).erase v := rfl

/-- **For each non-`w` neighbour `z` of `v`, `partnersOf G v z` is a 2-element
subset of `strangers G v` disjoint from `partnersOf G v w`.**

Combines `partnersOf_card`, `partnersOf_subset_strangers`, and
`partnersOf_disjoint`.  Reformulates the Bose 1963 incidence at the
"non-`w`" neighbours of `v`. -/
theorem IsPetersenLike.partnersOf_nonw_disjoint_w
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w z : V}
    (hadj_vw : G.Adj v w) (hadj_vz : G.Adj v z) (hzw : z ≠ w) :
    (partnersOf G v z).card = 2 ∧
    partnersOf G v z ⊆ strangers G v ∧
    Disjoint (partnersOf G v z) (partnersOf G v w) :=
  ⟨h.partnersOf_card hadj_vz, h.partnersOf_subset_strangers hadj_vz,
   h.partnersOf_disjoint hadj_vz hadj_vw hzw⟩

/-- **The `w`-side partner pair: 2-element subset of strangers.**

Combines `partnersOf_card` and `partnersOf_subset_strangers` at
`z = w`.  This exposes the "right side" `N(w) \ {v}` of the bipartite
K_{3,3}-minus-matching as a 2-element pair of strangers. -/
theorem IsPetersenLike.partnersOf_w_pair
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    (partnersOf G v w).card = 2 ∧ partnersOf G v w ⊆ strangers G v :=
  ⟨h.partnersOf_card hadj, h.partnersOf_subset_strangers hadj⟩

/-- **The bipartite-side carrier `N(v) \ {w}` is exactly `partnersOf G w v`
restricted by membership in `N(v)`** (= the same thing in disguise).

In symbols: `(G.neighborFinset v).erase w = partnersOf G w v ∩ G.neighborFinset v`.
Actually more directly, both sides equal `{x : V | G.Adj v x ∧ x ≠ w}`.
This characterises the "left side" of the K_{3,3}-bipartite incidence. -/
theorem IsPetersenLike.neighborFinset_erase_w_eq
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} :
    (G.neighborFinset v).erase w =
      (G.neighborFinset v).filter (fun x => x ≠ w) := by
  ext x
  rw [Finset.mem_erase, Finset.mem_filter]
  exact and_comm

/-- **5-cycle existence on `petersenGraph`** (smoke test: the existence
theorem applies to the explicit `petersenGraph`).

Sanity check that `exists_5cycle_through_edge` works on the canonical
`petersenGraph`.  Records the trivial application. -/
theorem petersenGraph_exists_5cycle_through_edge
    {v w : Fin 10} (hvw : petersenGraph.Adj v w) :
    ∃ x y z, petersenGraph.Adj v x ∧ petersenGraph.Adj x y ∧
             petersenGraph.Adj y z ∧ petersenGraph.Adj z w ∧
             x ≠ v ∧ x ≠ w ∧ y ≠ v ∧ y ≠ w ∧ z ≠ v ∧ z ≠ w ∧
             x ≠ y ∧ x ≠ z ∧ y ≠ z :=
  petersenGraph_isPetersenLike.exists_5cycle_through_edge hvw

end Moore57
