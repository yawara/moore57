import Moore57.Foundations.GraphTheory.PetersenGraph
import Moore57.Foundations.GraphTheory.PetersenUniqueness
import Moore57.Foundations.GraphTheory.SRGPredicates
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Auxiliary structural lemmas for SRG `(10, 3, 0, 1)` graphs

Bridge lemmas extracting concrete combinatorial structure from the
abstract `IsSRGWith 10 3 0 1` hypothesis.  These feed into the proof
of `PetersenUniqueness` by establishing the basic neighbourhood and
distance shape that any Petersen-like graph must satisfy.

## Strategy

A graph `G` satisfying `IsSRGWith 10 3 0 1` is:

* triangle-free (`λ = 0`);
* has diameter `≤ 2` (any two non-adjacent distinct vertices share
  `μ = 1` common neighbour, so a `2`-path connects them);
* has 15 edges (degree-sum: `10 · 3 / 2 = 15`);
* has no 4-cycle (`μ = 1` forces unique common neighbour, so two
  non-adjacent vertices cannot share two distinct common neighbours).

Together these properties pin down Petersen up to isomorphism
(Hoffman–Singleton 1960; Bose 1963).  This file packages the abstract
versions of these properties so that they are available for the final
isomorphism construction.

## Main results

* `IsPetersenLike.triangleFree` — `λ = 0` ⟹ triangle-free.
* `IsPetersenLike.edgeFinset_card` — exactly 15 edges.
* `IsPetersenLike.no_C4` — no 4-cycle.
* `IsPetersenLike.adj_or_commonNeighbor` — every pair connected at
  distance `≤ 2`.
* `IsPetersenLike.exists_unique_commonNeighbor` — `μ = 1` gives a
  uniqueness witness.

## Why bridge lemmas?

These lemmas are conditional on `IsSRGWith 10 3 0 1` but **not** on
the eventual `PetersenUniqueness` hypothesis.  They are pure
combinatorial consequences of the SRG parameters and can be used
directly by the `PetersenUniqueness` proof or by downstream files
that need partial structure (e.g., triangle-freeness alone).
-/

namespace Moore57

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-- **Triangle-freeness from `λ = 0`.**

Any `(10, 3, 0, 1)`-SRG `G` has no triangle: if `a, b, c` are pairwise
adjacent, then `b` is a common neighbour of `a` and `c`, but `λ = 0`
forces zero common neighbours among adjacent vertices. -/
theorem IsPetersenLike.triangleFree
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) :
    ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj a c → False := by
  intro a b c hab hbc hac
  have hcn : Fintype.card (G.commonNeighbors a c) = 0 := h.of_adj a c hac
  have hmem : b ∈ G.commonNeighbors a c := ⟨hab, hbc.symm⟩
  have hpos : 0 < Fintype.card (G.commonNeighbors a c) :=
    Fintype.card_pos_iff.mpr ⟨⟨b, hmem⟩⟩
  omega

/-- **Exactly 15 edges from the parameters.**

Degree-sum: `∑ v, deg v = 2 · |E|`.  With 10 vertices each of degree 3,
the LHS is 30, so `|E| = 15`. -/
theorem IsPetersenLike.edgeFinset_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) : G.edgeFinset.card = 15 :=
  isPetersenLike_edgeFinset_card h

/-- **No 4-cycle (`μ = 1` Moore property).**

If `a, b, c, d` form a 4-cycle with `a ≠ c` and `b ≠ d`, then `b` and
`d` are two distinct common neighbours of the non-adjacent pair `(a, c)`
(after checking adjacency), contradicting `μ = 1`.  If `a, c` are
adjacent, triangle-freeness on `a, b, c` gives the contradiction. -/
theorem IsPetersenLike.no_C4
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) :
    ∀ a b c d : V, a ≠ c → b ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False := by
  classical
  intro a b c d hac hbd hab hbc hcd hda
  by_cases hadj : G.Adj a c
  · exact h.triangleFree a b c hab hbc hadj
  · have hcn : Fintype.card (G.commonNeighbors a c) = 1 :=
      h.of_not_adj hac hadj
    have hb_mem : b ∈ G.commonNeighbors a c := ⟨hab, hbc.symm⟩
    have hd_mem : d ∈ G.commonNeighbors a c := ⟨hda.symm, hcd⟩
    have hne :
        (⟨b, hb_mem⟩ : G.commonNeighbors a c) ≠ ⟨d, hd_mem⟩ := by
      intro heq
      exact hbd (Subtype.mk.injEq _ _ _ _ |>.mp heq)
    have hsubsingleton : Subsingleton (G.commonNeighbors a c) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact hne (Subsingleton.elim _ _)

/-- **Every pair of vertices is at distance `≤ 2` (diameter bound).**

For any `v ≠ w` in `V`:
* either `G.Adj v w` (distance 1), or
* `G` has `μ = 1` common neighbours of `(v, w)`, so there exists a
  `2`-path `v -- z -- w`.

This is the key Moore-property consequence: an SRG `(10, 3, 0, 1)` is
a Moore graph of diameter 2. -/
theorem IsPetersenLike.adj_or_commonNeighbor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v w : V) (hne : v ≠ w) :
    G.Adj v w ∨ ∃ z, G.Adj v z ∧ G.Adj w z := by
  by_cases hadj : G.Adj v w
  · exact Or.inl hadj
  · right
    have hcn : Fintype.card (G.commonNeighbors v w) = 1 :=
      h.of_not_adj hne hadj
    have hnonempty : Nonempty (G.commonNeighbors v w) :=
      Fintype.card_pos_iff.mp (by omega)
    obtain ⟨⟨z, hz⟩⟩ := hnonempty
    rcases hz with ⟨hvz, hwz⟩
    exact ⟨z, hvz, hwz⟩

/-- **Each vertex has exactly 3 neighbours.** -/
theorem IsPetersenLike.degree_eq_three
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) : G.degree v = 3 :=
  h.regular v

/-- **Vertex count is exactly 10.** -/
theorem IsPetersenLike.card_eq_ten
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) : Fintype.card V = 10 := h.card

/-- **Adjacent vertices share zero common neighbours.** -/
theorem IsPetersenLike.lambda_zero
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v w : V) (hadj : G.Adj v w) :
    Fintype.card (G.commonNeighbors v w) = 0 :=
  h.of_adj v w hadj

/-- **Non-adjacent distinct vertices share exactly one common neighbour.** -/
theorem IsPetersenLike.mu_one
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v w : V) (hne : v ≠ w) (hadj : ¬G.Adj v w) :
    Fintype.card (G.commonNeighbors v w) = 1 :=
  h.of_not_adj hne hadj

/-- **Uniqueness of the common neighbour (witness extraction).**

If `v, w` are distinct non-adjacent vertices, there exists a **unique**
`z` adjacent to both (the unique common neighbour from `μ = 1`). -/
theorem IsPetersenLike.exists_unique_commonNeighbor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v w : V) (hne : v ≠ w) (hadj : ¬G.Adj v w) :
    ∃! z, G.Adj v z ∧ G.Adj w z := by
  have hcn := h.mu_one v w hne hadj
  have hnonempty : Nonempty (G.commonNeighbors v w) := by
    rw [← Fintype.card_pos_iff]; omega
  obtain ⟨⟨z, hz⟩⟩ := hnonempty
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  have hz'_mem : z' ∈ G.commonNeighbors v w := hz'
  have hsubsingleton : Subsingleton (G.commonNeighbors v w) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have : (⟨z, hz⟩ : G.commonNeighbors v w) = ⟨z', hz'_mem⟩ :=
    Subsingleton.elim _ _
  exact (Subtype.mk.injEq _ _ _ _ |>.mp this).symm

/-- **Non-adjacent pair gives a 2-path (constructive form).**

For any distinct non-adjacent `v, w`, there exists `z` such that
`v -- z -- w` is a 2-path.  This is the constructive form of
`adj_or_commonNeighbor`. -/
theorem IsPetersenLike.exists_2path_of_not_adj
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v w : V) (hne : v ≠ w) (hadj : ¬G.Adj v w) :
    ∃ z, G.Adj v z ∧ G.Adj w z := by
  obtain ⟨z, hz, _⟩ := h.exists_unique_commonNeighbor v w hne hadj
  exact ⟨z, hz⟩

/-- **Petersen-like graphs are nonempty.**

10 vertices in particular means a witness exists. -/
theorem IsPetersenLike.nonempty
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) : Nonempty V := by
  have : Fintype.card V = 10 := h.card
  exact Fintype.card_pos_iff.mp (by omega)

/-- **Sum of degrees equals 30.**

Direct degree-sum: `∑_v deg(v) = 10 · 3 = 30`. -/
theorem IsPetersenLike.sum_degrees
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) :
    ∑ v : V, G.degree v = 30 := by
  have hcard : Fintype.card V = 10 := h.card
  have hreg : ∀ v : V, G.degree v = 3 := h.regular
  calc ∑ v : V, G.degree v
      = ∑ _v : V, 3 := Finset.sum_congr rfl (fun v _ => hreg v)
    _ = Fintype.card V * 3 := by
        rw [Finset.sum_const, Finset.card_univ]; ring
    _ = 30 := by rw [hcard]

/-- **Non-adjacent count: each vertex has exactly 6 non-neighbours
(excluding itself).**

In a 10-vertex graph of degree 3, the complement degree is `10 - 3 - 1 = 6`. -/
theorem IsPetersenLike.compl_degree
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    Gᶜ.degree v = 6 := by
  -- compl_is_regular gives Gᶜ.IsRegularOfDegree (n - k - 1).
  -- Here n = Fintype.card V via h.card = 10, and k = 3.
  have hcompl_reg := h.compl_is_regular
  have hcard : Fintype.card V = 10 := h.card
  have := hcompl_reg v
  -- this : Gᶜ.degree v = 10 - 3 - 1 = 6.
  omega

/-! ### Bose 1963 structural lemmas (toward `PetersenUniqueness`)

This block adds combinatorial structure heading toward Bose 1963's
enumeration of `(10, 3, 0, 1)`-SRGs.  The lemmas package neighbourhood
shape, complement parameters, and Moore-property refinements that are
the standard scaffolding for a direct uniqueness proof.

Each lemma is a pure consequence of the four SRG parameters
`(n, k, ℓ, μ) = (10, 3, 0, 1)` plus the `IsPetersenLike` predicate;
none require the (still-open) `PetersenUniqueness` hypothesis. -/

/-- **No third vertex lies on a triangle through a given edge** (`λ = 0`).

The "edge-witness" form of triangle-freeness: for any edge `{v, w}`,
no other vertex `z` is simultaneously adjacent to both `v` and `w`. -/
theorem IsPetersenLike.no_triangle_through_edge
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hadj : G.Adj v w) :
    ∀ z : V, ¬ (G.Adj v z ∧ G.Adj w z) := by
  intro z ⟨hvz, hwz⟩
  exact h.triangleFree v z w hvz hwz.symm hadj

/-- **Unique common-neighbour witness for non-adjacent pairs** (`μ = 1`
sharpened).

Compared to `exists_unique_commonNeighbor`, this packages the witness
together with the uniqueness statement as a `Subsingleton`/finset-level
statement: the `commonNeighbors` finset has cardinality exactly one. -/
theorem IsPetersenLike.adj_pair_unique_commonNeighbor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hne : v ≠ w) (hadj : ¬G.Adj v w) :
    ∃! z, G.Adj v z ∧ G.Adj w z :=
  h.exists_unique_commonNeighbor v w hne hadj

/-- **Each vertex's open neighbour-finset has exactly 3 elements.**

This is the finset form of `degree_eq_three`, more directly usable for
neighbourhood-based counting arguments. -/
theorem IsPetersenLike.neighborFinset_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) : (G.neighborFinset v).card = 3 := by
  have hdeg : G.degree v = 3 := h.regular v
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]

/-- **The open neighbourhood of any vertex is an independent set.**

This is a structural consequence of `λ = 0`: if `x, y ∈ N(v)` were
adjacent, the triple `v, x, y` would form a triangle. -/
theorem IsPetersenLike.neighborhood_is_independent
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    G.IsIndepSet (G.neighborSet v) := by
  intro x hx y hy _hxy hadj_xy
  rw [SimpleGraph.mem_neighborSet] at hx hy
  exact h.triangleFree v x y hx hadj_xy hy

/-- **The set of "strangers" of a vertex has cardinality 6.**

For any `v : V`, the set of vertices that are neither `v` itself nor
a neighbour of `v` has cardinality `10 - 1 - 3 = 6`.  This is the
"non-neighbour count" appearing in Bose 1963's enumeration: each
vertex sees 3 neighbours and 6 strangers (with itself excluded). -/
theorem IsPetersenLike.non_neighborhood_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    ((Finset.univ : Finset V) \ (insert v (G.neighborFinset v))).card = 6 := by
  classical
  have hcard : Fintype.card V = 10 := h.card
  have hcard_univ : (Finset.univ : Finset V).card = 10 := by
    rw [Finset.card_univ]; exact hcard
  have hndeg : (G.neighborFinset v).card = 3 := h.neighborFinset_card v
  have hv_nmem : v ∉ G.neighborFinset v := SimpleGraph.notMem_neighborFinset_self G v
  have hins :
      (insert v (G.neighborFinset v)).card = 4 := by
    rw [Finset.card_insert_of_notMem hv_nmem, hndeg]
  have hsub : insert v (G.neighborFinset v) ⊆ (Finset.univ : Finset V) := by
    intro _ _; exact Finset.mem_univ _
  rw [Finset.card_sdiff_of_subset hsub]
  omega

/-- **Every pair of vertices is at distance `≤ 2`** (alternative form).

This is `adj_or_commonNeighbor` recast in the constructive `∃ z, ...`
form for the non-adjacent case, with `Or` direction flattened. -/
theorem IsPetersenLike.distance_le_2
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v w : V) (hne : v ≠ w) :
    G.Adj v w ∨ ∃ z, z ≠ v ∧ z ≠ w ∧ G.Adj v z ∧ G.Adj w z := by
  rcases h.adj_or_commonNeighbor v w hne with hvw | ⟨z, hvz, hwz⟩
  · exact Or.inl hvw
  · refine Or.inr ⟨z, ?_, ?_, hvz, hwz⟩
    · intro heq; subst heq; exact (G.irrefl hvz).elim
    · intro heq; subst heq; exact (G.irrefl hwz).elim

/-- **Non-adjacent pair: exactly one `2`-path between them.**

For distinct non-adjacent `v, w`, the number of common neighbours
(= number of `2`-paths from `v` to `w`) is exactly 1.  This is the
finset form of `μ = 1`. -/
theorem IsPetersenLike.non_neighbor_2path_count
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) {v w : V} (hne : v ≠ w) (hadj : ¬G.Adj v w) :
    Fintype.card (G.commonNeighbors v w) = 1 :=
  h.mu_one v w hne hadj

/-- **Complement parameters: `IsSRGWith 10 6 3 4`.**

The complement of a Petersen-like graph is the complement
strongly-regular graph with parameters `(10, 6, 3, 4)` (this is the
triangular graph `T(5)` / Johnson `J(5, 2)`).  Follows by
specialising `IsSRGWith.compl` to `(n, k, ℓ, μ) = (10, 3, 0, 1)`. -/
theorem IsPetersenLike.compl_isSRGWith
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) :
    Gᶜ.IsSRGWith 10 6 3 4 := by
  classical
  have hcompl := h.compl
  -- `IsSRGWith.compl` gives `Gᶜ.IsSRGWith n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ))`.
  -- With `(n, k, ℓ, μ) = (10, 3, 0, 1)`: `(10 - 3 - 1, 10 - (6 - 1) - 2, 10 - 6) = (6, 3, 4)`.
  -- The arithmetic is definitional, but we rewrite to expose the numerals.
  -- `n - (2 * k - μ) - 2 = 10 - (6 - 1) - 2 = 10 - 5 - 2 = 3`.
  -- `n - (2 * k - ℓ) = 10 - 6 = 4`.
  exact hcompl

/-- **Complement edge count: 30 edges.**

A Petersen-like graph has 15 edges out of `C(10, 2) = 45`; its
complement has `45 - 15 = 30` edges.  Direct via `compl_isSRGWith`
and the degree-sum formula on the complement. -/
theorem IsPetersenLike.complement_edgeFinset_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) :
    Gᶜ.edgeFinset.card = 30 := by
  classical
  have hcompl : Gᶜ.IsSRGWith 10 6 3 4 := h.compl_isSRGWith
  have hcard : Fintype.card V = 10 := hcompl.card
  have hreg : ∀ v : V, Gᶜ.degree v = 6 := hcompl.regular
  have hsum := Gᶜ.sum_degrees_eq_twice_card_edges
  have h60 : ∑ v : V, Gᶜ.degree v = 60 := by
    calc ∑ v : V, Gᶜ.degree v
        = ∑ _v : V, 6 := Finset.sum_congr rfl (fun v _ => hreg v)
      _ = Fintype.card V * 6 := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ = 60 := by rw [hcard]
  rw [h60] at hsum
  omega

/-- **Total edge budget: `|E(G)| + |E(Gᶜ)| = 45`.**

A clean reformulation of "`G` and its complement partition the edges
of the complete graph on 10 vertices."  Follows from
`edgeFinset_card = 15` and `complement_edgeFinset_card = 30`. -/
theorem IsPetersenLike.edges_partition
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = 45 := by
  rw [h.edgeFinset_card, h.complement_edgeFinset_card]

/-- **The full vertex set decomposes as `{v} ⊔ N(v) ⊔ strangers(v)`.**

For each vertex `v`, the finset `univ` is the disjoint union of
`{v}`, the open neighbourhood `N(v)`, and the strangers
(non-neighbours other than `v`).  This is the Bose 1963 vertex
partition used in the enumeration.  We package the cardinality
identity `1 + 3 + 6 = 10`. -/
theorem IsPetersenLike.vertex_partition_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : IsPetersenLike G) (v : V) :
    1 + (G.neighborFinset v).card +
      ((Finset.univ : Finset V) \ (insert v (G.neighborFinset v))).card = 10 := by
  rw [h.neighborFinset_card v, h.non_neighborhood_card v]

/-! ### Petersen-like graphs satisfy the same properties on `Fin 10` -/

/-- **Petersen-like Prop restricted to `Fin 10`.**

A simpler reformulation: if `G : SimpleGraph (Fin 10)` is
Petersen-like, then `G ≃g petersenGraph`.  This is the most concrete
specialisation of `PetersenUniqueness`. -/
def PetersenUniquenessFin10 : Prop :=
  ∀ (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj],
    G.IsSRGWith 10 3 0 1 → Nonempty (G ≃g petersenGraph)

/-- **The general `PetersenUniqueness` implies the `Fin 10`-specialised form.**

Specialising `α := Fin 10` (`Type 0`) gives the restricted statement
directly.  Note universe constraints force an explicit `(Fin 10)`
binding rather than implicit unification. -/
theorem PetersenUniqueness.toFin10
    (h : PetersenUniqueness.{0}) :
    PetersenUniquenessFin10 := by
  intro G _ hG
  exact h G hG

end Moore57
