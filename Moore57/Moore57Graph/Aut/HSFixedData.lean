import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Defs
import Moore57.Moore57Graph.Aut.NeighborMod
import Moore57.Moore57Graph.Moore57Definition
import Moore57.Foundations.GroupAction.FixedPoints

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

/-- **HS `fixedVertexCount = 50`**: the σ-fixed-vertex count equals `50`.

Combines `span` (every σ-fixed vertex is in the image of `v`) with
`v_injective` to identify the σ-fixed finset with the image of `Fin 50`
under `v`. -/
theorem fixedVertexCount_eq_50
    [Fintype V] [DecidableEq V] (h : HSFixedData Γ σ) :
    fixedVertexCount σ = 50 := by
  unfold fixedVertexCount
  have heq :
      ((Finset.univ : Finset V).filter (fun w => σ w = w))
        = (Finset.univ : Finset (Fin 50)).image h.v := by
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

/-- **HS induced triangle-free**: three fixed vertices indexed by HS do not
form a triangle.

Derived from `induced_lambda` (`λ = 0`): adjacent `v i, v k` share `0` common
indexed neighbours, but a triangle would witness `v j` as one. -/
theorem induced_triangleFree (h : HSFixedData Γ σ) :
    ∀ i j k : Fin 50, Γ.Adj (h.v i) (h.v j) → Γ.Adj (h.v j) (h.v k) →
      Γ.Adj (h.v i) (h.v k) → False := by
  intro i j k hij hjk hik
  have hzero := h.induced_lambda i k hik
  have hfin : {m : Fin 50 | Γ.Adj (h.v i) (h.v m) ∧ Γ.Adj (h.v k) (h.v m)}.Finite :=
    Set.toFinite _
  have hempty := (Set.ncard_eq_zero hfin).mp hzero
  have hmem : j ∈ {m : Fin 50 | Γ.Adj (h.v i) (h.v m) ∧ Γ.Adj (h.v k) (h.v m)} :=
    ⟨hij, hjk.symm⟩
  rw [hempty] at hmem
  exact hmem.elim

/-- **HS induced no 4-cycle**: four distinct fixed vertices (with `i ≠ k` and
`j ≠ l`) cannot form a 4-cycle.

Derived from `induced_lambda` and `induced_mu`: either `v i, v k` are
adjacent (giving a triangle excluded by `λ = 0`) or non-adjacent (giving
≥ 2 common neighbours, contradicting `μ = 1`). -/
theorem induced_no_C4 (h : HSFixedData Γ σ) :
    ∀ i j k l : Fin 50, i ≠ k → j ≠ l →
      Γ.Adj (h.v i) (h.v j) → Γ.Adj (h.v j) (h.v k) →
      Γ.Adj (h.v k) (h.v l) → Γ.Adj (h.v l) (h.v i) → False := by
  intro i j k l hik hjl hij hjk hkl hli
  by_cases hadj : Γ.Adj (h.v i) (h.v k)
  · exact h.induced_triangleFree i j k hij hjk hadj
  · have h1 := h.induced_mu i k hik hadj
    have hj_mem : j ∈ {m : Fin 50 | Γ.Adj (h.v i) (h.v m) ∧ Γ.Adj (h.v k) (h.v m)} :=
      ⟨hij, hjk.symm⟩
    have hl_mem : l ∈ {m : Fin 50 | Γ.Adj (h.v i) (h.v m) ∧ Γ.Adj (h.v k) (h.v m)} :=
      ⟨hli.symm, hkl⟩
    have hsub : ({j, l} : Set (Fin 50)) ⊆
        {m : Fin 50 | Γ.Adj (h.v i) (h.v m) ∧ Γ.Adj (h.v k) (h.v m)} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hj_mem
      · exact hl_mem
    have hpair : Set.ncard ({j, l} : Set (Fin 50)) = 2 := by
      rw [Set.ncard_pair hjl]
    have hfin : {m : Fin 50 | Γ.Adj (h.v i) (h.v m) ∧ Γ.Adj (h.v k) (h.v m)}.Finite :=
      Set.toFinite _
    have hge2 := Set.ncard_le_ncard hsub hfin
    rw [hpair] at hge2
    omega

end HSFixedData

end Moore57
