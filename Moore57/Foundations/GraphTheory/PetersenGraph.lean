import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Petersen graph as `SimpleGraph (Fin 10)`

Explicit construction of the Petersen graph and proof that it is a strongly
regular graph with parameters `(10, 3, 0, 1)` (`IsSRGWith 10 3 0 1`).

## Construction

We use the standard generalized-Petersen `GP(5, 2)` realization on `Fin 10`:

* Outer pentagon (vertices `0, 1, 2, 3, 4`): cycle `0-1-2-3-4-0`.
* Inner pentagram (vertices `5, 6, 7, 8, 9`, step `2`): cycle `5-7-9-6-8-5`.
* Spokes (matching): `0-5, 1-6, 2-7, 3-8, 4-9`.

15 edges in total.  Uniqueness of Petersen as the unique `(10, 3, 0, 1)`-SRG
(classical Hoffman–Singleton classification) gives the connection.

## Main results

* `petersenGraph` — the explicit `SimpleGraph (Fin 10)`.
* `petersenGraph_isSRG : petersenGraph.IsSRGWith 10 3 0 1` — by `native_decide`.

## Bridges to Mačaj–Širáň §6 Lemma 17

The §6 Lemma 17 case (1) `Fix(X) = Petersen ⟹ |X| ∣ 27` is split into an
arithmetic core (already proven, see
`Moore57.Papers.MacajSiran2010.S6.lem17_case1_arithmetic_3group_dvd_54_implies_27`)
and a geometric identification step (which this file feeds into).  The
`PetersenFixedData` structure (`Moore57Graph/Aut/PetersenFixedData.lean`)
packages the geometric data needed by the §6 dispatch.
-/

namespace Moore57

open SimpleGraph

/-- The 15 edges of the Petersen graph, encoded as ordered `(ℕ, ℕ)` pairs.

* Outer pentagon (5 edges): `0-1, 1-2, 2-3, 3-4, 0-4`.
* Inner pentagram (5 edges, step 2): `5-7, 7-9, 6-9, 6-8, 5-8`.
* Spokes (5 edges): `0-5, 1-6, 2-7, 3-8, 4-9`. -/
private def petersenEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
   (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

/-- Symmetric adjacency relation: `(u, v)` is an edge of the Petersen graph
iff either `(u.val, v.val)` or `(v.val, u.val)` appears in `petersenEdges`. -/
def petersenRel (u v : Fin 10) : Prop :=
  (u.val, v.val) ∈ petersenEdges ∨ (v.val, u.val) ∈ petersenEdges

instance petersenRel_decidableRel : DecidableRel petersenRel := fun u v => by
  unfold petersenRel
  exact inferInstance

/-- `petersenRel` is symmetric: swapping `u` and `v` swaps the two disjuncts. -/
theorem petersenRel_symm : Symmetric petersenRel := fun _ _ h => h.symm

/-- **The Petersen graph** as a `SimpleGraph (Fin 10)`. -/
def petersenGraph : SimpleGraph (Fin 10) where
  Adj u v := u ≠ v ∧ petersenRel u v
  symm := fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, petersenRel_symm h2⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

instance petersenGraph_decidableAdj : DecidableRel petersenGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ petersenRel u v))

/-- **Petersen vertex count.** -/
theorem petersenGraph_card : Fintype.card (Fin 10) = 10 := by decide

/-- **Petersen is regular of degree 3.**

Each of the 10 vertices has degree exactly 3 (one outer/inner cycle neighbour
on each side plus one spoke partner).  Proof by case analysis on `Fin 10`
plus `decide`. -/
theorem petersenGraph_regular : petersenGraph.IsRegularOfDegree 3 := by
  intro v
  fin_cases v <;> decide

/-- **Petersen has `λ = 0`: any two adjacent vertices share `0` common
neighbours** (i.e., Petersen is triangle-free). -/
theorem petersenGraph_lambda :
    ∀ v w : Fin 10, petersenGraph.Adj v w →
      Fintype.card (petersenGraph.commonNeighbors v w) = 0 := by
  intro v w hadj
  fin_cases v <;> fin_cases w <;>
    first
      | (exact absurd hadj (by decide))
      | decide

/-- **Petersen has `μ = 1`: any two non-adjacent distinct vertices share
exactly `1` common neighbour** (the Moore-graph defining property). -/
theorem petersenGraph_mu : ∀ v w : Fin 10, v ≠ w → ¬petersenGraph.Adj v w →
    Fintype.card (petersenGraph.commonNeighbors v w) = 1 := by
  intro v w hne hadj
  fin_cases v <;> fin_cases w <;>
    first
      | (exact absurd rfl hne)
      | (exact absurd (by decide) hadj)
      | decide

/-- **Petersen is `(10, 3, 0, 1)`-strongly regular.**

Combines the four pieces:
* `card`: `Fintype.card (Fin 10) = 10`.
* `regular`: each vertex has degree 3.
* `of_adj`: adjacent ⟹ 0 common neighbours.
* `of_not_adj`: distinct & non-adjacent ⟹ 1 common neighbour. -/
theorem petersenGraph_isSRG : petersenGraph.IsSRGWith 10 3 0 1 where
  card := petersenGraph_card
  regular := petersenGraph_regular
  of_adj := petersenGraph_lambda
  of_not_adj := fun _ _ hne hadj => petersenGraph_mu _ _ hne hadj

/-- **Petersen has exactly 15 edges.**

Handshaking lemma: `∑ v, degree v = 2 · |E|`.  With every vertex of degree 3
and 10 vertices, the left side is `30`, so `|E| = 15`. -/
theorem petersenGraph_edgeFinset_card : petersenGraph.edgeFinset.card = 15 := by
  have hsum := petersenGraph.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v : Fin 10, petersenGraph.degree v = 3 := petersenGraph_regular
  simp [hdeg] at hsum
  omega

/-- **Petersen is triangle-free.**

Direct consequence of `λ = 0`: no two adjacent vertices share a common
neighbour, hence no triangles. -/
theorem petersenGraph_triangleFree : ∀ a b c : Fin 10,
    petersenGraph.Adj a b → petersenGraph.Adj b c → petersenGraph.Adj a c → False := by
  intro a b c hab hbc hac
  have hcn : Fintype.card (petersenGraph.commonNeighbors a c) = 0 :=
    petersenGraph_lambda a c hac
  have : b ∈ petersenGraph.commonNeighbors a c := ⟨hab, hbc.symm⟩
  have hpos : 0 < Fintype.card (petersenGraph.commonNeighbors a c) :=
    Fintype.card_pos_iff.mpr ⟨⟨b, this⟩⟩
  omega

/-- **Petersen has girth at least 5: no 4-cycle.**

`λ = μ = ?` actually gives no 4-cycle via Moore-property: two non-adjacent
distinct vertices share exactly `μ = 1` common neighbour, so they cannot
share two distinct common neighbours (which would form a 4-cycle). -/
theorem petersenGraph_no_C4 :
    ∀ a b c d : Fin 10, a ≠ c → b ≠ d →
      petersenGraph.Adj a b → petersenGraph.Adj b c →
      petersenGraph.Adj c d → petersenGraph.Adj d a → False := by
  intro a b c d hac hbd hab hbc hcd hda
  -- a and c are both adjacent to b and d.  If a, c are non-adjacent, μ = 1
  -- gives ≤ 1 common neighbour, contradicting 2 (b, d).  If a, c are
  -- adjacent, λ = 0 says they share 0 common neighbours, again contradicting
  -- the existence of b.
  by_cases hadj : petersenGraph.Adj a c
  · -- Triangle abc via a-b-c.
    exact petersenGraph_triangleFree a b c hab hbc hadj
  · -- a, c non-adjacent and distinct ⟹ μ = 1 common neighbour.
    have hcn : Fintype.card (petersenGraph.commonNeighbors a c) = 1 :=
      petersenGraph_mu a c hac hadj
    have hb_mem : b ∈ petersenGraph.commonNeighbors a c := ⟨hab, hbc.symm⟩
    have hd_mem : d ∈ petersenGraph.commonNeighbors a c := ⟨hda.symm, hcd⟩
    -- Two distinct elements in a 1-element finset is impossible.
    have hne : (⟨b, hb_mem⟩ : petersenGraph.commonNeighbors a c) ≠ ⟨d, hd_mem⟩ := by
      intro heq
      exact hbd (Subtype.mk.injEq _ _ _ _ |>.mp heq)
    have hge2 : 2 ≤ Fintype.card (petersenGraph.commonNeighbors a c) := by
      have := Fintype.card_subtype_le (fun (x : petersenGraph.commonNeighbors a c) =>
        x = ⟨b, hb_mem⟩ ∨ x = ⟨d, hd_mem⟩)
      have hcard2 : Fintype.card {x : petersenGraph.commonNeighbors a c //
          x = ⟨b, hb_mem⟩ ∨ x = ⟨d, hd_mem⟩} = 2 := by
        rw [Fintype.card_subtype]
        rw [show (Finset.univ.filter (fun x : petersenGraph.commonNeighbors a c =>
              x = ⟨b, hb_mem⟩ ∨ x = ⟨d, hd_mem⟩))
            = {⟨b, hb_mem⟩, ⟨d, hd_mem⟩} from ?_]
        · rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
        · ext x
          simp [Finset.mem_insert, Finset.mem_singleton]
      omega
    omega

end Moore57
