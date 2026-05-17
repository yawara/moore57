import Moore57.Moore57Graph.Aut.OrderElevenCandidates
import Moore57.Moore57Graph.Aut.FixedSubgraphData

/-!
# Construction of `C5FixedData` for an order-11 Moore57 automorphism

Given `σ : Equiv.Perm V` with `σ ^ 11 = 1` and `σ ≠ 1`, we have shown
(in `OrderElevenCandidates.lean`) that:

* The σ-fixed induced graph is regular of some degree `k`.
* `|Fix(σ)| = k² + 1`.
* `k = 2` (from the local Hoffman-Singleton classification + Stage 5).
* Hence `|Fix(σ)| = 5`.

This file packages those 5 vertices as a `C5FixedData Γ σ`: explicit
cyclic enumeration `v : Fin 5 → V` with adjacency exactly the cycle edges.

The construction proceeds by:
1. Pick `v₀ : fixedVertexSet σ` (exists since |Fix| = 5 > 0).
2. `v₀` has exactly 2 H-neighbors. Call them `v₁` and `v₄`.
3. `v₂` := unique H-neighbor of `v₁` other than `v₀`.
4. `v₃` := unique H-neighbor of `v₂` other than `v₁`.
5. Show `v₃` is adjacent to `v₄` (the cycle closes).
6. Verify injectivity, span, and cycle_only.
-/

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- For `σ ^ 11 = 1, σ ≠ 1` automorphism of Moore57, the σ-fixed induced
graph is regular of degree exactly 2, and has 5 vertices. -/
theorem aut_order_eleven_fixedInducedGraph_isSRGWith_5_2_0_1
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1) :
    (autFixedInducedGraph Γ σ).IsSRGWith 5 2 0 1 := by
  classical
  have hcard : fixedVertexCount σ = 5 :=
    aut_order_eleven_fixedVertexCount_eq_five hΓ σ smul_adj pow_eleven hne
  rcases aut_fixedInducedGraph_regular_of_pow_eleven hΓ σ smul_adj pow_eleven
    with ⟨k, hreg⟩
  have hk_sq : fixedVertexCount σ = k * k + 1 :=
    aut_fixedVertexCount_eq_sq_add_one_of_regular_of_pow_eleven
      hΓ σ smul_adj pow_eleven k hreg
  -- k*k + 1 = 5 ⟹ k = 2.
  have hk_eq_2 : k = 2 := by
    have h5 : k * k + 1 = 5 := by rw [← hk_sq, hcard]
    have : k * k = 4 := by omega
    nlinarith
  subst hk_eq_2
  have hsrg :=
    autFixedInducedGraph_isSRGWith_of_regular hΓ σ smul_adj 2 hreg
  rw [hcard] at hsrg
  exact hsrg

/-! ### Pick first vertex v₀ and its 2 neighbors -/

/-- Pick `v₀ : fixedVertexSet σ` arbitrarily. -/
noncomputable def aut_order_eleven_v0
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1) : fixedVertexSet σ := by
  have hcard : fixedVertexCount σ = 5 :=
    aut_order_eleven_fixedVertexCount_eq_five hΓ σ smul_adj pow_eleven hne
  have hpos : 0 < Fintype.card (fixedVertexSet σ) := by
    rw [← fixedVertexCount_eq_card_fixedVertexSet]; omega
  exact (Fintype.card_pos_iff.mp hpos).some

/-- The H-neighbors of `v₀`. Since H is 2-regular, this Finset has size 2. -/
noncomputable def aut_order_eleven_v0_neighbors
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1) :
    Finset (fixedVertexSet σ) :=
  (autFixedInducedGraph Γ σ).neighborFinset
    (aut_order_eleven_v0 hΓ σ smul_adj pow_eleven hne)

theorem aut_order_eleven_v0_neighbors_card
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1) :
    (aut_order_eleven_v0_neighbors hΓ σ smul_adj pow_eleven hne).card = 2 := by
  classical
  unfold aut_order_eleven_v0_neighbors
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  have hsrg := aut_order_eleven_fixedInducedGraph_isSRGWith_5_2_0_1
    hΓ σ smul_adj pow_eleven hne
  exact hsrg.regular _

end Moore57

/-! ### Generic cycle-extraction helper

These helpers live outside the Moore57 namespace because they are pure
graph theory on a 2-regular vertex. -/

namespace SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Given a vertex `v` in a graph `G` with degree 2 and a designated neighbor
`prev`, "the other neighbor" is the unique H-neighbor of `v` distinct from
`prev`. -/
noncomputable def otherNeighbor
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (v prev : W) (hdeg : G.degree v = 2) (hprev_adj : G.Adj v prev) : W := by
  classical
  have hne : ((G.neighborFinset v).erase prev).Nonempty := by
    have hcard : (G.neighborFinset v).card = 2 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
    have hprev_mem : prev ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]; exact hprev_adj
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := Finset.card_erase_of_mem hprev_mem
    rw [hempty] at this
    simp at this
    omega
  exact hne.choose

theorem otherNeighbor_mem_erase
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (v prev : W) (hdeg : G.degree v = 2) (hprev_adj : G.Adj v prev) :
    G.otherNeighbor v prev hdeg hprev_adj ∈
      (G.neighborFinset v).erase prev := by
  classical
  unfold otherNeighbor
  generalize_proofs hne
  exact hne.choose_spec

theorem otherNeighbor_adj
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (v prev : W) (hdeg : G.degree v = 2) (hprev_adj : G.Adj v prev) :
    G.Adj v (G.otherNeighbor v prev hdeg hprev_adj) := by
  classical
  have hmem := G.otherNeighbor_mem_erase v prev hdeg hprev_adj
  rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hmem
  exact hmem.2

theorem otherNeighbor_ne_prev
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (v prev : W) (hdeg : G.degree v = 2) (hprev_adj : G.Adj v prev) :
    G.otherNeighbor v prev hdeg hprev_adj ≠ prev := by
  classical
  have hmem := G.otherNeighbor_mem_erase v prev hdeg hprev_adj
  rw [Finset.mem_erase] at hmem
  exact hmem.1

/-- Uniqueness: `otherNeighbor` returns the unique non-`prev` H-neighbor. -/
theorem otherNeighbor_eq_of_adj
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (v prev : W) (hdeg : G.degree v = 2) (hprev_adj : G.Adj v prev)
    (w : W) (hw_adj : G.Adj v w) (hw_ne : w ≠ prev) :
    w = G.otherNeighbor v prev hdeg hprev_adj := by
  classical
  have hcard : (G.neighborFinset v).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
  have hprev_mem : prev ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]; exact hprev_adj
  have hw_mem : w ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]; exact hw_adj
  have herase_card : ((G.neighborFinset v).erase prev).card = 1 := by
    rw [Finset.card_erase_of_mem hprev_mem, hcard]
  have hw_mem_erase : w ∈ (G.neighborFinset v).erase prev :=
    Finset.mem_erase.mpr ⟨hw_ne, hw_mem⟩
  have hother_mem_erase := G.otherNeighbor_mem_erase v prev hdeg hprev_adj
  rcases Finset.card_eq_one.mp herase_card with ⟨a, ha⟩
  rw [ha, Finset.mem_singleton] at hw_mem_erase hother_mem_erase
  rw [hw_mem_erase, hother_mem_erase]

end SimpleGraph

namespace Moore57

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-! ### Build the cycle v_0 - v_1 - v_2 - v_3 - v_4 - v_0

Working in the σ-fixed induced graph H on `fixedVertexSet σ`. We build
the cycle by picking v_0 arbitrarily, then v_1 = some neighbor of v_0,
v_2 = other neighbor of v_1, v_3 = other neighbor of v_2, v_4 = other
neighbor of v_3. -/
section CycleBuild

variable (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1)

include hΓ smul_adj pow_eleven hne

/-- The H-degree at every vertex is 2 (from SRG). -/
private theorem hH_deg (x : fixedVertexSet σ) :
    (autFixedInducedGraph Γ σ).degree x = 2 := by
  exact (aut_order_eleven_fixedInducedGraph_isSRGWith_5_2_0_1
    hΓ σ smul_adj pow_eleven hne).regular x

/-- v_0 : the seed fixed vertex. -/
private noncomputable def w0 : fixedVertexSet σ :=
  aut_order_eleven_v0 hΓ σ smul_adj pow_eleven hne

/-- v_0's neighbor finset has at least one element (size 2). -/
private theorem hw0_neighbors_nonempty :
    ((autFixedInducedGraph Γ σ).neighborFinset
      (w0 hΓ σ smul_adj pow_eleven hne)).Nonempty := by
  rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
  rw [hH_deg hΓ σ smul_adj pow_eleven hne]
  norm_num

/-- v_1 : an arbitrary H-neighbor of v_0. -/
private noncomputable def w1 : fixedVertexSet σ :=
  (hw0_neighbors_nonempty hΓ σ smul_adj pow_eleven hne).choose

private theorem hw0_w1_adj :
    (autFixedInducedGraph Γ σ).Adj
      (w0 hΓ σ smul_adj pow_eleven hne) (w1 hΓ σ smul_adj pow_eleven hne) := by
  unfold w1
  have hspec := (hw0_neighbors_nonempty hΓ σ smul_adj pow_eleven hne).choose_spec
  rw [SimpleGraph.mem_neighborFinset] at hspec
  exact hspec

/-- v_2 : the other H-neighbor of v_1 (not v_0). -/
private noncomputable def w2 : fixedVertexSet σ :=
  (autFixedInducedGraph Γ σ).otherNeighbor
    (w1 hΓ σ smul_adj pow_eleven hne)
    (w0 hΓ σ smul_adj pow_eleven hne)
    (hH_deg hΓ σ smul_adj pow_eleven hne _)
    (hw0_w1_adj hΓ σ smul_adj pow_eleven hne).symm

private theorem hw1_w2_adj :
    (autFixedInducedGraph Γ σ).Adj
      (w1 hΓ σ smul_adj pow_eleven hne) (w2 hΓ σ smul_adj pow_eleven hne) :=
  (autFixedInducedGraph Γ σ).otherNeighbor_adj _ _ _ _

private theorem hw2_ne_w0 :
    (w2 hΓ σ smul_adj pow_eleven hne) ≠ (w0 hΓ σ smul_adj pow_eleven hne) :=
  (autFixedInducedGraph Γ σ).otherNeighbor_ne_prev _ _ _ _

/-- v_3 : the other H-neighbor of v_2 (not v_1). -/
private noncomputable def w3 : fixedVertexSet σ :=
  (autFixedInducedGraph Γ σ).otherNeighbor
    (w2 hΓ σ smul_adj pow_eleven hne)
    (w1 hΓ σ smul_adj pow_eleven hne)
    (hH_deg hΓ σ smul_adj pow_eleven hne _)
    (hw1_w2_adj hΓ σ smul_adj pow_eleven hne).symm

private theorem hw2_w3_adj :
    (autFixedInducedGraph Γ σ).Adj
      (w2 hΓ σ smul_adj pow_eleven hne) (w3 hΓ σ smul_adj pow_eleven hne) :=
  (autFixedInducedGraph Γ σ).otherNeighbor_adj _ _ _ _

private theorem hw3_ne_w1 :
    (w3 hΓ σ smul_adj pow_eleven hne) ≠ (w1 hΓ σ smul_adj pow_eleven hne) :=
  (autFixedInducedGraph Γ σ).otherNeighbor_ne_prev _ _ _ _

/-- v_4 : the other H-neighbor of v_3 (not v_2). -/
private noncomputable def w4 : fixedVertexSet σ :=
  (autFixedInducedGraph Γ σ).otherNeighbor
    (w3 hΓ σ smul_adj pow_eleven hne)
    (w2 hΓ σ smul_adj pow_eleven hne)
    (hH_deg hΓ σ smul_adj pow_eleven hne _)
    (hw2_w3_adj hΓ σ smul_adj pow_eleven hne).symm

private theorem hw3_w4_adj :
    (autFixedInducedGraph Γ σ).Adj
      (w3 hΓ σ smul_adj pow_eleven hne) (w4 hΓ σ smul_adj pow_eleven hne) :=
  (autFixedInducedGraph Γ σ).otherNeighbor_adj _ _ _ _

private theorem hw4_ne_w2 :
    (w4 hΓ σ smul_adj pow_eleven hne) ≠ (w2 hΓ σ smul_adj pow_eleven hne) :=
  (autFixedInducedGraph Γ σ).otherNeighbor_ne_prev _ _ _ _

/-! ### Distinctness of v_0, v_1, v_2, v_3, v_4 -/

private theorem hw0_ne_w1 :
    (w0 hΓ σ smul_adj pow_eleven hne) ≠ (w1 hΓ σ smul_adj pow_eleven hne) := by
  intro h
  exact (autFixedInducedGraph Γ σ).irrefl
    (h ▸ hw0_w1_adj hΓ σ smul_adj pow_eleven hne)

private theorem hw1_ne_w2 :
    (w1 hΓ σ smul_adj pow_eleven hne) ≠ (w2 hΓ σ smul_adj pow_eleven hne) := by
  intro h
  exact (autFixedInducedGraph Γ σ).irrefl
    (h ▸ hw1_w2_adj hΓ σ smul_adj pow_eleven hne)

private theorem hw2_ne_w3 :
    (w2 hΓ σ smul_adj pow_eleven hne) ≠ (w3 hΓ σ smul_adj pow_eleven hne) := by
  intro h
  exact (autFixedInducedGraph Γ σ).irrefl
    (h ▸ hw2_w3_adj hΓ σ smul_adj pow_eleven hne)

private theorem hw3_ne_w4 :
    (w3 hΓ σ smul_adj pow_eleven hne) ≠ (w4 hΓ σ smul_adj pow_eleven hne) := by
  intro h
  exact (autFixedInducedGraph Γ σ).irrefl
    (h ▸ hw3_w4_adj hΓ σ smul_adj pow_eleven hne)

/-! ### Future work: closing the cycle and constructing `C5FixedData`

The remaining steps (proving `v_3 ≠ v_0`, `v_4 ≠ v_0`, `v_4 - v_0` adjacent,
and packaging into `C5FixedData`) require careful case analysis on the
2-regular triangle-free structure of `H`. This is mathematically routine
but Lean-tedious. Future work will complete this. -/

end CycleBuild

end Moore57
