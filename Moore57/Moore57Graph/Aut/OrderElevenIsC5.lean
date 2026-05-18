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

/-! ### Triangle-free / common-neighbour helpers on H -/

omit [DecidableEq V] in
set_option linter.unusedSectionVars false in
/-- `H` is triangle-free: from `λ = 0` (SRG), any pair of adjacent vertices has
no common neighbour. So a third vertex adjacent to both yields contradiction. -/
private theorem hH_no_triangle
    {x y z : fixedVertexSet σ}
    (hxy : (autFixedInducedGraph Γ σ).Adj x y)
    (hxz : (autFixedInducedGraph Γ σ).Adj x z)
    (hyz : (autFixedInducedGraph Γ σ).Adj y z) : False := by
  classical
  have hcard0 :=
    autFixedInducedGraph_commonNeighbors_card_of_adj hΓ σ hxy
  have hz_mem : z ∈ (autFixedInducedGraph Γ σ).commonNeighbors x y :=
    ⟨hxz, hyz⟩
  have hpos :
      0 < Fintype.card ((autFixedInducedGraph Γ σ).commonNeighbors x y) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨z, hz_mem⟩⟩
  omega

omit [DecidableEq V] in
set_option linter.unusedSectionVars false in
/-- `H`'s `μ = 1` uniqueness: two common neighbours of a distinct non-adjacent
pair must coincide. -/
private theorem hH_common_nbr_unique
    {a b u₁ u₂ : fixedVertexSet σ}
    (h_ab_ne : a ≠ b)
    (h_ab_nadj : ¬ (autFixedInducedGraph Γ σ).Adj a b)
    (h_u1 :
      (autFixedInducedGraph Γ σ).Adj a u₁ ∧ (autFixedInducedGraph Γ σ).Adj b u₁)
    (h_u2 :
      (autFixedInducedGraph Γ σ).Adj a u₂ ∧ (autFixedInducedGraph Γ σ).Adj b u₂) :
    u₁ = u₂ := by
  classical
  have hcard1 :=
    autFixedInducedGraph_commonNeighbors_card_of_not_adj hΓ σ smul_adj
      h_ab_ne h_ab_nadj
  have hu1_mem : u₁ ∈ (autFixedInducedGraph Γ σ).commonNeighbors a b := h_u1
  have hu2_mem : u₂ ∈ (autFixedInducedGraph Γ σ).commonNeighbors a b := h_u2
  rcases Fintype.card_eq_one_iff.mp hcard1 with ⟨z, hz⟩
  have hu1eq :
      (⟨u₁, hu1_mem⟩ : ↥((autFixedInducedGraph Γ σ).commonNeighbors a b)) = z :=
    hz _
  have hu2eq :
      (⟨u₂, hu2_mem⟩ : ↥((autFixedInducedGraph Γ σ).commonNeighbors a b)) = z :=
    hz _
  exact congr_arg Subtype.val (hu1eq.trans hu2eq.symm)

/-! ### Remaining distinctness `w_3 ≠ w_0`, `w_4 ≠ w_0`, `w_4 ≠ w_1` -/

/-- `w_3 ≠ w_0`: otherwise `w_0, w_1, w_2` would form a triangle. -/
private theorem hw3_ne_w0 :
    (w3 hΓ σ smul_adj pow_eleven hne) ≠ (w0 hΓ σ smul_adj pow_eleven hne) := by
  intro heq
  have h_w2_w0 :
      (autFixedInducedGraph Γ σ).Adj
        (w2 hΓ σ smul_adj pow_eleven hne)
        (w0 hΓ σ smul_adj pow_eleven hne) :=
    heq ▸ hw2_w3_adj hΓ σ smul_adj pow_eleven hne
  exact hH_no_triangle hΓ σ smul_adj pow_eleven hne
    (hw0_w1_adj hΓ σ smul_adj pow_eleven hne)
    h_w2_w0.symm
    (hw1_w2_adj hΓ σ smul_adj pow_eleven hne)

/-- `w_4 ≠ w_1`: otherwise `w_1, w_2, w_3` would form a triangle. -/
private theorem hw4_ne_w1 :
    (w4 hΓ σ smul_adj pow_eleven hne) ≠ (w1 hΓ σ smul_adj pow_eleven hne) := by
  intro heq
  have h_w3_w1 :
      (autFixedInducedGraph Γ σ).Adj
        (w3 hΓ σ smul_adj pow_eleven hne)
        (w1 hΓ σ smul_adj pow_eleven hne) :=
    heq ▸ hw3_w4_adj hΓ σ smul_adj pow_eleven hne
  exact hH_no_triangle hΓ σ smul_adj pow_eleven hne
    (hw1_w2_adj hΓ σ smul_adj pow_eleven hne)
    h_w3_w1.symm
    (hw2_w3_adj hΓ σ smul_adj pow_eleven hne)

/-- `w_0 ≁ w_2`: otherwise `w_0, w_1, w_2` would form a triangle. -/
private theorem hw0_not_adj_w2 :
    ¬ (autFixedInducedGraph Γ σ).Adj
        (w0 hΓ σ smul_adj pow_eleven hne)
        (w2 hΓ σ smul_adj pow_eleven hne) := by
  intro hadj
  exact hH_no_triangle hΓ σ smul_adj pow_eleven hne
    (hw0_w1_adj hΓ σ smul_adj pow_eleven hne) hadj
    (hw1_w2_adj hΓ σ smul_adj pow_eleven hne)

/-- `w_0 ≁ w_3`: otherwise `w_1` and `w_3` would both be common neighbours of
the non-adjacent pair `(w_0, w_2)`, violating `μ = 1` (since `w_1 ≠ w_3`). -/
private theorem hw0_not_adj_w3 :
    ¬ (autFixedInducedGraph Γ σ).Adj
        (w0 hΓ σ smul_adj pow_eleven hne)
        (w3 hΓ σ smul_adj pow_eleven hne) := by
  intro hadj
  have hne_02 :
      (w0 hΓ σ smul_adj pow_eleven hne) ≠ (w2 hΓ σ smul_adj pow_eleven hne) :=
    (hw2_ne_w0 hΓ σ smul_adj pow_eleven hne).symm
  have h13 :
      (w1 hΓ σ smul_adj pow_eleven hne) = (w3 hΓ σ smul_adj pow_eleven hne) :=
    hH_common_nbr_unique hΓ σ smul_adj pow_eleven hne hne_02
      (hw0_not_adj_w2 hΓ σ smul_adj pow_eleven hne)
      ⟨hw0_w1_adj hΓ σ smul_adj pow_eleven hne,
        (hw1_w2_adj hΓ σ smul_adj pow_eleven hne).symm⟩
      ⟨hadj, hw2_w3_adj hΓ σ smul_adj pow_eleven hne⟩
  exact hw3_ne_w1 hΓ σ smul_adj pow_eleven hne h13.symm

/-- `w_4 ≠ w_0`: otherwise `w_1` and `w_3` would both be common neighbours of
the non-adjacent pair `(w_0, w_2)`, violating `μ = 1`. -/
private theorem hw4_ne_w0 :
    (w4 hΓ σ smul_adj pow_eleven hne) ≠ (w0 hΓ σ smul_adj pow_eleven hne) := by
  intro heq
  have h_w3_w0 :
      (autFixedInducedGraph Γ σ).Adj
        (w3 hΓ σ smul_adj pow_eleven hne)
        (w0 hΓ σ smul_adj pow_eleven hne) :=
    heq ▸ hw3_w4_adj hΓ σ smul_adj pow_eleven hne
  exact hw0_not_adj_w3 hΓ σ smul_adj pow_eleven hne h_w3_w0.symm

/-! ### All 5 vertices are distinct -/

private theorem hw0_ne_w2 :
    (w0 hΓ σ smul_adj pow_eleven hne) ≠ (w2 hΓ σ smul_adj pow_eleven hne) :=
  (hw2_ne_w0 hΓ σ smul_adj pow_eleven hne).symm

private theorem hw0_ne_w3 :
    (w0 hΓ σ smul_adj pow_eleven hne) ≠ (w3 hΓ σ smul_adj pow_eleven hne) :=
  (hw3_ne_w0 hΓ σ smul_adj pow_eleven hne).symm

private theorem hw0_ne_w4 :
    (w0 hΓ σ smul_adj pow_eleven hne) ≠ (w4 hΓ σ smul_adj pow_eleven hne) :=
  (hw4_ne_w0 hΓ σ smul_adj pow_eleven hne).symm

private theorem hw1_ne_w3 :
    (w1 hΓ σ smul_adj pow_eleven hne) ≠ (w3 hΓ σ smul_adj pow_eleven hne) :=
  (hw3_ne_w1 hΓ σ smul_adj pow_eleven hne).symm

private theorem hw1_ne_w4 :
    (w1 hΓ σ smul_adj pow_eleven hne) ≠ (w4 hΓ σ smul_adj pow_eleven hne) :=
  (hw4_ne_w1 hΓ σ smul_adj pow_eleven hne).symm

private theorem hw2_ne_w4 :
    (w2 hΓ σ smul_adj pow_eleven hne) ≠ (w4 hΓ σ smul_adj pow_eleven hne) :=
  (hw4_ne_w2 hΓ σ smul_adj pow_eleven hne).symm

/-! ### The 5 vertices exhaust `fixedVertexSet σ` -/

/-- `{w_0, w_1, w_2, w_3, w_4} = univ` as Finsets on `fixedVertexSet σ`,
since both have cardinality 5. -/
private theorem hWFin_eq_univ :
    ({w0 hΓ σ smul_adj pow_eleven hne,
       w1 hΓ σ smul_adj pow_eleven hne,
       w2 hΓ σ smul_adj pow_eleven hne,
       w3 hΓ σ smul_adj pow_eleven hne,
       w4 hΓ σ smul_adj pow_eleven hne} : Finset (fixedVertexSet σ)) =
      Finset.univ := by
  classical
  have hfin5 : Fintype.card (fixedVertexSet σ) = 5 := by
    rw [← fixedVertexCount_eq_card_fixedVertexSet]
    exact aut_order_eleven_fixedVertexCount_eq_five hΓ σ smul_adj pow_eleven hne
  set S : Finset (fixedVertexSet σ) :=
    ({w0 hΓ σ smul_adj pow_eleven hne,
        w1 hΓ σ smul_adj pow_eleven hne,
        w2 hΓ σ smul_adj pow_eleven hne,
        w3 hΓ σ smul_adj pow_eleven hne,
        w4 hΓ σ smul_adj pow_eleven hne} : Finset (fixedVertexSet σ))
  have hS_card : S.card = 5 := by
    have h01 := hw0_ne_w1 hΓ σ smul_adj pow_eleven hne
    have h02 := hw0_ne_w2 hΓ σ smul_adj pow_eleven hne
    have h03 := hw0_ne_w3 hΓ σ smul_adj pow_eleven hne
    have h04 := hw0_ne_w4 hΓ σ smul_adj pow_eleven hne
    have h12 := hw1_ne_w2 hΓ σ smul_adj pow_eleven hne
    have h13 := hw1_ne_w3 hΓ σ smul_adj pow_eleven hne
    have h14 := hw1_ne_w4 hΓ σ smul_adj pow_eleven hne
    have h23 := hw2_ne_w3 hΓ σ smul_adj pow_eleven hne
    have h24 := hw2_ne_w4 hΓ σ smul_adj pow_eleven hne
    have h34 := hw3_ne_w4 hΓ σ smul_adj pow_eleven hne
    simp [S, Finset.card_insert_of_notMem, Finset.mem_insert,
      Finset.mem_singleton, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, hfin5]
  omega

/-- Every vertex of `fixedVertexSet σ` is one of `w_0, …, w_4`. -/
private theorem hW_span (z : fixedVertexSet σ) :
    z = w0 hΓ σ smul_adj pow_eleven hne
    ∨ z = w1 hΓ σ smul_adj pow_eleven hne
    ∨ z = w2 hΓ σ smul_adj pow_eleven hne
    ∨ z = w3 hΓ σ smul_adj pow_eleven hne
    ∨ z = w4 hΓ σ smul_adj pow_eleven hne := by
  classical
  have hmem : z ∈ ({w0 hΓ σ smul_adj pow_eleven hne,
                      w1 hΓ σ smul_adj pow_eleven hne,
                      w2 hΓ σ smul_adj pow_eleven hne,
                      w3 hΓ σ smul_adj pow_eleven hne,
                      w4 hΓ σ smul_adj pow_eleven hne}
                     : Finset (fixedVertexSet σ)) := by
    rw [hWFin_eq_univ hΓ σ smul_adj pow_eleven hne]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

/-! ### Cycle closure: `w_0 ∼ w_4` -/

/-- The "other" H-neighbour of `w_0` (not `w_1`) must be `w_4`. -/
private theorem hw0_w4_adj :
    (autFixedInducedGraph Γ σ).Adj
      (w0 hΓ σ smul_adj pow_eleven hne) (w4 hΓ σ smul_adj pow_eleven hne) := by
  classical
  -- z := the otherNeighbor of w_0 w.r.t. prev := w_1.
  set z : fixedVertexSet σ :=
    (autFixedInducedGraph Γ σ).otherNeighbor
      (w0 hΓ σ smul_adj pow_eleven hne) (w1 hΓ σ smul_adj pow_eleven hne)
      (hH_deg hΓ σ smul_adj pow_eleven hne _)
      (hw0_w1_adj hΓ σ smul_adj pow_eleven hne) with hz_def
  have hz_adj :
      (autFixedInducedGraph Γ σ).Adj (w0 hΓ σ smul_adj pow_eleven hne) z := by
    have := (autFixedInducedGraph Γ σ).otherNeighbor_adj
      (w0 hΓ σ smul_adj pow_eleven hne) (w1 hΓ σ smul_adj pow_eleven hne)
      (hH_deg hΓ σ smul_adj pow_eleven hne _)
      (hw0_w1_adj hΓ σ smul_adj pow_eleven hne)
    simpa [hz_def] using this
  have hz_ne_w1 :
      z ≠ w1 hΓ σ smul_adj pow_eleven hne := by
    have := (autFixedInducedGraph Γ σ).otherNeighbor_ne_prev
      (w0 hΓ σ smul_adj pow_eleven hne) (w1 hΓ σ smul_adj pow_eleven hne)
      (hH_deg hΓ σ smul_adj pow_eleven hne _)
      (hw0_w1_adj hΓ σ smul_adj pow_eleven hne)
    simpa [hz_def] using this
  -- z ≠ w_0 (irrefl), z ≠ w_2 (¬ adj w_0 w_2), z ≠ w_3 (¬ adj w_0 w_3).
  have hz_ne_w0 :
      z ≠ w0 hΓ σ smul_adj pow_eleven hne := by
    intro heq
    exact (autFixedInducedGraph Γ σ).irrefl (heq ▸ hz_adj)
  have hz_ne_w2 :
      z ≠ w2 hΓ σ smul_adj pow_eleven hne := by
    intro heq
    exact hw0_not_adj_w2 hΓ σ smul_adj pow_eleven hne (heq ▸ hz_adj)
  have hz_ne_w3 :
      z ≠ w3 hΓ σ smul_adj pow_eleven hne := by
    intro heq
    exact hw0_not_adj_w3 hΓ σ smul_adj pow_eleven hne (heq ▸ hz_adj)
  -- z ∈ {w_0, ..., w_4}; eliminate all but w_4.
  rcases hW_span hΓ σ smul_adj pow_eleven hne z with h0 | h1 | h2 | h3 | h4
  · exact (hz_ne_w0 h0).elim
  · exact (hz_ne_w1 h1).elim
  · exact (hz_ne_w2 h2).elim
  · exact (hz_ne_w3 h3).elim
  · -- z = w_4 ⟹ w_0 adj w_4.
    rw [h4] at hz_adj; exact hz_adj

/-! ### Final non-adjacencies: `cycle_only` -/

/-- `w_1 ≁ w_3`: otherwise `w_1, w_2, w_3` would form a triangle. -/
private theorem hw1_not_adj_w3 :
    ¬ (autFixedInducedGraph Γ σ).Adj
        (w1 hΓ σ smul_adj pow_eleven hne)
        (w3 hΓ σ smul_adj pow_eleven hne) := by
  intro hadj
  exact hH_no_triangle hΓ σ smul_adj pow_eleven hne
    (hw1_w2_adj hΓ σ smul_adj pow_eleven hne) hadj
    (hw2_w3_adj hΓ σ smul_adj pow_eleven hne)

/-- `w_2 ≁ w_4`: otherwise `w_2, w_3, w_4` would form a triangle. -/
private theorem hw2_not_adj_w4 :
    ¬ (autFixedInducedGraph Γ σ).Adj
        (w2 hΓ σ smul_adj pow_eleven hne)
        (w4 hΓ σ smul_adj pow_eleven hne) := by
  intro hadj
  exact hH_no_triangle hΓ σ smul_adj pow_eleven hne
    (hw2_w3_adj hΓ σ smul_adj pow_eleven hne)
    hadj
    (hw3_w4_adj hΓ σ smul_adj pow_eleven hne)

/-- `w_1 ≁ w_4`: otherwise `w_2` and `w_4` would both be common neighbours of
the non-adjacent pair `(w_1, w_3)`, violating `μ = 1`. -/
private theorem hw1_not_adj_w4 :
    ¬ (autFixedInducedGraph Γ σ).Adj
        (w1 hΓ σ smul_adj pow_eleven hne)
        (w4 hΓ σ smul_adj pow_eleven hne) := by
  intro hadj
  have hne_13 :
      (w1 hΓ σ smul_adj pow_eleven hne) ≠ (w3 hΓ σ smul_adj pow_eleven hne) :=
    hw1_ne_w3 hΓ σ smul_adj pow_eleven hne
  have h24 :
      (w2 hΓ σ smul_adj pow_eleven hne) = (w4 hΓ σ smul_adj pow_eleven hne) :=
    hH_common_nbr_unique hΓ σ smul_adj pow_eleven hne hne_13
      (hw1_not_adj_w3 hΓ σ smul_adj pow_eleven hne)
      ⟨(hw1_w2_adj hΓ σ smul_adj pow_eleven hne),
        (hw2_w3_adj hΓ σ smul_adj pow_eleven hne).symm⟩
      ⟨hadj, (hw3_w4_adj hΓ σ smul_adj pow_eleven hne)⟩
  exact hw2_ne_w4 hΓ σ smul_adj pow_eleven hne h24

end CycleBuild

/-! ## Final construction of `C5FixedData` -/

section Construction

variable (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (pow_eleven : σ ^ 11 = 1) (hne : σ ≠ 1)

include hΓ smul_adj pow_eleven hne

/-- The 5 cycle vertices indexed by `Fin 5`, valued in `fixedVertexSet σ`. -/
private noncomputable def cycleSubtype (i : Fin 5) : fixedVertexSet σ :=
  match i with
  | ⟨0, _⟩ => w0 hΓ σ smul_adj pow_eleven hne
  | ⟨1, _⟩ => w1 hΓ σ smul_adj pow_eleven hne
  | ⟨2, _⟩ => w2 hΓ σ smul_adj pow_eleven hne
  | ⟨3, _⟩ => w3 hΓ σ smul_adj pow_eleven hne
  | ⟨4, _⟩ => w4 hΓ σ smul_adj pow_eleven hne

/-- Pointwise unfolding lemmas — make `cycleSubtype` step look up wᵢ. -/
private theorem cycleSubtype_zero :
    cycleSubtype hΓ σ smul_adj pow_eleven hne 0 =
      w0 hΓ σ smul_adj pow_eleven hne := rfl

private theorem cycleSubtype_one :
    cycleSubtype hΓ σ smul_adj pow_eleven hne 1 =
      w1 hΓ σ smul_adj pow_eleven hne := rfl

private theorem cycleSubtype_two :
    cycleSubtype hΓ σ smul_adj pow_eleven hne 2 =
      w2 hΓ σ smul_adj pow_eleven hne := rfl

private theorem cycleSubtype_three :
    cycleSubtype hΓ σ smul_adj pow_eleven hne 3 =
      w3 hΓ σ smul_adj pow_eleven hne := rfl

private theorem cycleSubtype_four :
    cycleSubtype hΓ σ smul_adj pow_eleven hne 4 =
      w4 hΓ σ smul_adj pow_eleven hne := rfl

/-- `cycleSubtype` is injective. Proof by pairwise distinctness on the 25 cases. -/
private theorem cycleSubtype_injective :
    Function.Injective (cycleSubtype hΓ σ smul_adj pow_eleven hne) := by
  have h01 := hw0_ne_w1 hΓ σ smul_adj pow_eleven hne
  have h02 := hw0_ne_w2 hΓ σ smul_adj pow_eleven hne
  have h03 := hw0_ne_w3 hΓ σ smul_adj pow_eleven hne
  have h04 := hw0_ne_w4 hΓ σ smul_adj pow_eleven hne
  have h12 := hw1_ne_w2 hΓ σ smul_adj pow_eleven hne
  have h13 := hw1_ne_w3 hΓ σ smul_adj pow_eleven hne
  have h14 := hw1_ne_w4 hΓ σ smul_adj pow_eleven hne
  have h23 := hw2_ne_w3 hΓ σ smul_adj pow_eleven hne
  have h24 := hw2_ne_w4 hΓ σ smul_adj pow_eleven hne
  have h34 := hw3_ne_w4 hΓ σ smul_adj pow_eleven hne
  intro i j hij
  fin_cases i
  · fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij h03
    · exact absurd hij h04
  · fin_cases j
    · exact absurd hij h01.symm
    · rfl
    · exact absurd hij h12
    · exact absurd hij h13
    · exact absurd hij h14
  · fin_cases j
    · exact absurd hij h02.symm
    · exact absurd hij h12.symm
    · rfl
    · exact absurd hij h23
    · exact absurd hij h24
  · fin_cases j
    · exact absurd hij h03.symm
    · exact absurd hij h13.symm
    · exact absurd hij h23.symm
    · rfl
    · exact absurd hij h34
  · fin_cases j
    · exact absurd hij h04.symm
    · exact absurd hij h14.symm
    · exact absurd hij h24.symm
    · exact absurd hij h34.symm
    · rfl

/-- The 5 cycle vertices as `V`. -/
private noncomputable def cycleVertex (i : Fin 5) : V :=
  (cycleSubtype hΓ σ smul_adj pow_eleven hne i : V)

private theorem cycleVertex_zero :
    cycleVertex hΓ σ smul_adj pow_eleven hne 0 =
      (w0 hΓ σ smul_adj pow_eleven hne : V) := rfl

private theorem cycleVertex_one :
    cycleVertex hΓ σ smul_adj pow_eleven hne 1 =
      (w1 hΓ σ smul_adj pow_eleven hne : V) := rfl

private theorem cycleVertex_two :
    cycleVertex hΓ σ smul_adj pow_eleven hne 2 =
      (w2 hΓ σ smul_adj pow_eleven hne : V) := rfl

private theorem cycleVertex_three :
    cycleVertex hΓ σ smul_adj pow_eleven hne 3 =
      (w3 hΓ σ smul_adj pow_eleven hne : V) := rfl

private theorem cycleVertex_four :
    cycleVertex hΓ σ smul_adj pow_eleven hne 4 =
      (w4 hΓ σ smul_adj pow_eleven hne : V) := rfl

/-- `cycleVertex` is injective: it is `Subtype.val ∘ cycleSubtype`. -/
private theorem cycleVertex_injective :
    Function.Injective (cycleVertex hΓ σ smul_adj pow_eleven hne) := by
  intro i j hij
  apply cycleSubtype_injective hΓ σ smul_adj pow_eleven hne
  exact Subtype.ext hij

/-! ### Helper lemmas for `cycle_only` -/

/-- Convert an H-adjacency on `cycleSubtype i, cycleSubtype j` to V-adjacency. -/
private theorem H_adj_of_cycleVertex_adj {i j : Fin 5}
    (hadj : Γ.Adj
      (cycleVertex hΓ σ smul_adj pow_eleven hne i)
      (cycleVertex hΓ σ smul_adj pow_eleven hne j)) :
    (autFixedInducedGraph Γ σ).Adj
      (cycleSubtype hΓ σ smul_adj pow_eleven hne i)
      (cycleSubtype hΓ σ smul_adj pow_eleven hne j) := hadj

/-! ### Main definition -/

/-- **Main result**: for `σ ^ 11 = 1` and `σ ≠ 1` automorphism of Moore57,
construct `C5FixedData Γ σ` from raw action data. -/
noncomputable def aut_order_eleven_C5FixedData : C5FixedData Γ σ where
  v := cycleVertex hΓ σ smul_adj pow_eleven hne
  v_injective := cycleVertex_injective hΓ σ smul_adj pow_eleven hne
  v_fixed := by
    intro i
    fin_cases i
    · exact (w0 hΓ σ smul_adj pow_eleven hne).property
    · exact (w1 hΓ σ smul_adj pow_eleven hne).property
    · exact (w2 hΓ σ smul_adj pow_eleven hne).property
    · exact (w3 hΓ σ smul_adj pow_eleven hne).property
    · exact (w4 hΓ σ smul_adj pow_eleven hne).property
  span := by
    intro x hx
    have hxFix : x ∈ fixedVertexSet σ := hx
    rcases hW_span hΓ σ smul_adj pow_eleven hne ⟨x, hxFix⟩ with
      h0 | h1 | h2 | h3 | h4
    · refine ⟨0, ?_⟩
      change x = (w0 hΓ σ smul_adj pow_eleven hne : V)
      exact congrArg Subtype.val h0
    · refine ⟨1, ?_⟩
      change x = (w1 hΓ σ smul_adj pow_eleven hne : V)
      exact congrArg Subtype.val h1
    · refine ⟨2, ?_⟩
      change x = (w2 hΓ σ smul_adj pow_eleven hne : V)
      exact congrArg Subtype.val h2
    · refine ⟨3, ?_⟩
      change x = (w3 hΓ σ smul_adj pow_eleven hne : V)
      exact congrArg Subtype.val h3
    · refine ⟨4, ?_⟩
      change x = (w4 hΓ σ smul_adj pow_eleven hne : V)
      exact congrArg Subtype.val h4
  cycle_adj := by
    intro i
    fin_cases i
    · -- (0, 1): w_0 ~ w_1
      change Γ.Adj (w0 hΓ σ smul_adj pow_eleven hne : V)
        (w1 hΓ σ smul_adj pow_eleven hne : V)
      exact hw0_w1_adj hΓ σ smul_adj pow_eleven hne
    · -- (1, 2): w_1 ~ w_2
      change Γ.Adj (w1 hΓ σ smul_adj pow_eleven hne : V)
        (w2 hΓ σ smul_adj pow_eleven hne : V)
      exact hw1_w2_adj hΓ σ smul_adj pow_eleven hne
    · -- (2, 3): w_2 ~ w_3
      change Γ.Adj (w2 hΓ σ smul_adj pow_eleven hne : V)
        (w3 hΓ σ smul_adj pow_eleven hne : V)
      exact hw2_w3_adj hΓ σ smul_adj pow_eleven hne
    · -- (3, 4): w_3 ~ w_4
      change Γ.Adj (w3 hΓ σ smul_adj pow_eleven hne : V)
        (w4 hΓ σ smul_adj pow_eleven hne : V)
      exact hw3_w4_adj hΓ σ smul_adj pow_eleven hne
    · -- (4, 0): w_4 ~ w_0
      change Γ.Adj (w4 hΓ σ smul_adj pow_eleven hne : V)
        (w0 hΓ σ smul_adj pow_eleven hne : V)
      exact (hw0_w4_adj hΓ σ smul_adj pow_eleven hne).symm
  cycle_only := by
    intro i j hadj
    -- Reflect to subtype-level H-adjacency.
    have hH : (autFixedInducedGraph Γ σ).Adj
        (cycleSubtype hΓ σ smul_adj pow_eleven hne i)
        (cycleSubtype hΓ σ smul_adj pow_eleven hne j) :=
      H_adj_of_cycleVertex_adj hΓ σ smul_adj pow_eleven hne hadj
    -- Case on (i, j) using fin_cases.
    fin_cases i
    · fin_cases j
      · -- (0, 0): loop, contradicts irrefl.
        exact ((autFixedInducedGraph Γ σ).irrefl hH).elim
      · -- (0, 1): forward cycle edge.
        left; rfl
      · -- (0, 2): non-edge.
        exact absurd hH (hw0_not_adj_w2 hΓ σ smul_adj pow_eleven hne)
      · -- (0, 3): non-edge.
        exact absurd hH (hw0_not_adj_w3 hΓ σ smul_adj pow_eleven hne)
      · -- (0, 4): backward cycle edge.
        right; rfl
    · fin_cases j
      · -- (1, 0): backward.
        right; rfl
      · -- (1, 1): loop.
        exact ((autFixedInducedGraph Γ σ).irrefl hH).elim
      · -- (1, 2): forward.
        left; rfl
      · -- (1, 3): non-edge.
        exact absurd hH (hw1_not_adj_w3 hΓ σ smul_adj pow_eleven hne)
      · -- (1, 4): non-edge.
        exact absurd hH (hw1_not_adj_w4 hΓ σ smul_adj pow_eleven hne)
    · fin_cases j
      · -- (2, 0): non-edge.
        exact absurd hH.symm (hw0_not_adj_w2 hΓ σ smul_adj pow_eleven hne)
      · -- (2, 1): backward.
        right; rfl
      · -- (2, 2): loop.
        exact ((autFixedInducedGraph Γ σ).irrefl hH).elim
      · -- (2, 3): forward.
        left; rfl
      · -- (2, 4): non-edge.
        exact absurd hH (hw2_not_adj_w4 hΓ σ smul_adj pow_eleven hne)
    · fin_cases j
      · -- (3, 0): non-edge.
        exact absurd hH.symm (hw0_not_adj_w3 hΓ σ smul_adj pow_eleven hne)
      · -- (3, 1): non-edge.
        exact absurd hH.symm (hw1_not_adj_w3 hΓ σ smul_adj pow_eleven hne)
      · -- (3, 2): backward.
        right; rfl
      · -- (3, 3): loop.
        exact ((autFixedInducedGraph Γ σ).irrefl hH).elim
      · -- (3, 4): forward.
        left; rfl
    · fin_cases j
      · -- (4, 0): forward (cycle edge: 0 = 4 + 1).
        left; rfl
      · -- (4, 1): non-edge.
        exact absurd hH.symm (hw1_not_adj_w4 hΓ σ smul_adj pow_eleven hne)
      · -- (4, 2): non-edge.
        exact absurd hH.symm (hw2_not_adj_w4 hΓ σ smul_adj pow_eleven hne)
      · -- (4, 3): backward.
        right; rfl
      · -- (4, 4): loop.
        exact ((autFixedInducedGraph Γ σ).irrefl hH).elim

end Construction

end Moore57
