import Moore57.Foundations.GroupAction.FixedPoints
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Moore57.Moore57Graph.Aut.CommonNeighbor
import Mathlib.Tactic.Linarith.Frontend

/-!
# Fixed induced subgraph of a Moore57 automorphism (Tier 2)

Abstract version of `D19OnMoore57/Fixed/InducedSubgraph.lean` and
`D19OnMoore57/Fixed/InducedDegree.lean`. For an automorphism `σ : Equiv.Perm V`
of a Moore57 graph, the subgraph induced on `fixedVertexSet σ` inherits the
`(λ, μ) = (0, 1)` SRG structure (when regular), and its degree at a fixed
vertex matches the σ-fixed-neighbour cardinality.

The dependence on dihedral-group packaging is removed: each statement takes
an explicit `σ : Equiv.Perm V` together with `smul_adj : ∀ v w, Γ.Adj v w ↔
Γ.Adj (σ v) (σ w)`.
-/

namespace Moore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Induced subgraph on the vertices fixed by an automorphism. -/
abbrev autFixedInducedGraph (Γ : SimpleGraph V) (σ : Equiv.Perm V) :
    SimpleGraph (fixedVertexSet σ) :=
  Γ.induce (fixedVertexSet σ)

@[simp] theorem autFixedInducedGraph_adj
    (σ : Equiv.Perm V) {x y : fixedVertexSet σ} :
    (autFixedInducedGraph Γ σ).Adj x y ↔ Γ.Adj (x : V) (y : V) := by
  rfl

/-- In the σ-fixed induced graph, adjacent vertices have no common neighbours. -/
theorem autFixedInducedGraph_commonNeighbors_card_of_adj
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    {x y : fixedVertexSet σ}
    (hxy : (autFixedInducedGraph Γ σ).Adj x y) :
    Fintype.card ((autFixedInducedGraph Γ σ).commonNeighbors x y) = 0 := by
  classical
  refine Fintype.card_eq_zero_iff.mpr ⟨fun z => ?_⟩
  have hz : (z : fixedVertexSet σ) ∈
      (autFixedInducedGraph Γ σ).commonNeighbors x y := z.property
  have hz_ambient : (z : V) ∈ Γ.commonNeighbors (x : V) (y : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz ⊢
    exact hz
  have hcard : Fintype.card (Γ.commonNeighbors (x : V) (y : V)) = 0 :=
    hΓ.of_adj (x : V) (y : V) hxy
  have hpos : 0 < Fintype.card (Γ.commonNeighbors (x : V) (y : V)) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨(z : V), hz_ambient⟩⟩
  omega

/-- In the σ-fixed induced graph, distinct non-adjacent vertices have exactly
one common neighbour. -/
theorem autFixedInducedGraph_commonNeighbors_card_of_not_adj
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    {x y : fixedVertexSet σ}
    (hxy_ne : x ≠ y) (hnadj : ¬ (autFixedInducedGraph Γ σ).Adj x y) :
    Fintype.card ((autFixedInducedGraph Γ σ).commonNeighbors x y) = 1 := by
  classical
  have hxy_ne_ambient : (x : V) ≠ (y : V) := by
    exact fun hval => hxy_ne (Subtype.ext hval)
  have hnadj_ambient : ¬ Γ.Adj (x : V) (y : V) := by
    simpa [autFixedInducedGraph] using hnadj
  have hcard : Fintype.card (Γ.commonNeighbors (x : V) (y : V)) = 1 :=
    hΓ.of_not_adj hxy_ne_ambient hnadj_ambient
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨z, hz_unique⟩
  have hz_mem : (z : V) ∈ Γ.commonNeighbors (x : V) (y : V) := z.property
  have hz_adj : Γ.Adj (x : V) (z : V) ∧ Γ.Adj (y : V) (z : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz_mem
    exact hz_mem
  have hx_fixed : σ (x : V) = (x : V) := x.property
  have hy_fixed : σ (y : V) = (y : V) := y.property
  let zFixed : fixedVertexSet σ :=
    ⟨(z : V), by
      exact
        aut_fixed_commonNeighbor_of_not_adj hΓ σ smul_adj
          hx_fixed hy_fixed hxy_ne_ambient hnadj_ambient hz_adj⟩
  have zFixed_mem : zFixed ∈ (autFixedInducedGraph Γ σ).commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hz_adj
  refine Fintype.card_eq_one_iff.mpr ⟨⟨zFixed, zFixed_mem⟩, ?_⟩
  intro w
  apply Subtype.ext
  apply Subtype.ext
  have hw_mem_fixed : (w : fixedVertexSet σ) ∈
      (autFixedInducedGraph Γ σ).commonNeighbors x y := w.property
  have hw_mem : (w : V) ∈ Γ.commonNeighbors (x : V) (y : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hw_mem_fixed ⊢
    exact hw_mem_fixed
  have hw_eq_z : (w : V) = (z : V) :=
    congrArg Subtype.val (hz_unique ⟨(w : V), hw_mem⟩)
  change (w : V) = (z : V)
  exact hw_eq_z

/-- The σ-fixed induced subgraph inherits the strong `(0, 1)` common-neighbor
condition. -/
theorem autFixedInducedGraph_isStrongZeroOne
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w)) :
    IsStrongZeroOne (autFixedInducedGraph Γ σ) where
  of_adj := by
    intro x y hxy
    exact autFixedInducedGraph_commonNeighbors_card_of_adj hΓ σ hxy
  of_not_adj := by
    intro x y hxy_ne hxy_not
    exact autFixedInducedGraph_commonNeighbors_card_of_not_adj hΓ σ smul_adj hxy_ne hxy_not

/-- If the σ-fixed induced graph has constant degree `k`, then it is strongly
regular with parameters `(fixedVertexCount, k, 0, 1)`. -/
theorem autFixedInducedGraph_isSRGWith_of_regular
    (hΓ : IsMoore57 Γ) (σ : Equiv.Perm V)
    (smul_adj : ∀ v w : V, Γ.Adj v w ↔ Γ.Adj (σ v) (σ w))
    (k : ℕ)
    (hreg : ∀ x : fixedVertexSet σ, (autFixedInducedGraph Γ σ).degree x = k) :
    (autFixedInducedGraph Γ σ).IsSRGWith (fixedVertexCount σ) k 0 1 where
  card := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
  regular := by
    intro x
    exact hreg x
  of_adj := by
    intro x y hxy
    exact autFixedInducedGraph_commonNeighbors_card_of_adj hΓ σ (x := x) (y := y) hxy
  of_not_adj := by
    intro x y hxy_ne hxy_not
    exact autFixedInducedGraph_commonNeighbors_card_of_not_adj hΓ σ smul_adj
      (x := x) (y := y) hxy_ne hxy_not

/-- The degree of a fixed vertex inside the σ-fixed induced graph equals the
σ-fixed-neighbour count in the ambient graph. -/
theorem autFixedInducedGraph_degree_eq_fixedNeighborFinset_card
    (σ : Equiv.Perm V) (x : fixedVertexSet σ) :
    (autFixedInducedGraph Γ σ).degree x =
      ((Γ.neighborFinset (x : V)).filter fun w => σ w = w).card := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  have hsubtypeCard :
      Fintype.card ((autFixedInducedGraph Γ σ).neighborSet x) =
        Fintype.card
          {w : V // w ∈ (Γ.neighborFinset (x : V)).filter fun w => σ w = w} := by
    refine Fintype.card_congr ?neighborEquiv
    exact
      { toFun := fun y =>
          ⟨y.1.1, by
            have hyAdj : Γ.Adj (x : V) y.1.1 := by
              have hyAdjSub : (autFixedInducedGraph Γ σ).Adj x y.1 :=
                (SimpleGraph.mem_neighborSet (G := autFixedInducedGraph Γ σ)
                  (v := x) (w := y.1)).1 y.property
              simpa [autFixedInducedGraph] using hyAdjSub
            have hyFixed : σ y.1.1 = y.1.1 := y.1.property
            simp [SimpleGraph.mem_neighborFinset, hyAdj, hyFixed]⟩
        invFun := fun y =>
          ⟨⟨(y : V), by exact (Finset.mem_filter.mp y.property).2⟩, by
            have hyAdj : Γ.Adj (x : V) (y : V) := by
              exact (SimpleGraph.mem_neighborFinset (G := Γ) (v := (x : V)) (w := (y : V))).1
                (Finset.mem_filter.mp y.property).1
            have hyAdjSub :
                (autFixedInducedGraph Γ σ).Adj x
                  ⟨(y : V), (Finset.mem_filter.mp y.property).2⟩ := by
              simpa [autFixedInducedGraph] using hyAdj
            exact (SimpleGraph.mem_neighborSet (G := autFixedInducedGraph Γ σ)
              (v := x) (w := ⟨(y : V), (Finset.mem_filter.mp y.property).2⟩)).2 hyAdjSub⟩
        left_inv := by
          intro y
          ext
          rfl
        right_inv := by
          intro y
          ext
          rfl }
  have hfinsetCard :
      Fintype.card
          {w : V // w ∈ (Γ.neighborFinset (x : V)).filter fun w => σ w = w} =
        ((Γ.neighborFinset (x : V)).filter fun w => σ w = w).card := by
    exact Fintype.card_ofFinset
      ((Γ.neighborFinset (x : V)).filter fun w => σ w = w) (by intro w; rfl)
  exact hsubtypeCard.trans hfinsetCard

end Moore57
