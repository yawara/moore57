import Moore57.FixedInducedSubgraph
import Moore57.FixedNeighborCounts

namespace Moore57

namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The degree of a fixed vertex inside the induced fixed graph is the number of
ambient neighbors fixed by the same group element. -/
theorem fixedInducedGraph_degree_eq_fixedNeighborFinset_card
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    (x : fixedVertexSet (h.smulEquiv g)) :
    (fixedInducedGraph h g).degree x =
      ((Γ.neighborFinset (x : V)).filter fun w => h.smulEquiv g w = w).card := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  have hsubtypeCard :
      Fintype.card ((fixedInducedGraph h g).neighborSet x) =
        Fintype.card
          {w : V // w ∈ (Γ.neighborFinset (x : V)).filter fun w => h.smulEquiv g w = w} := by
    refine Fintype.card_congr ?neighborEquiv
    exact
      { toFun := fun y =>
          ⟨y.1.1, by
            have hyAdj : Γ.Adj (x : V) y.1.1 := by
              have hyAdjSub : (fixedInducedGraph h g).Adj x y.1 :=
                (SimpleGraph.mem_neighborSet (G := fixedInducedGraph h g)
                  (v := x) (w := y.1)).1 y.property
              simpa [fixedInducedGraph] using hyAdjSub
            have hyFixed :
                h.smulEquiv g y.1.1 = y.1.1 := by
              exact y.1.property
            simp [SimpleGraph.mem_neighborFinset, hyAdj, hyFixed]⟩
        invFun := fun y =>
          ⟨⟨(y : V), by
              exact (Finset.mem_filter.mp y.property).2⟩, by
            have hyAdj : Γ.Adj (x : V) (y : V) := by
              exact (SimpleGraph.mem_neighborFinset (G := Γ) (v := (x : V)) (w := (y : V))).1
                (Finset.mem_filter.mp y.property).1
            have hyAdjSub :
                (fixedInducedGraph h g).Adj x
                  ⟨(y : V), (Finset.mem_filter.mp y.property).2⟩ := by
              simpa [fixedInducedGraph] using hyAdj
            exact (SimpleGraph.mem_neighborSet (G := fixedInducedGraph h g)
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
          {w : V // w ∈ (Γ.neighborFinset (x : V)).filter fun w => h.smulEquiv g w = w} =
        ((Γ.neighborFinset (x : V)).filter fun w => h.smulEquiv g w = w).card := by
    exact Fintype.card_ofFinset
      ((Γ.neighborFinset (x : V)).filter fun w => h.smulEquiv g w = w) (by intro w; rfl)
  exact hsubtypeCard.trans hfinsetCard

/-- Rotation-specialized form of `fixedInducedGraph_degree_eq_fixedNeighborFinset_card`. -/
theorem fixedInducedGraph_rotation_degree_eq_fixedNeighborFinset_card
    (h : D19ActsOnMoore57 V Γ) (d : ZMod 19)
    (x : fixedVertexSet (h.rotation d)) :
    (Γ.induce (fixedVertexSet (h.rotation d))).degree x =
      (h.fixedNeighborFinset d (x : V)).card := by
  simpa [fixedInducedGraph, fixedNeighborFinset, rotation] using
    h.fixedInducedGraph_degree_eq_fixedNeighborFinset_card (DihedralGroup.r d) x

end D19ActsOnMoore57

end Moore57
