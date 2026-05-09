import Moore57.FixedPointBasics
import Moore57.FixedCommonNeighbors

namespace Moore57
namespace D19ActsOnMoore57

variable {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The subgraph induced by the vertices fixed by a given group element. -/
abbrev fixedInducedGraph (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    SimpleGraph (fixedVertexSet (h.smulEquiv g)) :=
  Γ.induce (fixedVertexSet (h.smulEquiv g))

@[simp] theorem fixedInducedGraph_adj
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y : fixedVertexSet (h.smulEquiv g)} :
    (fixedInducedGraph h g).Adj x y ↔ Γ.Adj (x : V) (y : V) := by
  rfl

/-- In the fixed-point induced graph, adjacent vertices have no common neighbors. -/
theorem fixedInducedGraph_commonNeighbors_card_of_adj
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y : fixedVertexSet (h.smulEquiv g)}
    (hxy : (fixedInducedGraph h g).Adj x y) :
    Fintype.card ((fixedInducedGraph h g).commonNeighbors x y) = 0 := by
  classical
  refine Fintype.card_eq_zero_iff.mpr ⟨fun z => ?_⟩
  have hz : (z : fixedVertexSet (h.smulEquiv g)) ∈
      (fixedInducedGraph h g).commonNeighbors x y := z.property
  have hz_ambient : (z : V) ∈ Γ.commonNeighbors (x : V) (y : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz ⊢
    exact hz
  have hcard : Fintype.card (Γ.commonNeighbors (x : V) (y : V)) = 0 :=
    h.isMoore.of_adj (x : V) (y : V) hxy
  have hpos : 0 < Fintype.card (Γ.commonNeighbors (x : V) (y : V)) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨(z : V), hz_ambient⟩⟩
  omega

/-- In the fixed-point induced graph, distinct non-adjacent vertices have exactly one
common neighbor. -/
theorem fixedInducedGraph_commonNeighbors_card_of_not_adj
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    {x y : fixedVertexSet (h.smulEquiv g)}
    (hxy_ne : x ≠ y) (hnadj : ¬ (fixedInducedGraph h g).Adj x y) :
    Fintype.card ((fixedInducedGraph h g).commonNeighbors x y) = 1 := by
  classical
  have hxy_ne_ambient : (x : V) ≠ (y : V) := by
    exact fun hval => hxy_ne (Subtype.ext hval)
  have hnadj_ambient : ¬ Γ.Adj (x : V) (y : V) := by
    simpa [fixedInducedGraph] using hnadj
  have hcard : Fintype.card (Γ.commonNeighbors (x : V) (y : V)) = 1 :=
    h.isMoore.of_not_adj hxy_ne_ambient hnadj_ambient
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨z, hz_unique⟩
  have hz_mem : (z : V) ∈ Γ.commonNeighbors (x : V) (y : V) := z.property
  have hz_adj : Γ.Adj (x : V) (z : V) ∧ Γ.Adj (y : V) (z : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hz_mem
    exact hz_mem
  have hx_fixed : h.smul g (x : V) = (x : V) := by
    exact x.property
  have hy_fixed : h.smul g (y : V) = (y : V) := by
    exact y.property
  let zFixed : fixedVertexSet (h.smulEquiv g) :=
    ⟨(z : V), by
      exact
        h.fixed_commonNeighbor_of_not_adj g hx_fixed hy_fixed hxy_ne_ambient hnadj_ambient hz_adj⟩
  have zFixed_mem : zFixed ∈ (fixedInducedGraph h g).commonNeighbors x y := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact hz_adj
  refine Fintype.card_eq_one_iff.mpr ⟨⟨zFixed, zFixed_mem⟩, ?_⟩
  intro w
  apply Subtype.ext
  apply Subtype.ext
  have hw_mem_fixed : (w : fixedVertexSet (h.smulEquiv g)) ∈
      (fixedInducedGraph h g).commonNeighbors x y := w.property
  have hw_mem : (w : V) ∈ Γ.commonNeighbors (x : V) (y : V) := by
    rw [SimpleGraph.mem_commonNeighbors] at hw_mem_fixed ⊢
    exact hw_mem_fixed
  have hw_eq_z : (w : V) = (z : V) :=
    congrArg Subtype.val (hz_unique ⟨(w : V), hw_mem⟩)
  change (w : V) = (z : V)
  exact hw_eq_z

end D19ActsOnMoore57
end Moore57
