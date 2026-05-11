import Moore57.Foundations.GroupAction.FixedPointBasics
import Moore57.FixedCommonNeighbors
import Moore57.Foundations.GraphTheory.StrongZeroOne
import Mathlib.Tactic.Linarith.Frontend

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

/-- Paper Lemma 1(2) in its non-regular form: the subgraph induced by fixed
vertices inherits the strong `(λ, μ) = (0, 1)` common-neighbor condition. -/
theorem fixedInducedGraph_isStrongZeroOne
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) :
    IsStrongZeroOne (fixedInducedGraph h g) where
  of_adj := by
    intro x y hxy
    exact h.fixedInducedGraph_commonNeighbors_card_of_adj g hxy
  of_not_adj := by
    intro x y hxy_ne hxy_not
    exact h.fixedInducedGraph_commonNeighbors_card_of_not_adj g hxy_ne hxy_not

/-- Paper Lemma 1(2), packaged in mathlib's strongly-regular form: if the
fixed induced graph has constant fixed degree `k`, then it is strongly regular
with parameters `(fixedVertexCount, k, 0, 1)`.  The common-neighbor parameters
come directly from the ambient Moore graph and fixedness of unique common
neighbors. -/
theorem fixedInducedGraph_isSRGWith_of_regular
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19) (k : ℕ)
    (hreg : ∀ x : fixedVertexSet (h.smulEquiv g),
      (fixedInducedGraph h g).degree x = k) :
    (fixedInducedGraph h g).IsSRGWith
      (fixedVertexCount (h.smulEquiv g)) k 0 1 where
  card := by
    rw [fixedVertexCount_eq_card_fixedVertexSet]
  regular := by
    intro x
    exact hreg x
  of_adj := by
    intro x y hxy
    exact h.fixedInducedGraph_commonNeighbors_card_of_adj g (x := x) (y := y) hxy
  of_not_adj := by
    intro x y hxy_ne hxy_not
    exact h.fixedInducedGraph_commonNeighbors_card_of_not_adj g
      (x := x) (y := y) hxy_ne hxy_not

/-- If a fixed induced graph has `56` vertices, it cannot be regular with
common-neighbor parameters `(λ, μ) = (0, 1)`.  This isolates the arithmetic
part of excluding the regular Moore-graph branch in the paper classification
step. -/
theorem fixedInducedGraph_not_regular_of_fixedVertexCount_eq_56
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    (hfix : fixedVertexCount (h.smulEquiv g) = 56) :
    ¬ ∃ k : ℕ, ∀ x : fixedVertexSet (h.smulEquiv g),
      (fixedInducedGraph h g).degree x = k := by
  rintro ⟨k, hreg⟩
  have hsrg := h.fixedInducedGraph_isSRGWith_of_regular g k hreg
  have hsrg56 :
      (fixedInducedGraph h g).IsSRGWith 56 k 0 1 := by
    simpa [hfix] using hsrg
  exact not_isSRGWith_56_k_0_1 k hsrg56

/-- If a fixed induced graph has between `52` and `56` vertices, it cannot be
regular with common-neighbor parameters `(λ, μ) = (0, 1)`. -/
theorem fixedInducedGraph_not_regular_of_fixedVertexCount_between_52_56
    (h : D19ActsOnMoore57 V Γ) (g : DihedralGroup 19)
    (hfixed_lower : 52 ≤ fixedVertexCount (h.smulEquiv g))
    (hfixed_upper : fixedVertexCount (h.smulEquiv g) ≤ 56) :
    ¬ ∃ k : ℕ, ∀ x : fixedVertexSet (h.smulEquiv g),
      (fixedInducedGraph h g).degree x = k := by
  rintro ⟨k, hreg⟩
  exact
    not_isSRGWith_n_k_0_1_of_card_between_52_56
      (fixedVertexCount (h.smulEquiv g)) k hfixed_lower hfixed_upper
      (h.fixedInducedGraph_isSRGWith_of_regular g k hreg)

end D19ActsOnMoore57
end Moore57
