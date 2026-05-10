import Moore57.FixedPointBasics
import Moore57.FixedCommonNeighbors
import Mathlib.Tactic.Linarith.Frontend

namespace Moore57

/-- Non-regular strong graph condition with parameters `λ = 0`, `μ = 1`.
This is the exact paper-level condition used before the fixed graph is
classified as either a Moore graph or a star. -/
structure IsStrongZeroOne {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  of_adj : ∀ v w : V, G.Adj v w → Fintype.card (G.commonNeighbors v w) = 0
  of_not_adj :
    ∀ v w : V, v ≠ w → ¬ G.Adj v w →
      Fintype.card (G.commonNeighbors v w) = 1

/-- There is no regular strongly-regular graph with parameters
`(n, k, λ, μ) = (56, k, 0, 1)`.  This is the arithmetic obstruction behind the
paper's fixed-graph classification once the fixed graph is assumed regular
with `56` vertices. -/
theorem not_isSRGWith_56_k_0_1 {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (k : ℕ) :
    ¬ G.IsSRGWith 56 k 0 1 := by
  intro hG
  have hparam := SimpleGraph.IsSRGWith.param_eq G hG (by norm_num)
  have hcard : Fintype.card V = 56 := hG.card
  have hnonempty : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    norm_num
  rcases hnonempty with ⟨v⟩
  have hk_lt : k < 56 := by
    have hdegree := G.degree_lt_card_verts v
    simpa [hG.regular.degree_eq v, hcard] using hdegree
  have hk_le : k ≤ 55 := by omega
  by_cases hk_zero : k = 0
  · subst k
    norm_num at hparam
  have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk_zero)
  have hk_le56 : k ≤ 56 := by omega
  have hsub_pos : 1 ≤ 56 - k := by omega
  have hparam_int : (k : ℤ) * ((k : ℤ) - 1) = 56 - (k : ℤ) - 1 := by
    have hparam_nat : k * (k - 1) = 56 - k - 1 := by
      simpa using hparam
    have hparam_cast :
        ((k * (k - 1) : ℕ) : ℤ) = ((56 - k - 1 : ℕ) : ℤ) := by
      exact_mod_cast hparam_nat
    rw [Nat.cast_mul, Int.ofNat_sub hk_pos,
      Int.ofNat_sub hsub_pos, Int.ofNat_sub hk_le56] at hparam_cast
    norm_num at hparam_cast ⊢
    exact hparam_cast
  have hsquare : (k : ℤ) * (k : ℤ) = 55 := by
    calc
      (k : ℤ) * (k : ℤ) =
          (k : ℤ) * ((k : ℤ) - 1) + (k : ℤ) := by ring
      _ = 55 := by
        rw [hparam_int]
        ring
  by_cases hk_le7 : k ≤ 7
  · have hk_nonneg_int : 0 ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    have hk_le7_int : (k : ℤ) ≤ 7 := by exact_mod_cast hk_le7
    nlinarith
  · have hk_ge8 : 8 ≤ k := by omega
    have hk_ge8_int : (8 : ℤ) ≤ k := by exact_mod_cast hk_ge8
    nlinarith

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

end D19ActsOnMoore57
end Moore57
